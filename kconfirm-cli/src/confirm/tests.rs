use super::*;
use kconfirm_smt::encode_source;
use nom_kconfig::{KconfigInput, entry::Source, parse_kconfig};
use z3::ast::Bool;

fn fixture_model(text: &str) -> SmtModel {
    let file = KconfigFile::new(".".into(), "Kconfig".into());
    let ast = parse_kconfig(KconfigInput::new_extra(text, file))
        .unwrap()
        .1;
    encode_source(Source {
        kconfigs: vec![ast],
    })
}

fn confirm_checks() -> AnalysisArgs {
    let mut args = AnalysisArgs::new();
    args.enable_check(Check::UnmetDependency);
    args
}

#[test]
fn unmet_dependencies_return_structured_findings_and_respect_select_conditions() {
    let source = "config DEP\n bool \"dep\"\nconfig TARGET\n bool\n depends on DEP\nconfig SELECTOR\n bool \"selector\"\n select TARGET\n";
    let model = fixture_model(source);
    let constraints = model.solver().get_assertions();
    let findings = check_model(&model, &confirm_checks(), None);
    assert_eq!(findings.len(), 1);
    let finding = &findings[0];
    assert_eq!(finding.check, Check::UnmetDependency);
    assert_eq!(finding.severity, Severity::Error);
    assert_eq!(finding.symbol.as_deref(), Some("SELECTOR"));
    assert_eq!(finding.arch, None);
    assert_eq!(finding.message, "can select TARGET past its dependencies");
    assert_eq!(model.solver().get_assertions(), constraints);
    assert!(check_model(&model, &AnalysisArgs::new(), None).is_empty());
    assert_eq!(check_model(&model, &confirm_checks(), None).len(), 1);
    assert_eq!(model.solver().get_assertions(), constraints);

    let safe = fixture_model(&source.replace("select TARGET", "select TARGET if DEP"));
    assert!(check_model(&safe, &confirm_checks(), None).is_empty());
}

#[test]
fn unmet_selects_respect_the_selectors_own_dependencies() {
    let model = fixture_model(
        "config DEP\n bool \"dep\"\nconfig TARGET\n bool\n depends on DEP\nconfig SELECTOR\n bool\n depends on DEP\n select TARGET\nconfig FORCE\n bool \"force\"\n select SELECTOR\n",
    );
    let findings = check_model(&model, &confirm_checks(), None);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].symbol.as_deref(), Some("FORCE"));
    assert_eq!(
        findings[0].message,
        "can select SELECTOR past its dependencies"
    );
}

#[test]
fn unmet_check_preserves_bool_promotion_and_tristate_dependency_levels() {
    let source = "config MODULES\n bool\n default y\n modules\nconfig DEP\n tristate\n default m\nconfig TARGET\n bool\n depends on DEP\nconfig SELECTOR\n bool\n default y\n select TARGET\n";
    assert!(check_model(&fixture_model(source), &confirm_checks(), None).is_empty());
    let tristate = source.replace("config TARGET\n bool", "config TARGET\n tristate");
    let findings = check_model(&fixture_model(&tristate), &confirm_checks(), None);
    assert_eq!(findings.len(), 1);
    assert_eq!(findings[0].check, Check::UnmetDependency);
}

#[test]
fn unsatisfiable_model_is_a_fatal_finding_and_disabled_checks_do_not_solve() {
    let model = fixture_model("config A\n bool\n");
    model.solver().assert(Bool::from_bool(false));
    assert!(check_model(&model, &AnalysisArgs::new(), None).is_empty());
    let findings = check_model(&model, &confirm_checks(), None);
    assert_eq!(findings.len(), 1);
    assert_eq!(findings[0].check, Check::FailedModel);
    assert_eq!(findings[0].severity, Severity::Fatal);
}
