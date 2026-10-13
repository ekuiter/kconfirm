use super::*;
use crate::confirm::check_model;
use kconfirm_smt::encode_source;
use nom_kconfig::{KconfigFile, KconfigInput, entry::Source, parse_kconfig};

mod out_of_range_default;

const INPUTS: &str = "config A\n bool \"a\"\nconfig B\n bool \"b\"\nconfig C\n bool \"c\"\n";
const MODULES: &str = "config MODULES\n bool\n default y\n modules\n";

fn model(text: &str) -> SmtModel {
    let file = KconfigFile::new(".".into(), "Kconfig".into());
    let ast = parse_kconfig(KconfigInput::new_extra(text, file))
        .unwrap()
        .1;
    encode_source(Source {
        kconfigs: vec![ast],
    })
}

fn check(text: &str, checks: &[Check]) -> Vec<Finding> {
    let mut args = AnalysisArgs::new();
    for &check in checks {
        args.enable_check(check);
    }
    let findings = check_model(&model(text), &args, None);
    assert!(
        !findings
            .iter()
            .any(|finding| finding.check == Check::FailedModel),
        "{findings:?}"
    );
    findings
}

fn expect(text: &str, checks: &[Check], expected: &[(Check, &str)]) -> Vec<Finding> {
    let findings = check(text, checks);
    let actual: Vec<_> = findings
        .iter()
        .map(|finding| (finding.check, finding.symbol.as_deref().unwrap()))
        .collect();
    assert_eq!(actual, expected, "{findings:?}");
    findings
}

#[test]
fn dead_defaults_use_implication_and_the_union_of_earlier_conditions() {
    expect(
        "config A\n bool \"a\"\nconfig B\n bool \"b\"\n depends on A\nconfig X\n int\n default 1 if A\n default 2 if B\n",
        &[Check::DeadDefault],
        &[(Check::DeadDefault, "X")],
    );
    expect(
        &format!("{INPUTS}config X\n int\n default 1 if A\n default 2 if !A\n default 3 if B\n"),
        &[Check::DeadDefault],
        &[(Check::DeadDefault, "X")],
    );
}

#[test]
fn overlapping_conditions_do_not_make_a_default_dead_or_duplicate() {
    expect(
        &format!("{INPUTS}config X\n int\n default 1 if A\n default 2 if B\n"),
        &[Check::DeadDefault, Check::DuplicateDefault],
        &[],
    );
}

#[test]
fn trailing_default_n_and_def_bool_are_retained_for_checks() {
    expect(
        "config X\n def_bool y\n default n\n",
        &[Check::DeadDefault],
        &[(Check::DeadDefault, "X")],
    );
    expect(
        "config X\n def_bool y\n default y\n",
        &[Check::DuplicateDefault],
        &[(Check::DuplicateDefault, "X")],
    );
    expect(
        "config X\n bool\n default n\n default n\n",
        &[Check::DuplicateDefault],
        &[(Check::DuplicateDefault, "X")],
    );
}

#[test]
fn duplicate_defaults_prove_both_condition_and_value_equivalence() {
    expect(
        &format!("{INPUTS}config X\n bool\n default y if A || B\n default !n if B || A\n"),
        &[Check::DuplicateDefault],
        &[(Check::DuplicateDefault, "X")],
    );
    // Repeating a value from one default and a condition from another is not
    // a duplicate of either property.
    expect(
        &format!("{INPUTS}config X\n int\n default 1 if A\n default 2 if B\n default 2 if A\n"),
        &[Check::DuplicateDefault],
        &[],
    );
}

#[test]
fn checks_span_partial_definitions_and_keep_each_definition_scope() {
    expect(
        "config A\n bool \"a\"\nconfig B\n bool \"b\"\n depends on A\nif A\nconfig X\n int\n default 1\nendif\nmenu \"nested\"\n depends on B\nconfig X\n int\n default 2\nendmenu\n",
        &[Check::DeadDefault],
        &[(Check::DeadDefault, "X")],
    );
    expect(
        "config A\n bool \"a\"\nconfig B\n bool\n default A\nif A\nconfig X\n int\n default 1\nendif\nmenu \"nested\"\n depends on B\nconfig X\n int\n default 1\nendmenu\n",
        &[Check::DuplicateDefault],
        &[(Check::DuplicateDefault, "X")],
    );
    expect(
        &format!(
            "{INPUTS}if A\nconfig X\n int\n default 1\nendif\nif !A\nconfig X\n int\n default 1\nendif\n"
        ),
        &[Check::DuplicateDefault],
        &[],
    );
}

#[test]
fn conditional_depends_on_is_expanded_before_confirmation() {
    expect(
        &format!("{INPUTS}config X\n bool\n depends on A if B\n default y if A || !B\n"),
        &[Check::ConstantCondition],
        &[(Check::ConstantCondition, "X")],
    );
}

#[test]
fn range_priority_is_ordered_and_independent_of_bounds() {
    expect(
        &format!("{INPUTS}config X\n int \"x\"\n range 0 10 if A\n range 20 30 if A && B\n"),
        &[Check::DeadRange, Check::DuplicateRange],
        &[(Check::DeadRange, "X")],
    );
    // A later unconditional range does not shadow an earlier conditional one.
    expect(
        &format!("{INPUTS}config X\n int \"x\"\n range 0 10 if A\n range 0 10\n"),
        &[Check::DeadRange, Check::DuplicateRange],
        &[],
    );
}

#[test]
fn duplicate_ranges_use_symbolic_bounds_and_equivalent_conditions() {
    expect(
        &format!(
            "{INPUTS}config LOW\n int\n default 0\nconfig HIGH\n int\n default 10\nconfig X\n int \"x\"\n range LOW HIGH if A || B\n range 0 10 if B || A\n"
        ),
        &[Check::DeadRange, Check::DuplicateRange],
        &[(Check::DuplicateRange, "X")],
    );
}

#[test]
fn valid_numeric_ranges_still_restrict_user_values() {
    let model = model("config X\n int \"x\"\n default 20\n range 3 5\n");
    let Some(Z3Types::Integer(value)) = &model.symbols()["X"].z3_type else {
        panic!()
    };
    assert_eq!(
        model.solver().check_assumptions(&[value.eq(4)]),
        SatResult::Sat
    );
    assert_eq!(
        model.solver().check_assumptions(&[value.eq(20)]),
        SatResult::Unsat
    );
    assert_eq!(
        model.solver().check_assumptions(&[value.eq(2)]),
        SatResult::Unsat
    );
}

#[test]
fn conditions_use_transitive_dependencies_for_every_attribute_kind() {
    let findings = expect(
        "config A\n bool \"a\"\nconfig B\n bool \"b\"\n depends on A\nconfig TARGET\n bool\nconfig X\n int\n depends on B\n default 1 if A || B\n range 0 10 if !A\nconfig Y\n bool \"y\"\n depends on B\n select TARGET if A || B\n imply TARGET if !A\n",
        &[Check::ConstantCondition],
        &[
            (Check::ConstantCondition, "X"),
            (Check::ConstantCondition, "X"),
            (Check::ConstantCondition, "Y"),
            (Check::ConstantCondition, "Y"),
        ],
    );
    assert!(findings[0].message.contains("always y"));
    assert!(findings[1].message.contains("always n"));
    expect(
        &format!("{INPUTS}config X\n bool\n depends on A && !A\n default y if A\n"),
        &[Check::ConstantCondition],
        &[],
    );
}

#[test]
fn tristate_conditions_preserve_m_and_modules_rewriting() {
    expect(
        &format!(
            "{MODULES}config A\n tristate \"a\"\nconfig X\n tristate\n depends on A\n default y if !A\n"
        ),
        &[Check::ConstantCondition],
        &[],
    );
    let findings = expect(
        &format!(
            "{MODULES}config A\n tristate \"a\"\nconfig X\n tristate\n depends on A = m\n default y if A\n"
        ),
        &[Check::ConstantCondition],
        &[(Check::ConstantCondition, "X")],
    );
    assert!(findings[0].message.contains("always m"));
    let findings = expect(
        "config X\n bool\n default y if m\n",
        &[Check::ConstantCondition],
        &[(Check::ConstantCondition, "X")],
    );
    assert!(findings[0].message.contains("always n"));
}

#[test]
fn dependencies_are_compared_without_assuming_the_option_is_enabled() {
    expect(
        "config A\n bool \"a\"\nconfig B\n bool \"b\"\n depends on A\nconfig C\n bool \"c\"\nconfig X\n bool \"x\"\n depends on B\n depends on A || C\n",
        &[Check::DuplicateDependency],
        &[(Check::DuplicateDependency, "X")],
    );
    expect(
        &format!("{INPUTS}config X\n bool \"x\"\n depends on A\n depends on B\n"),
        &[Check::DuplicateDependency],
        &[],
    );
    expect(
        &format!(
            "{MODULES}config A\n tristate \"a\"\nconfig X\n tristate\n depends on A\n depends on !A\n"
        ),
        &[Check::DuplicateDependency],
        &[],
    );
}

#[test]
fn selects_and_implies_combine_by_max_in_either_source_order() {
    for (attribute, dead, duplicate) in [
        ("select", Check::DeadSelect, Check::DuplicateSelect),
        ("imply", Check::DeadImply, Check::DuplicateImply),
    ] {
        for (first, second) in [("A", "A || B"), ("A || B", "A")] {
            expect(
                &format!(
                    "{INPUTS}config TARGET\n bool\nconfig X\n bool \"x\"\n {attribute} TARGET if {first}\n {attribute} TARGET if {second}\n"
                ),
                &[dead, duplicate],
                &[(dead, "X")],
            );
        }
        expect(
            &format!(
                "{INPUTS}config TARGET\n bool\nconfig X\n bool \"x\"\n {attribute} TARGET if A || B\n {attribute} TARGET if B || A\n"
            ),
            &[dead, duplicate],
            &[(duplicate, "X")],
        );
        expect(
            &format!(
                "{INPUTS}config TARGET\n bool\nconfig X\n bool \"x\"\n {attribute} TARGET if A\n {attribute} TARGET if B\n"
            ),
            &[dead, duplicate],
            &[],
        );
    }
}

#[test]
fn edge_redundancy_keeps_one_representative_and_respects_bool_promotion() {
    expect(
        &format!(
            "{INPUTS}config TARGET\n bool\nconfig X\n bool \"x\"\n select TARGET if A\n select TARGET if B\n select TARGET if A || B\n"
        ),
        &[Check::DeadSelect, Check::DuplicateSelect],
        &[(Check::DeadSelect, "X"), (Check::DeadSelect, "X")],
    );
    for (ty, expected) in [
        ("tristate", Check::DeadSelect),
        ("bool", Check::DuplicateSelect),
    ] {
        expect(
            &format!(
                "{MODULES}config M\n tristate\n default m\nconfig TARGET\n {ty}\nconfig X\n bool \"x\"\n select TARGET if M\n select TARGET\n"
            ),
            &[Check::DeadSelect, Check::DuplicateSelect],
            &[(expected, "X")],
        );
    }
}

#[test]
fn select_visible_requires_jointly_reachable_edge_and_prompt() {
    expect(
        &format!(
            "{INPUTS}config TARGET\n bool \"target\" if A || B\nconfig X\n bool \"x\"\n select TARGET if A && B\n"
        ),
        &[Check::SelectVisible],
        &[(Check::SelectVisible, "X")],
    );
    expect(
        &format!(
            "{INPUTS}config TARGET\n bool \"target\" if A\nconfig X\n bool \"x\"\n select TARGET if !A\n"
        ),
        &[Check::SelectVisible],
        &[],
    );
    expect(
        "config TARGET\n bool\nconfig X\n bool \"x\"\n select TARGET\n",
        &[Check::SelectVisible],
        &[],
    );
}

#[test]
fn impossible_edges_and_implies_to_unavailable_targets_are_dead() {
    expect(
        "config TARGET\n bool\nconfig X\n bool\n select TARGET\n imply TARGET\n",
        &[Check::DeadSelect, Check::DeadImply],
        &[(Check::DeadSelect, "X"), (Check::DeadImply, "X")],
    );
    expect(
        "config TARGET\n bool\n depends on n\nconfig X\n bool \"x\"\n imply TARGET\n select TARGET\n",
        &[Check::DeadSelect, Check::DeadImply],
        &[(Check::DeadImply, "X")],
    );
}

#[test]
fn style_checks_remain_opt_in_and_use_original_attribute_order() {
    expect(
        "config TARGET\n bool\nconfig X\n bool \"x\"\n select TARGET\n default y\n select TARGET\n",
        &[Check::UngroupedAttribute],
        &[(Check::UngroupedAttribute, "X")],
    );
    expect(
        &format!(
            "{INPUTS}config VALUE\n int\n default 5\nconfig X\n int\n default VALUE if A\n default 5 if B\n"
        ),
        &[Check::DuplicateDefaultValue],
        &[(Check::DuplicateDefaultValue, "X")],
    );
}

#[test]
fn disabled_checks_are_independent_and_queries_do_not_leak_between_runs() {
    let model = model("config X\n bool\n default y\n default y\n default n\n");
    for (check, count) in [
        (Check::DeadDefault, 1),
        (Check::DuplicateDefault, 1),
        (Check::DuplicateDefaultValue, 0),
        (Check::UnmetDependency, 0),
        (Check::DuplicateDefault, 1),
        (Check::DeadDefault, 1),
    ] {
        let mut args = AnalysisArgs::new();
        args.enable_check(check);
        let findings = check_model(&model, &args, None);
        assert_eq!(findings.len(), count, "{findings:?}");
        assert!(findings.iter().all(|finding| finding.check == check));
    }
}

#[test]
fn inconsistent_models_never_prove_all_attributes_dead_or_duplicate() {
    let model = model("config X\n bool\n default y\n default n\n");
    model.solver().assert(Bool::from_bool(false));
    for check in [
        Check::DeadDefault,
        Check::DuplicateDefault,
        Check::OutOfRangeDefault,
    ] {
        let mut args = AnalysisArgs::new();
        args.enable_check(check);
        let findings = check_model(&model, &args, None);
        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].check, Check::FailedModel);
        assert_eq!(findings[0].severity, Severity::Fatal);
    }
}

#[test]
fn inconclusive_queries_report_failure_instead_of_unreachability() {
    let model = model(INPUTS);
    assert_eq!(model.solver().check(), SatResult::Sat);
    let mut params = z3::Params::new();
    // A resource limit, rather than a wall-clock timeout, makes this test
    // independent of how fast the host machine happens to be.
    params.set_u32("rlimit", 1);
    model.solver().set_params(&params);
    let mut args = AnalysisArgs::new();
    args.enable_check(Check::DuplicateDefault);
    let mut checker = Checker {
        model: &model,
        analysis: &Analysis::default(),
        args: &args,
        findings: Vec::new(),
        answers: HashMap::new(),
    };
    assert!(
        checker
            .possible("X", Check::DuplicateDefault, Bool::fresh_const("query"))
            .is_err()
    );
    assert_eq!(checker.findings.len(), 1);
    assert_eq!(checker.findings[0].check, Check::FailedModel);
    assert!(
        checker.findings[0]
            .message
            .contains("duplicate_default check inconclusive for X")
    );
    assert!(checker.answers.is_empty());
}

#[test]
fn default_equivalence_handles_strings_and_numeric_comparisons() {
    expect(
        "config N\n int \"n\"\n range 0 10\nconfig TEXT\n string\n default \"same\"\nconfig X\n string\n default TEXT if N > 3\n default \"same\" if N >= 4\n",
        &[Check::DuplicateDefault],
        &[(Check::DuplicateDefault, "X")],
    );
    expect(
        "config N\n int \"n\"\n range 0 10\nconfig X\n string\n default \"first\" if N > 3\n default \"second\" if N >= 4\n",
        &[Check::DuplicateDefault],
        &[],
    );
}

#[test]
fn unreachable_attributes_do_not_prove_vacuous_value_equivalence() {
    expect(
        "config X\n int\n default 1 if n\n default 2 if n\n range 0 10 if n\n range 20 30 if n\n",
        &[
            Check::DeadDefault,
            Check::DuplicateDefault,
            Check::DuplicateDefaultValue,
            Check::DeadRange,
            Check::DuplicateRange,
        ],
        &[
            (Check::DeadDefault, "X"),
            (Check::DeadDefault, "X"),
            (Check::DeadRange, "X"),
            (Check::DeadRange, "X"),
        ],
    );
}

#[test]
fn choice_members_ignore_ordinary_defaults_and_reverse_dependencies() {
    expect(
        "choice\n prompt \"pick one\"\nconfig A\n bool \"a\"\n default y\n default y\nconfig B\n bool \"b\"\nendchoice\nconfig X\n bool \"x\"\n select A\n imply B\n",
        &[
            Check::DeadDefault,
            Check::DuplicateDefault,
            Check::DeadSelect,
            Check::DeadImply,
        ],
        &[
            (Check::DeadDefault, "A"),
            (Check::DeadDefault, "A"),
            (Check::DeadSelect, "X"),
            (Check::DeadImply, "X"),
        ],
    );
}
