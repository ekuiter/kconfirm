// SPDX-License-Identifier: GPL-2.0-only
//! Find select edges that can exceed the target's dependencies.

use std::{collections::HashSet, path::Path};

use kconfirm_lib::{Check, Finding, Severity};
use kconfirm_smt::{SmtModel, Z3Types, definition_dependencies, model_condition};
use log::info;
use nom_kconfig::attribute::r#type::Type;
use z3::{SatResult, ast::Bool};
use z3_ternary::{Ternary, and, clamp, lt};

use super::failure;

struct UnmetDepCheck {
    selector: String,
    selectee: String,
    violation: Bool,
}

fn queries(model: &SmtModel) -> Vec<UnmetDepCheck> {
    let symbols = model.symbols();
    let mut queries = Vec::new();
    for (selectee, info) in symbols {
        if model.is_choice_member(selectee)
            || !matches!(info.z3_type, Some(Z3Types::Ternary(_)))
            || info
                .definition
                .as_ref()
                .and_then(|definition| definition.kconfig_dependencies.as_ref())
                .is_none()
        {
            continue;
        }

        // For a bool target, dependencies at m count as fully satisfied.
        let dependencies = definition_dependencies(symbols, info);
        let warning_dependencies = match info.kconfig_type {
            Some(Type::Bool(_) | Type::DefBool(_)) => clamp(&dependencies, &Bool::from_bool(true)),
            _ => dependencies,
        };
        for (selector, conditions) in &info.selected_by {
            let selector_info = &symbols[selector];
            let Some(Z3Types::Ternary(selector_value)) = &selector_info.z3_type else {
                continue;
            };
            let selector_dependencies = definition_dependencies(symbols, selector_info);
            for condition in conditions {
                let condition = condition
                    .as_ref()
                    .map_or_else(Ternary::y, |expr| model_condition(symbols, expr.clone()));
                let pull = and(&[
                    selector_value.clone(),
                    selector_dependencies.clone(),
                    condition,
                ]);
                let violation = lt(&warning_dependencies, &pull);
                if violation.as_bool() != Some(false) {
                    queries.push(UnmetDepCheck {
                        selector: selector.clone(),
                        selectee: selectee.clone(),
                        violation,
                    });
                }
            }
        }
    }
    queries
}

pub(super) fn check(model: &SmtModel, witness_directory: Option<&Path>) -> Vec<Finding> {
    let checks = queries(model);
    info!(
        "Checking {} select edges for unmet dependencies",
        checks.len()
    );
    let mut findings = Vec::new();
    if let Some(directory) = witness_directory {
        if let Err(e) = std::fs::create_dir_all(directory) {
            findings.push(failure(
                Check::FailedModel,
                format!(
                    "Cannot create witness directory {}: {e}",
                    directory.display()
                ),
            ));
            return findings;
        }
    }
    let mut witness_names = HashSet::new();
    for check in checks {
        match model
            .solver()
            .check_assumptions(std::slice::from_ref(&check.violation))
        {
            SatResult::Sat => {
                findings.push(Finding {
                    severity: Severity::Error,
                    check: Check::UnmetDependency,
                    symbol: Some(check.selector.clone()),
                    message: format!("can select {} past its dependencies", check.selectee),
                    arch: None,
                });
                if let Some(directory) = witness_directory {
                    let base = format!("unmet_dep-{}-selects-{}", check.selector, check.selectee);
                    let mut name = format!("{base}.config");
                    let mut counter = 2;
                    while !witness_names.insert(name.clone()) {
                        name = format!("{base}-{counter}.config");
                        counter += 1;
                    }
                    let path = directory.join(name);
                    let assignment = model.solver().get_model().expect("sat produces a model");
                    if let Err(e) = std::fs::write(&path, model.render_config(&assignment)) {
                        findings.push(failure(
                            Check::FailedModel,
                            format!("Cannot write witness {}: {e}", path.display()),
                        ));
                    } else {
                        info!("Wrote unmet-dependency witness {}", path.display());
                    }
                }
            }
            SatResult::Unsat => {}
            SatResult::Unknown => findings.push(failure(
                Check::FailedModel,
                format!(
                    "Unmet-dependency check inconclusive for {} -> {}: {:?}",
                    check.selector,
                    check.selectee,
                    model.solver().get_reason_unknown()
                ),
            )),
        }
    }
    findings
}
