// SPDX-License-Identifier: GPL-2.0-only
//! `--confirm` mode checks and their findings.

use std::path::Path;

use kconfirm_lib::{AnalysisArgs, Check, Finding, Severity};
use kconfirm_smt::{BuildError, MacroOptions, SmtModel};
use log::info;
use nom_kconfig::KconfigFile;
use z3::SatResult;

mod checks;
mod dead_subrange;
mod unmet;

fn failure(check: Check, message: impl Into<String>) -> Finding {
    Finding {
        severity: Severity::Fatal,
        check,
        symbol: None,
        message: message.into(),
        arch: None,
    }
}

/// Build all constraints before selecting any checks.
pub fn build_model(
    file: KconfigFile,
    macros: Option<MacroOptions>,
) -> Result<SmtModel, Vec<Finding>> {
    kconfirm_smt::build_model(file, macros).map_err(|error| {
        let (check, message) = match error {
            BuildError::Parse(message) => (Check::FailedParse, message),
            BuildError::Preprocess(message) => (Check::FailedModel, message),
        };
        vec![failure(check, message)]
    })
}

/// Run enabled `--confirm` mode checks.
/// The caller labels and aggregates by architecture after each target completes.
pub fn check_model(
    model: &SmtModel,
    args: &AnalysisArgs,
    witness_directory: Option<&Path>,
) -> Vec<Finding> {
    let mut findings = checks::structural_checks(model.source(), args);
    if !checks::needs_solver(args) {
        return findings;
    }
    info!("Checking the model before running SMT --confirm checks");
    match model.solver().check() {
        SatResult::Unsat => {
            findings.push(failure(
                Check::FailedModel,
                "The Kconfig model is unsatisfiable; --confirm checks could not be run",
            ));
            return findings;
        }
        SatResult::Unknown => {
            findings.push(failure(
                Check::FailedModel,
                format!(
                    "The solver could not check the model: {:?}",
                    model.solver().get_reason_unknown()
                ),
            ));
            return findings;
        }
        SatResult::Sat => {}
    }
    findings.extend(checks::check(model, args));
    if args.is_enabled(Check::DeadSubrange) {
        findings.extend(dead_subrange::check(model));
    }
    if args.is_enabled(Check::UnmetDependency) {
        findings.extend(unmet::check(model, witness_directory));
    }
    findings
}

#[cfg(test)]
mod tests;
