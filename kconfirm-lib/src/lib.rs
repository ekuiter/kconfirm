// SPDX-License-Identifier: GPL-2.0-only
#![doc = include_str!("../README.md")]
mod analyze;
mod checks;
mod dead_links;
mod output;
mod symbol_table;

use nom_kconfig::{
    Entry,
    KconfigInput,
    parse_kconfig, //
};

pub use analyze::analyze;
pub use checks::{
    AnalysisArgs,
    Check,
    parse_check, //
};
use checks::{
    check_select_visible,
    check_variable_info, //
};
pub use output::{
    Finding,
    Severity,
    print_findings, //
};
pub use symbol_table::*;

/// Runs the specified checks on raw Kconfig files.
/// In the case of Linux, architectures can be specified in the
/// `kconfig_files` argument.
///
/// # Examples
///
/// ## Analyze a Kconfig tree
/// ```no_run
/// use kconfirm_lib::{check_kconfig, print_findings, AnalysisArgs, Check};
/// use nom_kconfig::{KconfigFile, KconfigInput};
///
/// # fn main() -> std::io::Result<()> {
/// let mut checks = AnalysisArgs::new();
/// checks.enable_check(Check::SelectVisible);
///
/// // Load the root Kconfig of the project under analysis.
/// let kconfig_file = KconfigFile::new("linux".into(), "Kconfig".into());
/// let contents = kconfig_file.read_to_string()?;
/// let input = KconfigInput::new_extra(&contents, kconfig_file);
///
/// // Pair each complete target input with an optional architecture label.
/// // Linux callers read the top-level Kconfig with SRCARCH set for each target;
/// // use None for a project with a single target.
/// let findings = check_kconfig(checks, vec![(None, input)]);
/// print_findings(findings);
/// # Ok(())
/// # }
/// ```
pub fn check_kconfig(
    args: AnalysisArgs,
    kconfig_files: Vec<(Option<String>, KconfigInput)>,
) -> Vec<Finding> {
    // Inputs for one target share a table; different architectures never do.
    let mut targets = std::collections::BTreeMap::new();
    for (arch, input) in kconfig_files {
        targets.entry(arch).or_insert_with(Vec::new).push(input);
    }
    let mut findings = Vec::new();
    for (arch, inputs) in targets {
        let mut target_findings = Vec::new();
        let mut symbol_table = SymbolTable::new();
        for input in inputs {
            match parse_kconfig(input) {
                Ok(parsed) => {
                    let entries: Vec<Entry> = parsed.1.entries;
                    target_findings.extend(analyze(&args, &mut symbol_table, entries));
                }
                Err(e) => target_findings.push(Finding {
                    severity: Severity::Fatal,
                    check: Check::FailedParse,
                    symbol: None,
                    message: format!("Failed to parse kconfig, error is: {e}"),
                    arch: None,
                }),
            }
        }
        for (symbol, info) in &symbol_table.raw {
            for (_, definition) in &info.attribute_defs {
                target_findings.extend(check_variable_info(&args, symbol, &None, definition));
            }
            if args.is_enabled(Check::SelectVisible) {
                target_findings.extend(check_select_visible(symbol, info));
            }
        }
        for finding in &mut target_findings {
            finding.arch = arch.clone();
        }
        findings.extend(target_findings);
    }
    findings
}
