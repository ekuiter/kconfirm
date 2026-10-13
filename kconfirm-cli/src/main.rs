// SPDX-License-Identifier: GPL-2.0-only
use clap::{ArgGroup, CommandFactory, Parser};
use confirm::build_model;
use kconfirm_lib::{AnalysisArgs, Check, Finding, check_kconfig, parse_check, print_findings};
use kconfirm_smt::MacroOptions;
use log::info;
use nom_kconfig::{KconfigFile, KconfigInput};
use std::{
    fs, io,
    path::{Path, PathBuf},
};

mod confirm;

#[derive(Parser, Debug)]
#[command(
    author, version, about = "A static analysis tool for Kconfig",
    group(ArgGroup::new("mode").args(["lint", "confirm"]).required(true)),
    group(ArgGroup::new("source")
        .args(["linux_dir_path", "coreboot_dir_path", "other_kconfig_path"])
        .required(true))
)]
struct Args {
    /// Lint mode: quick heuristic checks (the original kconfirm)
    #[arg(long)]
    lint: bool,

    /// Confirm mode: advanced checks using SMT solving
    #[arg(long)]
    confirm: bool,

    /// Linux source tree (all architectures by default)
    #[arg(long)]
    linux_dir_path: Option<PathBuf>,

    /// Coreboot source tree
    #[arg(long)]
    coreboot_dir_path: Option<PathBuf>,

    /// Another project's entry file, such as Kconfig or Config.in
    #[arg(long)]
    other_kconfig_path: Option<PathBuf>,

    /// Linux architecture directory names; repeat or separate with commas
    #[arg(long, requires = "linux_dir_path", value_delimiter = ',', num_args = 1..)]
    arch: Vec<String>,

    /// Enable checks in the chosen mode (e.g. dead_default for --confirm)
    #[arg(long, value_delimiter = ',', num_args = 1.., value_parser = check_name)]
    enable_check: Vec<Check>,

    /// Disable checks in the chosen mode; applied after --enable-check
    #[arg(long, value_delimiter = ',', num_args = 1.., value_parser = check_name)]
    disable_check: Vec<Check>,

    /// Optionally write SMT witnesses, in a subdirectory per architecture
    #[arg(long, requires = "confirm", value_name = "DIR")]
    output_witness_dir: Option<PathBuf>,
}

fn check_name(name: &str) -> Result<Check, String> {
    parse_check(name).ok_or_else(|| format!("unknown check: {name}"))
}

impl Args {
    fn checks(&self) -> AnalysisArgs {
        let mut checks = AnalysisArgs::new();
        checks.enable_check(Check::SelectVisible);
        if self.confirm {
            checks.enable_check(Check::UnmetDependency);
        } else {
            for check in [
                Check::ReverseRange,
                Check::ConstantCondition,
                Check::DuplicateDependency,
                Check::DuplicateRange,
                Check::DuplicateSelect,
                Check::DuplicateDefault,
                Check::DuplicateImply,
                Check::DeadDefault,
                Check::DeadSelect,
                Check::DeadRange,
                Check::DeadImply,
            ] {
                checks.enable_check(check);
            }
        }
        for &check in &self.enable_check {
            checks.enable_check(check);
        }
        for &check in &self.disable_check {
            checks.disable_check(check);
        }
        checks
    }
}

fn analyze_target(
    args: &Args,
    checks: &AnalysisArgs,
    file: KconfigFile,
    arch: Option<&str>,
) -> io::Result<Vec<Finding>> {
    let mut findings = if args.confirm {
        let macros = arch.map(|arch| MacroOptions {
            load: None,
            dump: None,
            arch: arch.to_owned(),
        });
        // Each architecture / loop iteration has a separate symbol table.
        info!("Building SMT model for {}", arch.unwrap_or("Kconfig"));
        match build_model(file, macros) {
            Ok(model) => {
                let witnesses = args.output_witness_dir.as_ref().map(|directory| {
                    arch.map_or_else(|| directory.clone(), |arch| directory.join(arch))
                });
                confirm::check_model(&model, checks, witnesses.as_deref())
            }
            Err(findings) => findings,
        }
    } else {
        let contents = file.read_to_string()?;
        let input = KconfigInput::new_extra(&contents, file);
        check_kconfig(checks.clone(), vec![(None, input)])
    };
    for finding in &mut findings {
        finding.arch = arch.map(str::to_owned);
    }
    Ok(findings)
}

fn main() -> io::Result<()> {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();
    let args = Args::parse();
    let checks = args.checks();
    if args.confirm && checks.is_enabled(Check::ReverseRange) {
        Args::command()
            .error(
                clap::error::ErrorKind::ArgumentConflict,
                "reverse_range is only available in --lint mode",
            )
            .exit();
    }
    for check in [Check::DeadSubrange, Check::OutOfRangeDefault] {
        if args.lint && checks.is_enabled(check) {
            Args::command()
                .error(
                    clap::error::ErrorKind::ArgumentConflict,
                    format!("{} is only available in --confirm mode", check.as_str()),
                )
                .exit();
        }
    }
    let mut findings = Vec::new();
    if let Some(root) = &args.linux_dir_path {
        let available = kconfirm_linux::architectures(root)?;
        let mut arches = if args.arch.is_empty() {
            available.clone()
        } else {
            args.arch.clone()
        };
        arches.sort();
        arches.dedup();
        for arch in &arches {
            if !available.contains(arch) {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    format!(
                        "architecture {arch:?} has no arch/{arch}/Kconfig in {}",
                        root.display()
                    ),
                ));
            }
        }
        for arch in arches {
            let file = kconfirm_linux::kconfig_for_arch(root, &arch);
            findings.extend(analyze_target(&args, &checks, file, Some(&arch))?);
        }
    } else if let Some(root) = &args.coreboot_dir_path {
        let file = KconfigFile::new(root.clone(), PathBuf::from("src/Kconfig"));

        let site_local_dir = root.join("site-local");
        let site_local_kconfig = site_local_dir.join("Kconfig");

        let mut created_dir = false;
        let mut temp_kconfig = None;
        if !site_local_kconfig.exists() {
            info!(
                "coreboot/site-local/Kconfig was missing. Attempting to create it temporarily..."
            );
            if !site_local_dir.exists() {
                fs::create_dir(&site_local_dir)?;
                info!("coreboot/site-local/ was created temporarily.");
                created_dir = true;
            }

            temp_kconfig = Some(fs::File::create_new(&site_local_kconfig)?);
            info!("coreboot/site-local/Kconfig was created temporarily.");
        }

        // TODO: ensure that if analyze_target errors, then we still remove the dir and file that was created
        findings.extend(analyze_target(&args, &checks, file, None)?);

        if temp_kconfig.is_some() {
            fs::remove_file(site_local_kconfig)?;
            info!("Cleaned up coreboot/site-local/Kconfig.");
        }

        if created_dir {
            fs::remove_dir(site_local_dir)?;
            info!("Cleaned up coreboot/site-local/.");
        }
    } else if let Some(path) = &args.other_kconfig_path {
        if !path.is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "--other-kconfig-path requires a Kconfig entry file",
            ));
        }
        let root = path.parent().unwrap_or_else(|| Path::new("."));
        let relative = path.strip_prefix(root).unwrap_or(path);
        let file = KconfigFile::new(root.to_path_buf(), relative.to_path_buf());
        findings.extend(analyze_target(&args, &checks, file, None)?);
    }
    // Sorts and aggregates by architecture.
    print_findings(findings);
    Ok(())
}
