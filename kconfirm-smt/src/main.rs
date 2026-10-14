use std::path::PathBuf;

use clap::Parser;
use kconfirm_smt::{MacroOptions, ModelSource, RunMode, run_model};
use z3::SatResult;

/// SMT feature model for the Linux kernel's Kconfig.
#[derive(Parser)]
#[command(version, about)]
struct Args {
    /// Path to the Linux kernel source tree
    #[arg(long, required_unless_present = "load_model")]
    linux: Option<PathBuf>,

    /// Where to write a generated random witness .config.
    #[arg(long, value_name = "FILE")]
    output_config: Option<PathBuf>,

    /// Save reusable model constraints.
    /// Defaults to constraints.smt2 when generating a model.
    #[arg(long, value_name = "FILE")]
    output_smt_lib: Option<PathBuf>,

    /// Check that a .config is consistent with the model (0 on SAT, 1 on UNSAT).
    /// A partial configuration can be passed, and kconfirm-smt will randomize the rest.
    #[arg(long, value_name = "CONFIG",
          conflicts_with_all = ["output_config", "seed"])]
    add_config_constraints: Option<PathBuf>,

    /// Load a saved model from a previous run with --output-smt-lib.
    #[arg(long, value_name = "FILE", requires = "add_config_constraints",
          conflicts_with_all = ["output_smt_lib", "output_config", "seed", "load_preproc", "dump_preproc"])]
    load_model: Option<PathBuf>,

    /// Randomize the Z3 solver with this seed.
    #[arg(long)]
    seed: Option<u32>,

    /// Z3 solver timeout, in milliseconds (0 disables the timeout).
    #[arg(long, default_value_t = 0)]
    solver_timeout_ms: u32,

    /// Use macro/function values from FILE for pre-processing, instead of evaluating:
    /// scripts/Kconfig.include from the target linux source and $(...) probes
    /// with the host toolchain.
    ///
    /// It is expected that the user previously output these with kconfirm-smt using --dump.
    ///
    /// Use this for cross-compiling offline:
    /// e.g. first --dump-preproc the values for ARM, then --load-preproc while on x86.
    #[arg(long, value_name = "FILE")]
    load_preproc: Option<PathBuf>,

    /// After pre-processing the tree, write every evaluated macro/function value
    /// to FILE, for a later --load
    #[arg(long, value_name = "FILE")]
    dump_preproc: Option<PathBuf>,
}

fn main() {
    env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("info")).init();

    let args = Args::parse();
    let mode = match args.add_config_constraints {
        Some(config_input) => RunMode::CheckConfig {
            config_input,
            constraints_output: args.output_smt_lib,
        },
        None => RunMode::Model {
            config_output: args.output_config,
            constraints_output: args
                .output_smt_lib
                .unwrap_or_else(|| "constraints.smt2".into()),
            seed: args.seed,
        },
    };
    let source = match args.load_model {
        Some(path) => ModelSource::SmtLib(path),
        None => {
            let arch = kconfirm_linux::infer_arch();
            log::info!("using arch {arch} (from $ARCH or `uname -m` if not set)");
            ModelSource::Linux {
                path: args.linux.expect("required without --load-model"),
                macros: MacroOptions {
                    load: args.load_preproc,
                    dump: args.dump_preproc,
                    arch,
                },
            }
        }
    };
    let status = match run_model(source, mode, args.solver_timeout_ms) {
        Ok(None | Some(SatResult::Sat)) => 0,
        Ok(Some(SatResult::Unsat)) => 1,
        Ok(Some(SatResult::Unknown)) => 2,
        Err(error) => {
            log::error!("{error}");
            2
        }
    };
    std::process::exit(status);
}
