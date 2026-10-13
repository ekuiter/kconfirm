// SPDX-License-Identifier: GPL-2.0-only
use nom_kconfig::KconfigFile;
use std::{
    io,
    path::{Path, PathBuf},
};

/// The host architecture implemented by UML in the Linux tree.
///
/// The kernel's `scripts/subarch.include` normalizes both x86_64 and i386
/// hosts to `x86`. UML uses that value to expose its `64BIT` prompt, so the
/// same Kconfig tree represents both its 32-bit and 64-bit configurations.
pub const UML_SUBARCH: &str = "x86";

// each architecture has its own directory, and config option.
// most are the same, but powerpc / ppc and um / uml are not.
// this maps the directory to the config option
pub fn arch_dir_to_config(arch_dir: &str) -> String {
    match arch_dir {
        "powerpc" => String::from("PPC"),
        "um" => String::from("UML"),
        _ => String::from(arch_dir).to_uppercase(),
    }
}

/// The kernel arch name for a `uname -m` machine string
pub fn subarch(machine: &str) -> String {
    let machine = machine.trim();
    if machine.len() == 4 && machine.starts_with('i') && machine.ends_with("86") {
        return String::from("x86");
    }
    if machine == "x86_64" {
        return String::from("x86");
    }
    if machine == "sun4u" {
        return String::from("sparc64");
    }
    if machine != "arm64" && machine.starts_with("arm") {
        return String::from("arm");
    }
    if machine == "sa110" {
        return String::from("arm");
    }
    if machine == "s390x" {
        return String::from("s390");
    }
    if machine.starts_with("ppc") {
        return String::from("powerpc");
    }
    if machine.starts_with("mips") {
        return String::from("mips");
    }
    if machine.starts_with("sh2") || machine.starts_with("sh3") || machine.starts_with("sh4") {
        return String::from("sh");
    }
    if machine.starts_with("aarch64") {
        return String::from("arm64");
    }
    if machine.starts_with("riscv") {
        return String::from("riscv");
    }
    if machine.starts_with("loongarch") {
        return String::from("loongarch");
    }
    String::from(machine)
}

/// Uses the `ARCH` environment variable when set
/// otherwise `uname -m`.
pub fn infer_arch() -> String {
    if let Ok(arch) = std::env::var("ARCH")
        && !arch.is_empty()
    {
        return arch;
    }
    let machine = std::process::Command::new("uname")
        .arg("-m")
        .output()
        .ok()
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .filter(|stdout| !stdout.trim().is_empty())
        .unwrap_or_else(|| String::from(std::env::consts::ARCH));
    subarch(&machine)
}

/// Architectures actually supported by this source tree, in deterministic order.
pub fn architectures(linux_source: &Path) -> io::Result<Vec<String>> {
    let mut arches = Vec::new();
    for entry in std::fs::read_dir(linux_source.join("arch"))? {
        let entry = entry?;
        if entry.file_type()?.is_dir() && entry.path().join("Kconfig").is_file() {
            arches.push(entry.file_name().to_string_lossy().into_owned());
        }
    }
    arches.sort();
    if arches.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "no architecture Kconfig files found under arch/",
        ));
    }
    Ok(arches)
}

/// A complete top-level Kconfig input, with source expansion set for one target.
pub fn kconfig_for_arch(linux_source: &Path, arch: &str) -> KconfigFile {
    let mut file = KconfigFile::new(linux_source.to_path_buf(), PathBuf::from("Kconfig"));
    file.add_local_var("SRCARCH", arch);
    file.add_local_var("ARCH", arch);
    if arch == "um" {
        file.add_local_var("HEADER_ARCH", UML_SUBARCH);
        file.add_local_var("SUBARCH", UML_SUBARCH);
    }
    file
}

pub struct LinuxKconfig {
    pub arch_config_option: Option<String>,
    pub kconfig_file: KconfigFile,
    pub file_contents: String,
}

/// Read a complete tree for every architecture. Callers must analyze each
/// target independently and aggregate its findings afterwards.
pub fn collect_kconfig_root_files(linux_source: PathBuf) -> io::Result<Vec<LinuxKconfig>> {
    architectures(&linux_source)?
        .into_iter()
        .map(|arch| {
            let file = kconfig_for_arch(&linux_source, &arch);
            Ok(LinuxKconfig {
                arch_config_option: Some(arch),
                file_contents: file.read_to_string()?,
                kconfig_file: file,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::subarch;

    /// The machine strings scripts/subarch.include rewrites, and a few it
    /// leaves alone.
    #[test]
    fn subarch_matches_the_kernels_sed_script() {
        for (machine, arch) in [
            ("i386", "x86"),
            ("i686", "x86"),
            ("x86_64", "x86"),
            ("sun4u", "sparc64"),
            ("armv7l", "arm"),
            ("arm64", "arm64"),
            ("sa110", "arm"),
            ("s390x", "s390"),
            ("ppc64le", "powerpc"),
            ("mips64", "mips"),
            ("sh4a", "sh"),
            ("aarch64", "arm64"),
            ("aarch64_be", "arm64"),
            ("riscv64", "riscv"),
            ("loongarch64", "loongarch"),
            // untouched by the script
            ("m68k", "m68k"),
            ("sparc64", "sparc64"),
        ] {
            assert_eq!(subarch(machine), arch, "uname -m {machine}");
        }
    }
}
