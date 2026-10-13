use std::collections::BTreeSet;
use std::fs;
use std::process::Command;

fn findings_for_arch(output: &str, arch: &str) -> BTreeSet<String> {
    output
        .lines()
        .filter_map(|line| {
            let (head, rest) = line.split_once("] [")?;
            let (arches, message) = rest.split_once(']')?;
            arches
                .split(',')
                .any(|item| item.trim() == arch)
                .then(|| format!("{head}]{message}"))
        })
        .collect()
}

#[test]
// system test
fn test_linux_kconfig_analysis_v6_19() {
    let tmp_dir = std::env::temp_dir().join("kconfirm_linux_test");
    let tar_path = tmp_dir.join("linux-6.19.tar.xz");
    let extract_dir = tmp_dir.join("linux-6.19");

    fs::create_dir_all(&tmp_dir).unwrap();

    // download if missing
    if !tar_path.exists() {
        let status = Command::new("curl")
            .args(["-L", "-o"])
            .arg(&tar_path)
            .arg("https://cdn.kernel.org/pub/linux/kernel/v6.x/linux-6.19.tar.xz")
            .status()
            .expect("failed to run curl");

        assert!(status.success(), "download failed");
    }

    // extract if missing
    if !extract_dir.exists() {
        let status = Command::new("tar")
            .arg("-xf")
            .arg(&tar_path)
            .arg("-C")
            .arg(&tmp_dir)
            .status()
            .expect("failed to extract");

        assert!(status.success(), "extract failed");
    }

    // run analysis via cli
    let output = Command::new("cargo")
        .args([
            "run",
            "-p",
            "kconfirm-cli",
            "--quiet",
            "--",
            "--lint",
            "--linux-dir-path",
        ])
        .arg(&extract_dir)
        // explicitly enable style, keep dead_link disabled
        .args([
            "--enable-check",
            "duplicate_default_value,ungrouped_attribute",
            "--disable-check",
            "dead_link",
        ])
        .output()
        .expect("failed to run cargo");

    assert!(
        output.status.success(),
        "analysis failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("[failed_parse]"), "{stdout}");
    let all_x86 = findings_for_arch(&stdout, "x86");
    assert!(!all_x86.is_empty(), "expected Linux lint findings");

    // Per-target analysis changes grouping and the old global line count. The
    // x86 results must be identical whether analyzed alone or in the full loop.
    let isolated = Command::new("cargo")
        .args([
            "run",
            "-p",
            "kconfirm-cli",
            "--quiet",
            "--",
            "--lint",
            "--linux-dir-path",
        ])
        .arg(&extract_dir)
        .args([
            "--arch",
            "x86",
            "--enable-check",
            "duplicate_default_value,ungrouped_attribute",
            "--disable-check",
            "dead_link",
        ])
        .output()
        .expect("failed to run cargo");
    assert!(
        isolated.status.success(),
        "{}",
        String::from_utf8_lossy(&isolated.stderr)
    );
    let isolated = String::from_utf8_lossy(&isolated.stdout);
    assert!(!isolated.contains("[failed_parse]"), "{isolated}");
    assert_eq!(all_x86, findings_for_arch(&isolated, "x86"));
}
