<div align="center">
  <img src="assets/kconfirm.png" alt="Project Logo" width="200">
</div>
<p align="center"><sub><em>Logo given to me by my friend, <a href="https://www.silasvibes.com/">Silas</a></em></sub></p>

# kconfirm
A static analysis tool for the Kconfig language.

Detect dead code, unmet dependencies, and more.

# Usage

Build with Rust, OpenSSL, pkg-config, and Z3 installed, or enter the provided
development environment with `nix develop`:
```
# install missing dependencies (or use nix develop)
sudo apt update
sudo apt install -y pkg-config libssl-dev libz3-dev z3 flex bison

# clone this repo
git clone https://github.com/julianbraha/kconfirm.git

cd kconfirm

# compile
cargo build --release -p kconfirm-cli

# run in lint mode (for linux):
./target/release/kconfirm-cli --lint --linux-dir-path RELATIVE_PATH_TO_LINUX_SOURCE

# run in lint mode (for coreboot):
./target/release/kconfirm-cli --lint --coreboot-dir-path RELATIVE_PATH_TO_COREBOOT_SOURCE
```

Choose exactly one mode:
1. `--lint` runs fast heuristic checks,
2. `--confirm` uses SMT solving for advanced checks like unmet dependencies. 

Both modes produce their findings in the same structured format.

By default, running on Linux analyzes every architecture with an `arch/<name>/Kconfig` in the source tree, sequentially. Findings are deduplicated across architectures. Use `--arch` to select particular targets:
```sh
# all architectures:
./target/release/kconfirm-cli --confirm --linux-dir-path /path/to/linux

# only x86 and arm64:
./target/release/kconfirm-cli --confirm --linux-dir-path /path/to/linux --arch x86,arm64
```

`--enable-check` and `--disable-check` accept repeated or comma-separated check IDs:

```sh
# disable the unmet dependency check:
./target/release/kconfirm-cli --confirm --linux-dir-path /path/to/linux --disable-check unmet_dependency
```

Internal checks that the SMT model is satisfiable produce random solutions to the model (witness files) and saving them is optional. Linux witnesses go under `witnesses/<arch>/`.

Note that `--confirm` mode evaluates Linux's Kconfig preprocessing using the current active toolchain in your environment. 

The `kconfirm-smt` package is available for standalone usage for exporting the model constraints, and loading or dumping preprocessing values.

To enable the check for dead links in the Kconfig `help` texts:
```
# NOTE: this is very slow! It will attempt to visit every link that it finds!
./target/release/kconfirm-cli --lint --linux-dir-path RELATIVE_PATH_TO_LINUX_SOURCE --enable-check dead_link
```

To run differential tests between the SMT model and the Kconfig interpreter:
```sh
cd kconfirm-smt

# compile
cargo build --release

# generate random seeds, and save them for reproducibility
bash generate_random_seeds.sh 10000 > random-seeds.txt

# run differential tests in both directions
bash differential_test_model_config.sh 10000 random-seeds.txt 300000 < /dev/null
bash differential_test_randconfig.sh 10000 random-seeds.txt 300000 < /dev/null
```

## Submitted Patches: Linux

### Dead Defaults

[2026-03-23 "drm: fix dead default for DRM_TTM_KUNIT_TEST"](https://lore.kernel.org/all/20260323124118.1414913-1-julianbraha@gmail.com/)

[2026-03-23 "s390: fix dead defaults for S390_MODULES_SANITY_TEST and S390_UNWIND_SELFTEST"](https://lkml.org/lkml/2026/3/23/1056)

[2026-03-22 "soc: aspeed: cleanup dead default for ASPEED_SOCINFO"](https://lkml.org/lkml/2026/3/22/591)

### Select-Visible

[2026-05-31 "x86/cpu: cleanup duplicate dependencies in Kconfig"](https://lore.kernel.org/all/20260531065743.1408481-1-julianbraha@gmail.com/)

[2026-05-23 "drm/i915: use 'depends on' with visible DEBUG_OBJECTS for DRM_I915_DEBUG and DRM_I915_SW_FENCE_DEBUG_OBJECTS"](https://lore.kernel.org/all/20260523154121.147103-1-julianbraha@gmail.com/)

[2026-05-03 "riscv: replace select with dependency for visible RELOCATABLE"](https://lore.kernel.org/all/20260503040331.71875-1-julianbraha@gmail.com/)

### Duplicate Dependencies

[2026-05-31 "x86/cpu: cleanup duplicate dependencies in Kconfig"](https://lore.kernel.org/all/20260531065743.1408481-1-julianbraha@gmail.com/)

[2026-04-18 "cpufreq: clean up dead dependencies on X86 in Kconfig"](https://lore.kernel.org/all/20260417230652.305414-1-julianbraha@gmail.com/)

[2026-04-02 "stmmac: cleanup dead dependencies on STMMAC_PLATFORM and STMMAC_ETH in Kconfig"](https://lore.kernel.org/all/20260402145858.240231-1-julianbraha@gmail.com/)

[2026-03-31	"cpufreq: clean up dead code in Kconfig"](https://git.kernel.org/pub/scm/linux/kernel/git/next/linux-next.git/commit/?id=2e00c2dcc5325af04e2dfbb29281ced1c724ab81)

[2026-03-31 "soc: apple: cleanup dead code in kconfig"](https://lore.kernel.org/all/20260331072808.37198-1-julianbraha@gmail.com/)

[2026-03-31 "mm/thp: dead code cleanup in Kconfig"](https://lore.kernel.org/all/20260331070730.33915-1-julianbraha@gmail.com/)

[2026-03-31 "media: dvb: cleanup dead DVB_USB code in Kconfig"](https://lore.kernel.org/all/20260331153230.15871-1-julianbraha@gmail.com/)

[2026-03-31 "keys: cleanup dead code in Kconfig for FIPS_SIGNATURE_SELFTEST"](https://lore.kernel.org/all/20260331122214.103145-1-julianbraha@gmail.com/)

[2026-03-31 "nvmem: cleanup dead code in Kconfig"](https://lore.kernel.org/all/20260331120459.99382-1-julianbraha@gmail.com/)

[2026-03-30 "remoteproc: dead code cleanup in Kconfig for STM32_RPROC"](https://lore.kernel.org/all/20260330224545.29769-1-julianbraha@gmail.com/)

[2026-03-30 "pci: dead code cleanup in Kconfig"](https://lore.kernel.org/all/20260330214549.16157-1-julianbraha@gmail.com/)

[2026-03-30 "ppp: dead code cleanup in Kconfig"](https://lore.kernel.org/all/20260330213258.13982-1-julianbraha@gmail.com/)

[2026-03-29 "riscv: dead code cleanup in kconfig for RISCV_PROBE_VECTOR_UNALIGNED_ACCESS"](https://lore.kernel.org/all/20260329203249.563434-1-julianbraha@gmail.com/)

[2026-03-29 "net: microchip: dead code cleanup in kconfig for FDMA"](https://lore.kernel.org/all/20260329185348.526893-1-julianbraha@gmail.com/)

### Duplicate Selects

[2026-03-29 "ARM: omap2: dead code cleanup in kconfig for ARCH_OMAP4"](https://lore.kernel.org/all/20260329183018.519560-1-julianbraha@gmail.com/)

[2026-03-29 "media: dead code cleanup in kconfig for VIDEO_SOLO6X10"](https://lore.kernel.org/all/20260329183942.522693-1-julianbraha@gmail.com/)

## Submitted Patches: U-Boot

### Dead Defaults

[2026-04-15 "powerpc: fix dead default for SYS_L3_SIZE"](https://lore.kernel.org/all/20260414231833.200277-1-julianbraha@gmail.com/)

## Submitted Patches: coreboot

### Dead Defaults

[2026-04-12 "mainboard/opencellular/elgon/Kconfig: fix dead default for FMDFILE"](https://review.coreboot.org/c/coreboot/+/92141)

[2026-04-12 "payloads/Kconfig: fix dead default for PAYLOAD_FIT_SUPPORT"](https://review.coreboot.org/c/coreboot/+/92140)

## Submitted Patches: BusyBox

[2026-05-26 "config: remove duplicate dependency on SELINUX for CHCON"](https://lists.busybox.net/pipermail/busybox/2026-May/092311.html)

## Submitted Pull Requests: Fiasco

https://github.com/kernkonzept/fiasco/pull/22

## Special Thanks
- [Yann Prono "Mcdostone"](https://mcdostone.github.io/) for building the [nom-kconfig](https://github.com/Mcdostone/nom-kconfig) crate for parsing `kconfig`, and continuing to support it.
- [Necip Fazil Yildiran](https://github.com/necipfazil), [Jeho Oh](https://github.com/jeho-oh), and [Paul Gazzillo](https://paulgazzillo.com/) for introducing me to the unmet dependency bug, and for their mentorship.
