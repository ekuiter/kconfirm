#!/usr/bin/env bash
# Differential test 1: is the model under-constrained?
#
# Every solution generated to the model and rendered as
# a configuration file is checked against the real Linux
# Kconfig interpreter. All outputs are preserved:
#
# - preserves every generated witness
# - preserves every exported SMT model
# - preserves the base model and macro dump, plus each iteration's macro dump
# - preserves every seed
# - preserves all model and kconfig logs
# - preserves all recomputed configs
# - preserves metadata and run summary
#
# usage (from kconfirm-smt/):
#   bash generate_random_seeds.sh 2000 > random-seeds.txt
#   bash differential_test_model_config.sh [RUNS] [SEEDS_FILE]
#
# Uses the first RUNS seeds in file order, including duplicates.
# Defaults: RUNS=1000, SEEDS_FILE=random-seeds.txt (or $SEEDS_FILE).
# Set MACRO_CACHE to an existing macro dump to reuse it; otherwise macros are
# evaluated afresh once per invocation. The values used are always archived.

set -u

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)" || exit 2

LINUX="${LINUX:-evaluation/linux-model}"
BINARY="${BINARY:-$SCRIPT_DIR/../target/release/kconfirm-smt}"
ARCH="${ARCH:-x86_64}"

RUNS="${1:-1000}"
SEEDS_FILE="${2:-${SEEDS_FILE:-random-seeds.txt}}"

# Load once so both directions can reuse exactly the same recorded seed list.
if [ "$#" -gt 2 ]; then
    echo "usage: $0 [RUNS] [SEEDS_FILE]" >&2
    exit 2
fi
if [ ! -f "$SEEDS_FILE" ] || [ ! -r "$SEEDS_FILE" ]; then
    echo "error: seed file not readable: $SEEDS_FILE (generate it with generate_random_seeds.sh)" >&2
    exit 2
fi
if ! mapfile -t seeds < "$SEEDS_FILE"; then
    echo "error: failed to read seed file: $SEEDS_FILE" >&2
    exit 2
fi
seed_count="${#seeds[@]}"
if [ "$seed_count" -eq 0 ]; then
    echo "error: seed file is empty: $SEEDS_FILE" >&2
    exit 2
fi
if [[ ! "$RUNS" =~ ^[1-9][0-9]*$ ]] ||
   (( ${#RUNS} > ${#seed_count} )) || (( RUNS > seed_count )); then
    echo "error: RUNS must be between 1 and $seed_count (seeds available in $SEEDS_FILE)" >&2
    exit 2
fi
for index in "${!seeds[@]}"; do
    seed="${seeds[index]}"
    if [[ ! "$seed" =~ ^(0|[1-9][0-9]{0,9})$ ]] || (( seed > 4294967295 )); then
        echo "error: $SEEDS_FILE:$((index + 1)): expected a decimal seed in 0..4294967295" >&2
        exit 2
    fi
done

LINUX_REPO="git://git.kernel.org/pub/scm/linux/kernel/git/stable/linux.git"
LINUX_BRANCH="v7.2.10"

MACRO_CACHE="${MACRO_CACHE:-}"

RESULTS_DIR="reverse-differential-results"
ITERATIONS_DIR="$RESULTS_DIR/iterations"
FAILURES_DIR="$RESULTS_DIR/failures"
MODEL_FILE="$RESULTS_DIR/model.smt2"
PREPROC_FILE="$RESULTS_DIR/macros.txt"

macro_args=()
if [ -n "$MACRO_CACHE" ]; then
    if [ ! -f "$MACRO_CACHE" ] || [ ! -r "$MACRO_CACHE" ] || [ ! -s "$MACRO_CACHE" ]; then
        echo "error: MACRO_CACHE must name an existing, readable, nonempty macro dump: $MACRO_CACHE" >&2
        exit 2
    fi
    macro_args=(--load-preproc "$MACRO_CACHE")
fi

# Clone Linux v7.2.10 if missing
if [ ! -d "$LINUX/.git" ]; then
    echo "Linux source tree not found at $LINUX"
    echo "Cloning Linux $LINUX_BRANCH..."

    mkdir -p "$(dirname "$LINUX")"

    git clone \
        --depth 1 \
        --branch "$LINUX_BRANCH" \
        "$LINUX_REPO" \
        "$LINUX"

    if [ $? -ne 0 ]; then
        echo "error: failed to clone Linux $LINUX_BRANCH" >&2
        exit 2
    fi
fi


mkdir -p "$ITERATIONS_DIR"
mkdir -p "$FAILURES_DIR"

printf '%s\n' "${seeds[@]:0:RUNS}" > "$RESULTS_DIR/seeds.txt" || exit 2

if [ ! -x "$BINARY" ]; then
    echo "error: kconfirm-smt binary not found at $BINARY (build it, or set BINARY=)" >&2
    exit 2
fi


# Save evaluation metadata
{
    echo "reverse differential testing evaluation"
    echo "date: $(date -Iseconds)"
    echo
    echo "linux: $LINUX"
    echo "binary: $BINARY"
    echo "arch: $ARCH"
    echo "runs: $RUNS"
    echo "seed source: $SEEDS_FILE"
    echo "selected seeds: $RESULTS_DIR/seeds.txt"
    echo "model constraints: $MODEL_FILE"
    echo "preprocessed macros: $PREPROC_FILE"
    echo "macro input: ${MACRO_CACHE:-fresh evaluation}"
    echo
    echo "kernel commit:"
    git -C "$LINUX" rev-parse HEAD 2>/dev/null || echo "unknown"
    echo
    echo "compiler:"
    cc --version 2>/dev/null || true
    echo
    echo "environment:"
    env | sort
} > "$RESULTS_DIR/metadata.txt"

# Archive the base model and the exact macro values used by this invocation.
# An explicitly supplied cache is read and dumped into the results directory.
if ! ARCH="$ARCH" "$BINARY" \
    --linux "$LINUX" \
    --output-smt-lib "$MODEL_FILE" \
    --dump-preproc "$PREPROC_FILE" \
    "${macro_args[@]}" \
    > "$RESULTS_DIR/model.log" 2>&1 || [ ! -s "$MODEL_FILE" ] || [ ! -s "$PREPROC_FILE" ]; then
    echo "error: model generation failed; see $RESULTS_DIR/model.log" >&2
    exit 2
fi
if grep -Eq 'Preprocessed macros: [0-9]+ evaluated, [1-9][0-9]* unresolved' "$RESULTS_DIR/model.log"; then
    echo "error: model has unresolved macros; see $RESULTS_DIR/model.log" >&2
    exit 2
fi


pass=0
fail=0
model_fail=0

for i in $(seq 1 "$RUNS"); do

    seed="${seeds[i - 1]}"

    iteration_name=$(printf "%06d-seed%s" "$i" "$seed")
    iteration_dir="$ITERATIONS_DIR/$iteration_name"

    mkdir -p "$iteration_dir"

    echo "$seed" > "$iteration_dir/seed.txt"

    work="$(mktemp -d)"
    witness="$iteration_dir/witness.config"
    constraints="$iteration_dir/constraints.smt2"
    preproc="$iteration_dir/macros.txt"


    # Write directly into the archive so failed attempts retain their artifacts.
    if ! ARCH="$ARCH" "$BINARY" \
        --linux "$LINUX" \
        --output-config "$witness" \
        --output-smt-lib "$constraints" \
        --seed "$seed" \
        --load-preproc "$PREPROC_FILE" \
        --dump-preproc "$preproc" \
        > "$iteration_dir/model.log" 2>&1 || [ ! -s "$witness" ] || [ ! -s "$constraints" ] || [ ! -s "$preproc" ]; then

        model_fail=$((model_fail + 1))
        fail=$((fail + 1))

        echo "MODEL_FAILED" > "$iteration_dir/status.txt"

        cp "$iteration_dir/model.log" \
            "$FAILURES_DIR/model-seed$seed.log"

        echo "[$i/$RUNS] MODEL FAILED (seed $seed)"

        rm -rf "$work"
        continue
    fi


    # Run real kconfig
    recomputed="$work/recomputed.config"

    cp "$witness" "$recomputed"

    cp "$recomputed" "$iteration_dir/recomputed.before.config"


    kconfig_output="$(
        KCONFIG_WARN_CHANGED_INPUT=1 \
        KCONFIG_CONFIG="$recomputed" \
        make -C "$LINUX" ARCH="$ARCH" olddefconfig 2>&1
    )"

    kconfig_status=$?


    printf '%s\n' "$kconfig_output" \
        > "$iteration_dir/kconfig.log"

    cp "$recomputed" "$iteration_dir/recomputed.config"


    #
    # Detect disagreement
    #
    if [ "$kconfig_status" -ne 0 ] || \
       printf '%s' "$kconfig_output" | grep -q "user-provided values changed"; then

        fail=$((fail + 1))

        echo "CHANGED" > "$iteration_dir/status.txt"

        cp "$witness" \
            "$FAILURES_DIR/witness-seed$seed.config"

        cp "$recomputed" \
            "$FAILURES_DIR/witness-seed$seed.recomputed.config"

        cp "$iteration_dir/kconfig.log" \
            "$FAILURES_DIR/witness-seed$seed.log"


        changed_count="$(
            printf '%s' "$kconfig_output" |
            grep -c '^  CONFIG_'
        )"

        echo "[$i/$RUNS] CHANGED (seed $seed): $changed_count values"

    else

        pass=$((pass + 1))

        echo "SUCCESS" > "$iteration_dir/status.txt"

        echo "[$i/$RUNS] success (seed $seed)"

    fi


    rm -rf "$work"

done


# Summary
{
    echo
    echo "reverse differential testing complete"
    echo "date: $(date -Iseconds)"
    echo "total runs: $RUNS"
    echo "successes: $pass"
    echo "failures: $fail"
    echo "model failures: $model_fail"
    echo "model constraints: $MODEL_FILE"
    echo "preprocessed macros: $PREPROC_FILE"
    echo "macro input: ${MACRO_CACHE:-fresh evaluation}"
} | tee "$RESULTS_DIR/run.log"


[ "$fail" -eq 0 ]
