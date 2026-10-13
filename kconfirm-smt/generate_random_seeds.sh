#!/usr/bin/env bash
# Generate COUNT unsigned 32-bit seeds, one decimal value per line.
# Sampling is with replacement: duplicate seeds are allowed.
# Save and reuse the output to reproduce the experiment:
#   ./generate_random_seeds.sh 2000 > random-seeds.txt

set -euo pipefail

if [[ $# -ne 1 ]] || [[ ! $1 =~ ^[1-9][0-9]*$ ]]; then
    echo "usage: $0 COUNT (a positive integer)" >&2
    exit 2
fi

exec shuf --repeat \
    --input-range=0-4294967295 \
    --head-count="$1" \
    --random-source=/dev/urandom
