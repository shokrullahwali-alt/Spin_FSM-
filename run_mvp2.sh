#!/usr/bin/env bash
set -euo pipefail

MODEL=elevator_mvp.pml
LTL=mvp_properties.ltl
TAG=mvp2
PAN_DEPTH=${PAN_DEPTH:-20000}

mkdir -p results/${TAG}

# For MVP, we check SAFETY via inline assertions in the model.
# Run SPIN without a never claim to verify assertions.

echo "Running SPIN verification for ${MODEL}..."

# generate pan.c from model (no never claim)
spin -a "${MODEL}" > results/${TAG}/spin_compile.txt 2>&1 || true

# compile pan if pan.c exists
if [[ -f pan.c ]]; then
  gcc -O2 pan.c -o pan 2> results/${TAG}/gcc.txt || true
fi

# run pan to check for assertion violations and invalid end states
if [[ -x ./pan ]]; then
  ./pan -a -m${PAN_DEPTH} > results/${TAG}/verification.log 2>&1 || true
else
  echo "No pan binary available; check SPIN installation" > results/${TAG}/verification.log
fi

# summary
if grep -q "errors: 0" results/${TAG}/verification.log 2>/dev/null; then
  echo "Verification PASSED: no assertion violations or invalid end states." > results/${TAG}/summary.txt
else
  echo "Verification FAILED: see verification.log for details." > results/${TAG}/summary.txt
fi

# cleanup temp files
rm -f pan pan.c 2>/dev/null || true

echo "Verification complete. Results in results/${TAG}/"
cat results/${TAG}/summary.txt