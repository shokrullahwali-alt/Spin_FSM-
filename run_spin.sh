#!/usr/bin/env bash
set -euo pipefail

MODEL=elevator.pml
BUG_OBSTRUCT=elevator_obstruction_bug_full.pml
BUG_OVERLOAD=elevator_overload_bug.pml
BUG_SENSOR=elevator_sensor_bug.pml
LTL=properties.ltl
mkdir -p results

check_model() {
  local model_file="$1"
  local run_tag="$2"
  echo "Running checks on model: $model_file (tag=$run_tag)"
  mkdir -p results/${run_tag}
  i=0
  while IFS= read -r line || [[ -n "$line" ]]; do
    formula="$line"
    # skip comments and blank lines
    if [[ -z "$formula" || "$formula" =~ ^\s*// ]]; then
      continue
    fi
    echo "=== [$run_tag] Checking property $i: $formula ==="
    # generate never claim; capture spin stderr if it fails
    spin -f "$formula" > never${i}.pml 2> results/${run_tag}/property_${i}.spinerr.txt || {
      echo "spin failed to translate formula $i (see results/${run_tag}/property_${i}.spinerr.txt). Skipping." | tee -a results/${run_tag}/summary.txt
      rm -f never${i}.pml
      i=$((i+1))
      continue
    }
    # compose model and never claim
    cat "$model_file" never${i}.pml > model${i}.pml
    # generate pan
    if ! spin -a model${i}.pml > results/${run_tag}/spin_compile_${i}.txt 2>&1; then
      echo "spin -a failed for property $i (see results/${run_tag}/spin_compile_${i}.txt). Skipping." | tee -a results/${run_tag}/summary.txt
      rm -f never${i}.pml model${i}.pml
      i=$((i+1))
      continue
    fi
    gcc -O2 pan.c -o pan 2> results/${run_tag}/gcc_${i}.txt || true

    # Run pan: no fairness, then weak fairness (-f); use large depth
  ./pan -a -m${PAN_DEPTH:-1000000} > results/${run_tag}/property_${i}_nofair.log 2>&1 || true
    if grep -q "errors: 0" results/${run_tag}/property_${i}_nofair.log; then
      echo "Property $i (no fairness) holds." | tee -a results/${run_tag}/summary.txt
    else
      echo "Property $i (no fairness) FAILED. See results/${run_tag}/property_${i}_nofair.log" | tee -a results/${run_tag}/summary.txt
      if [[ -f pan.trail ]]; then
        mv pan.trail results/${run_tag}/property_${i}_nofair.trail || true
        spin -t model${i}.pml < results/${run_tag}/property_${i}_nofair.trail > results/${run_tag}/property_${i}_nofair.trace.txt 2>&1 || true
      fi
    fi

  ./pan -a -f -m${PAN_DEPTH:-1000000} > results/${run_tag}/property_${i}_weakfair.log 2>&1 || true
    if grep -q "errors: 0" results/${run_tag}/property_${i}_weakfair.log; then
      echo "Property $i (weak fairness) holds." | tee -a results/${run_tag}/summary.txt
    else
      echo "Property $i (weak fairness) FAILED. See results/${run_tag}/property_${i}_weakfair.log" | tee -a results/${run_tag}/summary.txt
      if [[ -f pan.trail ]]; then
        mv pan.trail results/${run_tag}/property_${i}_weakfair.trail || true
        spin -t model${i}.pml < results/${run_tag}/property_${i}_weakfair.trail > results/${run_tag}/property_${i}_weakfair.trace.txt 2>&1 || true
      fi
    fi

    # cleanup model-specific temporary files
    rm -f pan pan.* *.tmp never${i}.pml model${i}.pml pan.c || true
    i=$((i+1))
  done < "$LTL"
}

echo "Running BUG runs (intentional faults)"
check_model "$BUG_OBSTRUCT" "bug_obstruction"
check_model "$BUG_OVERLOAD" "bug_overload"
check_model "$BUG_SENSOR" "bug_sensor"

echo "Running FIXED model with POLICY_FIFO (default)"
# ensure FIFO policy defined at top of temp model
awk 'BEGIN{print "#define POLICY_FIFO"} {print}' "$MODEL" > elevator_fifo.pml
check_model "elevator_fifo.pml" "fixed_fifo"

echo "Running FIXED model with POLICY_SCAN"
awk 'BEGIN{print "#define POLICY_SCAN"} {print}' "$MODEL" > elevator_scan.pml
check_model "elevator_scan.pml" "fixed_scan"

echo "MVP (2-floor) runs: generating temporary MVP models"
# generate MVP variants for FIFO/SCAN
awk '{ if ($0 ~ /#define N_FLOORS/) { print "#define N_FLOORS 2" } else print }' elevator_fifo.pml > elevator_mvp_fifo.pml
awk '{ if ($0 ~ /#define N_FLOORS/) { print "#define N_FLOORS 2" } else print }' elevator_scan.pml > elevator_mvp_scan.pml
check_model "elevator_mvp_fifo.pml" "mvp_fifo"
check_model "elevator_mvp_scan.pml" "mvp_scan"

echo "All runs complete. See results/ for per-run logs and traces."
