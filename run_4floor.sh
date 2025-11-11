#!/usr/bin/env bash
set -euo pipefail

MODEL="elevator.pml"
PAN_DEPTH="${PAN_DEPTH:-2000000}"  # Larger depth for 4-floor model
RESULTS_DIR="results/4floor"

echo "Running SPIN verification for 4-floor elevator model..."
echo "Model: $MODEL"
echo "Max depth: $PAN_DEPTH"

mkdir -p "$RESULTS_DIR"

# Test with FIFO policy
echo ""
echo "=== Testing with POLICY_FIFO ==="
FIFO_MODEL="${RESULTS_DIR}/elevator_fifo.pml"
awk 'BEGIN{print "#define POLICY_FIFO"} {print}' "$MODEL" > "$FIFO_MODEL"

echo "Generating verifier (spin -a)..."
spin -a "$FIFO_MODEL" > "${RESULTS_DIR}/spin_compile_fifo.txt" 2>&1

echo "Compiling verifier (gcc)..."
gcc -O2 -DMEMLIM=4096 -DVECTORSZ=8192 pan.c -o pan 2> "${RESULTS_DIR}/gcc_fifo.txt"

echo "Running verification (checking assertions and invalid end states)..."
./pan -a -m${PAN_DEPTH} > "${RESULTS_DIR}/verification_fifo.log" 2>&1 || true

# Check results
if grep -q "errors: 0" "${RESULTS_DIR}/verification_fifo.log"; then
    echo "✓ POLICY_FIFO verification PASSED: no assertion violations or invalid end states."
    echo "PASSED" > "${RESULTS_DIR}/fifo_result.txt"
else
    echo "✗ POLICY_FIFO verification FAILED. See ${RESULTS_DIR}/verification_fifo.log"
    echo "FAILED" > "${RESULTS_DIR}/fifo_result.txt"
    if [[ -f pan.trail ]]; then
        mv pan.trail "${RESULTS_DIR}/fifo.trail"
    fi
fi

# Cleanup before SCAN test
rm -f pan pan.* *.tmp

# Test with SCAN policy
echo ""
echo "=== Testing with POLICY_SCAN ==="
SCAN_MODEL="${RESULTS_DIR}/elevator_scan.pml"
awk 'BEGIN{print "#define POLICY_SCAN"} {print}' "$MODEL" > "$SCAN_MODEL"

echo "Generating verifier (spin -a)..."
spin -a "$SCAN_MODEL" > "${RESULTS_DIR}/spin_compile_scan.txt" 2>&1

echo "Compiling verifier (gcc)..."
gcc -O2 -DMEMLIM=4096 -DVECTORSZ=8192 pan.c -o pan 2> "${RESULTS_DIR}/gcc_scan.txt"

echo "Running verification (checking assertions and invalid end states)..."
./pan -a -m${PAN_DEPTH} > "${RESULTS_DIR}/verification_scan.log" 2>&1 || true

# Check results
if grep -q "errors: 0" "${RESULTS_DIR}/verification_scan.log"; then
    echo "✓ POLICY_SCAN verification PASSED: no assertion violations or invalid end states."
    echo "PASSED" > "${RESULTS_DIR}/scan_result.txt"
else
    echo "✗ POLICY_SCAN verification FAILED. See ${RESULTS_DIR}/verification_scan.log"
    echo "FAILED" > "${RESULTS_DIR}/scan_result.txt"
    if [[ -f pan.trail ]]; then
        mv pan.trail "${RESULTS_DIR}/scan.trail"
    fi
fi

# Cleanup
rm -f pan pan.* *.tmp

# Generate summary
echo ""
echo "=== Verification Summary ==="
echo "Results directory: $RESULTS_DIR"
FIFO_RESULT=$(cat "${RESULTS_DIR}/fifo_result.txt")
SCAN_RESULT=$(cat "${RESULTS_DIR}/scan_result.txt")

echo "POLICY_FIFO: $FIFO_RESULT"
echo "POLICY_SCAN: $SCAN_RESULT"

if [[ "$FIFO_RESULT" == "PASSED" && "$SCAN_RESULT" == "PASSED" ]]; then
    echo ""
    echo "✓ All verification tests PASSED!"
    exit 0
else
    echo ""
    echo "✗ Some verification tests FAILED. Check logs in $RESULTS_DIR"
    exit 1
fi
