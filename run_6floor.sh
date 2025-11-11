#!/usr/bin/env bash
set -euo pipefail

MODEL="elevator_6floor.pml"
PAN_DEPTH="${PAN_DEPTH:-2000000}"
RESULTS_DIR="results/6floor"

echo "Running SPIN verification for 6-floor elevator model..."
echo "Model: $MODEL (6 floors: 0..5)"
echo "Features: weight/overload, door obstruction, sensor failure, FIRE/VIP/SAFE modes"
echo "Max depth: $PAN_DEPTH"
echo ""

mkdir -p "$RESULTS_DIR"

# Test with FIFO policy
echo "=== Testing with POLICY_FIFO ==="
FIFO_MODEL="${RESULTS_DIR}/elevator_fifo.pml"
awk 'BEGIN{print "#define POLICY_FIFO"} {print}' "$MODEL" > "$FIFO_MODEL"

echo "Generating verifier (spin -a)..."
spin -a "$FIFO_MODEL" > "${RESULTS_DIR}/spin_compile_fifo.txt" 2>&1

echo "Compiling verifier (gcc)..."
gcc -O2 -DMEMLIM=8192 -DVECTORSZ=16384 pan.c -o pan 2> "${RESULTS_DIR}/gcc_fifo.txt"

echo "Running verification (checking assertions and invalid end states)..."
echo "Note: 6-floor model has larger state space - this may take longer..."
./pan -a -m${PAN_DEPTH} > "${RESULTS_DIR}/verification_fifo.log" 2>&1 || true

# Check results
if grep -q "errors: 0" "${RESULTS_DIR}/verification_fifo.log"; then
    FIFO_STATES=$(grep "states, stored" "${RESULTS_DIR}/verification_fifo.log" | head -1 | awk '{print $1}')
    FIFO_TIME=$(grep "elapsed time" "${RESULTS_DIR}/verification_fifo.log" | head -1 | awk '{print $3}')
    echo "✓ POLICY_FIFO verification PASSED: no assertion violations or invalid end states."
    echo "  States explored: $FIFO_STATES"
    echo "  Time: $FIFO_TIME seconds"
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
gcc -O2 -DMEMLIM=8192 -DVECTORSZ=16384 pan.c -o pan 2> "${RESULTS_DIR}/gcc_scan.txt"

echo "Running verification (checking assertions and invalid end states)..."
./pan -a -m${PAN_DEPTH} > "${RESULTS_DIR}/verification_scan.log" 2>&1 || true

# Check results
if grep -q "errors: 0" "${RESULTS_DIR}/verification_scan.log"; then
    SCAN_STATES=$(grep "states, stored" "${RESULTS_DIR}/verification_scan.log" | head -1 | awk '{print $1}')
    SCAN_TIME=$(grep "elapsed time" "${RESULTS_DIR}/verification_scan.log" | head -1 | awk '{print $3}')
    echo "✓ POLICY_SCAN verification PASSED: no assertion violations or invalid end states."
    echo "  States explored: $SCAN_STATES"
    echo "  Time: $SCAN_TIME seconds"
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
echo "=== Verification Summary (6-FLOOR MODEL) ==="
echo "Results directory: $RESULTS_DIR"
FIFO_RESULT=$(cat "${RESULTS_DIR}/fifo_result.txt")
SCAN_RESULT=$(cat "${RESULTS_DIR}/scan_result.txt")

echo "POLICY_FIFO: $FIFO_RESULT"
echo "POLICY_SCAN: $SCAN_RESULT"

if [[ "$FIFO_RESULT" == "PASSED" && "$SCAN_RESULT" == "PASSED" ]]; then
    echo ""
    echo "✓ All 6-floor verification tests PASSED!"
    echo ""
    echo "Model features verified:"
    echo "  - Safety: Never move with door open"
    echo "  - Weight/overload handling (MAX_WEIGHT=10)"
    echo "  - Door obstruction detection"
    echo "  - Sensor failure → SAFE mode"
    echo "  - FIRE mode priority"
    echo "  - VIP request handling"
    echo "  - Normal operation (FIFO and SCAN policies)"
    exit 0
else
    echo ""
    echo "✗ Some verification tests FAILED. Check logs in $RESULTS_DIR"
    exit 1
fi
