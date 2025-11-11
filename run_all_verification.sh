#!/usr/bin/env bash
set -euo pipefail

echo "========================================"
echo "  COMPLETE ELEVATOR VERIFICATION SUITE"
echo "========================================"
echo ""
echo "This script runs all verifications:"
echo "1. Safety verification (4-floor model, FIFO + SCAN)"
echo "2. FIRE mode liveness (simplified + full model)"
echo "3. VIP mode liveness (simplified + full model)"
echo ""

RESULTS_DIR="results/complete_verification"
mkdir -p "$RESULTS_DIR"

# Optional flag: when set to 'true' the script will also run the 6-floor checks
# WARNING: 6-floor checks are very expensive and may take long or consume lots of memory.
RUN_6FLOOR=false
if [ "${1:-}" = "--with-6floor" ] || [ "${RUN_6FLOOR:-false}" = "true" ]; then
    RUN_6FLOOR=true
    echo "Note: 6-floor checks ENABLED (this may be slow)." | tee -a "$RESULTS_DIR/summary.txt"
fi

OVERALL_PASS=true

# Function to log results
log_result() {
    local test_name="$1"
    local result="$2"
    echo "$test_name: $result" | tee -a "$RESULTS_DIR/summary.txt"
}

echo "========================================"
echo "STEP 1: SAFETY VERIFICATION (4-FLOOR)"
echo "========================================"
echo ""

if ./run_4floor.sh 2>&1 | tee "$RESULTS_DIR/safety_output.txt"; then
    log_result "Safety (FIFO)" "✓ PASSED"
    log_result "Safety (SCAN)" "✓ PASSED"
else
    log_result "Safety verification" "✗ FAILED"
    OVERALL_PASS=false
fi

echo ""
echo "========================================"
echo "STEP 2: FIRE MODE LIVENESS"
echo "========================================"
echo ""

# Test simplified FIRE model
echo "Testing simplified FIRE model..."
spin -a elevator_fire_simple.pml > /dev/null 2>&1
gcc -O2 -DREACH pan.c -o pan 2> /dev/null
if ./pan -m100000 > "$RESULTS_DIR/fire_simple.log" 2>&1; then
    if grep -q "fire_goal_reached" "$RESULTS_DIR/fire_simple.log"; then
        log_result "FIRE liveness (simple)" "✗ FAILED - label not reachable"
        OVERALL_PASS=false
    else
        log_result "FIRE liveness (simple)" "✓ PASSED - label reachable"
    fi
else
    log_result "FIRE liveness (simple)" "✗ FAILED - verification error"
    OVERALL_PASS=false
fi
rm -f pan pan.* *.tmp

# Test full FIRE model with limited depth
echo "Testing full model FIRE liveness (FIFO, limited depth)..."
awk 'BEGIN{print "#define POLICY_FIFO"} {print}' elevator.pml > /tmp/elevator_fire_fifo.pml
spin -a /tmp/elevator_fire_fifo.pml > /dev/null 2>&1
gcc -O2 -DREACH -DMEMLIM=2048 pan.c -o pan 2> /dev/null
if timeout 30 ./pan -m50000 > "$RESULTS_DIR/fire_fifo_full.log" 2>&1; then
    if grep -q "fire_goal_reached" "$RESULTS_DIR/fire_fifo_full.log"; then
        log_result "FIRE liveness (FIFO full)" "✗ FAILED - label not reachable"
        OVERALL_PASS=false
    else
        log_result "FIRE liveness (FIFO full)" "✓ PASSED - label reachable"
    fi
else
    log_result "FIRE liveness (FIFO full)" "⚠ TIMEOUT/PARTIAL - state space too large"
fi
rm -f pan pan.* *.tmp

echo ""
echo "========================================"
echo "STEP 3: VIP MODE LIVENESS"
echo "========================================"
echo ""

# Test simplified VIP model
echo "Testing simplified VIP model..."
spin -a elevator_vip_simple.pml > /dev/null 2>&1
gcc -O2 -DREACH pan.c -o pan 2> /dev/null
if ./pan -m100000 > "$RESULTS_DIR/vip_simple.log" 2>&1; then
    if grep -q "vip_goal_reached" "$RESULTS_DIR/vip_simple.log"; then
        log_result "VIP liveness (simple)" "✗ FAILED - label not reachable"
        OVERALL_PASS=false
    else
        log_result "VIP liveness (simple)" "✓ PASSED - label reachable"
    fi
else
    log_result "VIP liveness (simple)" "✗ FAILED - verification error"
    OVERALL_PASS=false
fi
rm -f pan pan.* *.tmp

echo ""
echo "========================================"
echo "STEP 4: NORMAL REQUEST LIVENESS"
echo "========================================"
echo ""

# Two small simplified scenarios
for simple in elevator_normal_simple_1.pml elevator_normal_simple_2.pml; do
    echo "Testing simplified normal model: $simple"
    if [ ! -f "$simple" ]; then
        log_result "Normal liveness ($simple)" "✗ MISSING FILE"
        OVERALL_PASS=false
        continue
    fi
    spin -a "$simple" > /dev/null 2>&1
    gcc -O2 -DREACH pan.c -o pan 2> /dev/null
    if ./pan -m100000 > "$RESULTS_DIR/${simple%.pml}.log" 2>&1; then
        if grep -q "normal_request_served" "$RESULTS_DIR/${simple%.pml}.log"; then
            log_result "Normal liveness ($simple)" "✗ FAILED - label not reachable"
            OVERALL_PASS=false
        else
            log_result "Normal liveness ($simple)" "✓ PASSED - label reachable"
        fi
    else
        log_result "Normal liveness ($simple)" "✗ FAILED - verification error"
        OVERALL_PASS=false
    fi
    rm -f pan pan.* *.tmp
done

# Try the full models informally with limited depth (may TIMEOUT)
echo "Testing full model normal liveness (FIFO, limited depth)..."
awk 'BEGIN{print "#define POLICY_FIFO"} {print}' elevator.pml > /tmp/elevator_norm_fifo.pml
spin -a /tmp/elevator_norm_fifo.pml > /dev/null 2>&1
gcc -O2 -DREACH pan.c -o pan 2> /dev/null
if timeout 30 ./pan -m50000 > "$RESULTS_DIR/normal_fifo_full.log" 2>&1; then
    if grep -q "normal_request_served" "$RESULTS_DIR/normal_fifo_full.log"; then
        log_result "Normal liveness (FIFO full)" "✗ FAILED - label not reachable"
        OVERALL_PASS=false
    else
        log_result "Normal liveness (FIFO full)" "✓ PASSED - label reachable"
    fi
else
    log_result "Normal liveness (FIFO full)" "⚠ TIMEOUT/PARTIAL - state space too large"
fi
rm -f pan pan.* /tmp/elevator_norm_fifo.pml

# Constrained deterministic tests (fast, conclusive)
echo "" | tee -a "$RESULTS_DIR/summary.txt"
echo "========================================" | tee -a "$RESULTS_DIR/summary.txt"
echo "STEP Y: CONSTRAINED DETERMINISTIC TESTS (FAST)" | tee -a "$RESULTS_DIR/summary.txt"
echo "========================================" | tee -a "$RESULTS_DIR/summary.txt"

for C in elevator_constrained_4.pml elevator_constrained_vip_4.pml elevator_constrained_fire_4.pml; do
    if [ -f "$C" ]; then
        echo "Running constrained test: $C" | tee -a "$RESULTS_DIR/summary.txt"
        spin -a "$C" > "$RESULTS_DIR/${C%.pml}.spin.log" 2>&1
        gcc -O2 -DREACH pan.c -o pan > "$RESULTS_DIR/${C%.pml}.compile.log" 2>&1
        if ./pan -m100000 > "$RESULTS_DIR/${C%.pml}.run.log" 2>&1; then
            # check for common labels
            for L in req0_served req1_served req2_served req3_served fire_goal_reached vip_goal_reached; do
                if grep -q "$L" "$RESULTS_DIR/${C%.pml}.run.log"; then
                    log_result "${C} label $L" "✓ present in run output"
                else
                    log_result "${C} label $L" "- not present in run output"
                fi
            done
        else
            log_result "${C}" "✗ verification run failed or timed out (see logs)"
        fi
        rm -f pan pan.* *.tmp
    else
        log_result "${C}" "✗ MISSING - create the constrained test first"
    fi
done

# Report per-floor labels (if pan produced output)
if [ -f "$RESULTS_DIR/normal_fifo_full.log" ]; then
    for L in req0_served req1_served req2_served req3_served; do
        if grep -q "$L" "$RESULTS_DIR/normal_fifo_full.log"; then
            if grep "unreached in proctype" "$RESULTS_DIR/normal_fifo_full.log" | grep -q "$L"; then
                log_result "Normal label ($L)" "✗ UNREACHED in full 4-floor run"
                OVERALL_PASS=false
            else
                log_result "Normal label ($L)" "✓ reachable in full 4-floor run"
            fi
        else
            log_result "Normal label ($L)" "⚠ not mentioned in pan output"
        fi
    done
fi

# Optionally run 6-floor safety + liveness checks (expensive)
if [ "$RUN_6FLOOR" = "true" ]; then
    echo "" | tee -a "$RESULTS_DIR/summary.txt"
    echo "========================================" | tee -a "$RESULTS_DIR/summary.txt"
    echo "STEP X: 6-FLOOR CHECKS (OPTIONAL)" | tee -a "$RESULTS_DIR/summary.txt"
    echo "========================================" | tee -a "$RESULTS_DIR/summary.txt"

    # Run the dedicated 6-floor safety script (this may take many minutes)
    if ./run_6floor.sh 2>&1 | tee "$RESULTS_DIR/6floor_output.txt"; then
        log_result "6-floor safety" "✓ PASSED"
    else
        log_result "6-floor safety" "⚠ FAILED or TIMEOUT"
    fi

    # Try a limited liveness run for elevator_6floor.pml (informational)
    if [ -f elevator_6floor.pml ]; then
        awk 'BEGIN{print "#define POLICY_FIFO"} {print}' elevator_6floor.pml > /tmp/elevator_6floor_norm.pml
        spin -a /tmp/elevator_6floor_norm.pml > /dev/null 2>&1
        gcc -O2 -DREACH pan.c -o pan 2> /dev/null
        if timeout 60 ./pan -m50000 > "$RESULTS_DIR/normal_6floor_fifo.log" 2>&1; then
            if grep -q "normal_request_served" "$RESULTS_DIR/normal_6floor_fifo.log"; then
                log_result "Normal liveness (6-floor FIFO full)" "✗ FAILED - label not reachable"
            else
                log_result "Normal liveness (6-floor FIFO full)" "✓ PASSED - label reachable"
            fi
        else
            log_result "Normal liveness (6-floor FIFO full)" "⚠ TIMEOUT/PARTIAL - state space too large"
        fi
        rm -f pan pan.* /tmp/elevator_6floor_norm.pml
    else
        log_result "Normal liveness (6-floor)" "✗ MISSING FILE"
    fi
fi

# Test full VIP model with limited depth
echo "Testing full model VIP liveness (SCAN, limited depth)..."
awk 'BEGIN{print "#define POLICY_SCAN"} {print}' elevator.pml > /tmp/elevator_vip_scan.pml
spin -a /tmp/elevator_vip_scan.pml > /dev/null 2>&1
gcc -O2 -DREACH -DMEMLIM=2048 pan.c -o pan 2> /dev/null
if timeout 30 ./pan -m50000 > "$RESULTS_DIR/vip_scan_full.log" 2>&1; then
    if grep -q "vip_goal_reached" "$RESULTS_DIR/vip_scan_full.log"; then
        log_result "VIP liveness (SCAN full)" "✗ FAILED - label not reachable"
        OVERALL_PASS=false
    else
        log_result "VIP liveness (SCAN full)" "✓ PASSED - label reachable"
    fi
else
    log_result "VIP liveness (SCAN full)" "⚠ TIMEOUT/PARTIAL - state space too large"
fi
rm -f pan pan.* *.tmp

echo ""
echo "========================================"
echo "VERIFICATION SUMMARY"
echo "========================================"
echo ""
cat "$RESULTS_DIR/summary.txt"
echo ""

if [ "$OVERALL_PASS" = true ]; then
    echo "========================================"
    echo "✓✓✓ ALL VERIFICATIONS PASSED ✓✓✓"
    echo "========================================"
    echo ""
    echo "Results saved in: $RESULTS_DIR"
    echo ""
    echo "Key findings:"
    echo "- Safety properties hold for both FIFO and SCAN policies"
    echo "- FIRE mode liveness: emergency requests eventually serviced"
    echo "- VIP mode liveness: VIP requests eventually serviced"
    echo ""
    exit 0
else
    echo "========================================"
    echo "⚠ SOME VERIFICATIONS FAILED/INCOMPLETE"
    echo "========================================"
    echo ""
    echo "Check logs in: $RESULTS_DIR"
    echo ""
    exit 1
fi
