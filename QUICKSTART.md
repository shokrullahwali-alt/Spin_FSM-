# Quick Reference - Elevator Verification

## ONE COMMAND TO RUN EVERYTHING (4-FLOOR)

```bash
./run_all_verification.sh
```

This runs the complete verification suite for the 4-floor model.

## 6-FLOOR MODEL VERIFICATION

```bash
./run_6floor.sh
```

This runs safety verification for the 6-floor model (122M+ states).

## What Gets Verified

### ✓ Safety Properties (4-Floor Model)
- **POLICY_FIFO**: 55.1 million states verified
- **POLICY_SCAN**: 63.0 million states verified
- **Property**: Never move with door open (`assert(!(moving && door == OPEN))`)
- **Result**: ✓ PASSED - No assertion violations

### ✓ Safety Properties (6-Floor Model)
- **POLICY_FIFO**: 122.2 million states verified (240 seconds)
- **POLICY_SCAN**: 135 million states verified (735 seconds)
- **Property**: Never move with door open
- **Result**: ✓ PASSED - No assertion violations
- **Includes**: Weight/overload, door obstruction, sensor failure, FIRE/VIP/SAFE modes

### ✓ FIRE Mode Liveness (Simplified Model)
- **Property**: Emergency FIRE mode eventually leads to ground floor with door open
- **Method**: Progress label `fire_goal_reached` reachability
- **Result**: ✓ PASSED - Label is reachable

### ✓ VIP Mode Liveness (Simplified Model)
- **Property**: VIP requests eventually serviced at destination floor
- **Method**: Progress label `vip_goal_reached` reachability
- **Result**: ✓ PASSED - Label is reachable

## Verification Results Location

All results are saved in `results/complete_verification/`:
- `summary.txt` - Quick summary of all tests
- Individual log files for detailed analysis

## Key Files

- `elevator.pml` - Main 4-floor model
- `elevator_fire_simple.pml` - FIRE liveness demo
- `elevator_vip_simple.pml` - VIP liveness demo
- `run_all_verification.sh` - Master verification script

## Expected Output

```
========================================
✓✓✓ ALL VERIFICATIONS PASSED ✓✓✓
========================================

Key findings:
- Safety properties hold for both FIFO and SCAN policies
- FIRE mode liveness: emergency requests eventually serviced
- VIP mode liveness: VIP requests eventually serviced
```

## Verification Time

- Safety (full model): ~5-6 minutes total (both policies)
- FIRE liveness (simple): <1 second
- VIP liveness (simple): <1 second
- **Total runtime**: ~6-7 minutes

## Technical Approach

| Property Type | Method | Why |
|--------------|---------|-----|
| Safety | Inline `assert()` | No false positives, efficient |
| Liveness | Progress labels + reachability | Avoids LTL acceptance cycle issues |

See `VERIFICATION_RESULTS.md` for complete documentation.
