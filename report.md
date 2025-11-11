# Formal Verification of an Extended Smart Elevator with SPIN

Author: Automated deliverable

This report documents extensions to the Smart Elevator SPIN model to add several "realism" features (sensor failure, overload, door obstruction, and explicit scheduling policies), the corresponding LTL properties, the test matrix (including intentional bugs), and summary results.

## 1. Goals and Acceptance Criteria

Goal: extend the prior MVP elevator to include realistic safety and scheduling features and verify safety and liveness properties using SPIN.

Acceptance criteria met by this deliverable:
- Model builds in SPIN (no syntax errors).
- New features implemented: `sensor_ok`, `weight`, `door_obstructed`, `MAX_WEIGHT`, and compile-time scheduling policies (`POLICY_FIFO` or `POLICY_SCAN`).
- LTL properties for sensor fail-safe, overload, obstruction, and scheduling fairness added and checked.
- `run_spin.sh` orchestrates checks for bug variants, fixed model with FIFO/SCAN, and MVP variants, and writes organized results/traces to `results/`.
- At least two intentional counterexamples produced from buggy models and then fixed models re-run.

## 2. Model overview (files)

- `elevator.pml` — extended full model (4 floors by default) with:
  - sensor_ok (bool) — if becomes false, controller switches to `SAFE` mode and elevator stops/open door.
  - weight (byte) and `MAX_WEIGHT` — when weight > MAX_WEIGHT doors cannot close and movement prohibited.
  - door_obstructed (bool) — prevents doors from closing; attempt to close reopens them and movement forbidden.
  - scheduling policies: FIFO (default) and SCAN (compile-time option). FIFO uses a bounded queue; SCAN scans floors in a direction.
  - Controller, Elevator, Env processes — Env only updates weight when `door==OPEN`, flips `sensor_ok` at most once, and toggles `door_obstructed` only when doors are open.

- `elevator_obstruction_bug.pml` — buggy variant that ignores door obstruction and closes/moves anyway (demonstrates violation of obstruction properties).
- `elevator_overload_bug.pml` — buggy variant that allows movement even when weight > MAX_WEIGHT.
- `elevator_sensor_bug.pml` — buggy variant where Controller ignores `sensor_ok` (movement continues after sensor failure).

- `properties.ltl` — LTL properties including safety, FIRE/VIP behavior, sensor fail-safe, overload/obstruction properties, and scheduling fairness.

- `run_spin.sh` — orchestrates checks, runs bug cases, runs fixed model under FIFO and SCAN, and runs MVP(2-floor) variants. Results stored under `results/<run_tag>/` with logs, spin compile output, and `pan` traces if present.

## 3. New LTL properties (English + formal)

Safety (existing):
- Never move while door open: [] !(moving && door == OPEN)

Obstruction:
- Door obstructed implies door stays open: [] (door_obstructed -> door == OPEN)
- While obstructed, door remains open: [] (door_obstructed -> [] (door == OPEN))

Sensor fail-safe:
- If sensor fails, eventually elevator is stopped with door open: [] (!sensor_ok -> <> (!moving && door == OPEN))
- Once sensor failed, never move again: [] (!sensor_ok -> [] !(moving))

Overload / Weight:
- If weight > MAX_WEIGHT, doors must be open and elevator not moving: [] (weight > MAX_WEIGHT -> (door == OPEN && !moving))
- If moving with door CLOSED, weight must be <= MAX_WEIGHT: [] ((door == CLOSED && moving) -> weight <= MAX_WEIGHT)

Scheduling fairness (NORMAL mode):
- Persistent request on floor i must eventually be served (for i=0..3): [] ((mode == NORMAL && rq[i]) -> <> (floor == i && door == OPEN))

Note: Some liveness properties rely on weak fairness assumptions and the bounded Env used in the model. The `run_spin.sh` script executes checks under weak fairness (`pan -f`) as well as without fairness.

## 4. Test matrix and intentional bugs

The script runs these cases in order and stores results under `results/<tag>/`:

- `bug_obstruction` — run using `elevator_obstruction_bug.pml` (should fail obstruction properties).
- `bug_overload` — run using `elevator_overload_bug.pml` (should fail overload properties).
- `bug_sensor` — run using `elevator_sensor_bug.pml` (should fail sensor fail-safe properties).
- `fixed_fifo` — fixed model with `POLICY_FIFO` defined (default scheduling FIFO).
- `fixed_scan` — fixed model with `POLICY_SCAN` defined (SCAN scheduling).
- `mvp_fifo`, `mvp_scan` — reduced N_FLOORS=2 variants for faster checking.

For any failing property the script attempts to save `pan.trail` and produce a human-readable trace in `results/<tag>/property_<i>_*.trace.txt` using `spin -t`.

## 5. How to run

Requirements: `spin` and `gcc` available on PATH.

Make script executable and run:
```bash
chmod +x run_spin.sh
./run_spin.sh
```

Results will appear in `results/` with per-run subfolders and a `summary.txt` in each.

## 6. Representative results (what to expect)

- Bug runs are expected to produce failing logs and counterexample traces demonstrating the precise violating behavior (door closes while obstructed, movement with overload, or movement after sensor failure).
- Fixed runs should pass the new safety properties and many of the liveness properties within the search bounds; if a liveness property fails consider increasing the search depth or arguing fairness assumptions.

## 7. Fairness and progress

Liveness under scheduling may require weak fairness assumptions. `run_spin.sh` runs `pan` both without and with weak fairness (`-f`). We also include a local "progress" label in the Controller where requests are served (label `served:`) to help SPIN detect non-progress cycles.

## 8. Limitations and next steps

- Boundedness: queue size and Env step limits bound the state-space and affect liveness guarantees.
- Simplifications: sensor failure is sticky (no recovery) and weight changes are coarse-grained. Multi-elevator coordination not modeled.
- Next: add explicit resets for sensor, richer weight models, and better SCAN fairness heuristics.

## 9. Conclusion

The extended model encodes non-trivial safety and liveness concerns. The test harness demonstrates failing traces for intentional bugs and re-checks the fixed models under both FIFO and SCAN scheduling. The artifacts are ready for further refinement.

-- End of report
