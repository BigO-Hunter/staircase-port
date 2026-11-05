/- N3 timing ladder stage 2: decide +kernel on the WORST ROW (22 — the al/be
coefficient row; heaviest total digits per extract/n3_corner_stats.py).
Calibrates the per-entry marginal kernel cost: full 45x45 ~= 45x this row's
marginal. Budget: 30 min. -/
import StaircasePort.Cert

open StaircasePort.Stair
open Matrix

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem n3_t2_row_22 :
    ((List.range 45).all fun j =>
      decide (corZStair stairMZ 22 j % (stairCertP : ℤ) =
        (((stairCertRows.getD 22 []).getD j 0 : ℕ) : ℤ))) = true := by
  decide +kernel

#print axioms n3_t2_row_22
