/- N3 timing ladder stage 1: decide +kernel on ONE representative entry — the
worst cell (22,23) of the 45x45 staircase corner: 36-digit Z value, coefficient
row (al/be) x coefficient column (a_0/b_0), Kronecker of 1 - vecMulVec products.
Budget: 5 min. If this passes, stage 2 (row 22) and stage 3 (full 45x45) follow. -/
import StaircasePort.Cert

open StaircasePort.Stair
open Matrix

set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem n3_t1_entry_22_23 :
    corZStair stairMZ 22 23 % (stairCertP : ℤ) =
      (((stairCertRows.getD 22 []).getD 23 0 : ℕ) : ℤ) := by
  decide +kernel

#print axioms n3_t1_entry_22_23
