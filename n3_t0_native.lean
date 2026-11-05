/- N3 timing ladder stage 0: native_decide sanity checks (seconds expected).
Confirms every N3 numeric prop is TRUE at the Lean level (data/family alignment
between CertData.lean, the LtermsZStair/RtermsZStair if-chains and the extracted
cert_data.json) BEFORE spending kernel time on the decide +kernel ladder.
VM-trusted (native_decide axioms), timing-only artifact — not part of the submission. -/
import StaircasePort.Cert

open StaircasePort.Stair
open IntMul.Kappa.R6.Bit.NB (certChk)
open Matrix

set_option maxRecDepth 20000
set_option maxHeartbeats 0

-- y ⬝ x = 1 EXACT over Z (both pairs; feeds stairQxy1/2)
example : stairWY1 ⬝ᵥ stairWX1 = (1 : ℤ) := by native_decide
example : stairWY2 ⬝ᵥ stairWX2 = (1 : ℤ) := by native_decide

-- Q-level dots exactly as stairQxy1/2 state them
example : stairQY1 ⬝ᵥ stairQX1 = (1 : ℚ) := by native_decide
example : stairQY2 ⬝ᵥ stairQX2 = (1 : ℚ) := by native_decide

-- worst corner entry (22,23): 36-digit Z value (extract/n3_corner_stats.py argmax)
example : corZStair stairMZ 22 23 % (stairCertP : ℤ) =
    (((stairCertRows.getD 22 []).getD 23 0 : ℕ) : ℤ) := by native_decide

-- the FULL stair_cert_entries prop (2025 entries)
example : ((List.range 45).all fun i => (List.range 45).all fun j =>
    decide (corZStair stairMZ i j % (stairCertP : ℤ) =
      (((stairCertRows.getD i []).getD j 0 : ℕ) : ℤ))) = true := by native_decide

-- the FULL stair_cert_chk prop
example : certChk stairCertRows stairCertCols 45 stairCertP = true := by native_decide

#eval "N3-T0-ALL-PASSED"
