/-
# N7 data — kernel-decided pins for the CORNER CLAUSE (the heavy `decide` payload)

Split from `Corner.lean` for build economy: every module here is banked independently,
so each `lake build` stage fits the host's kill window (see SCAFFOLD.md "## CORNER
RESUME"). Contents: the 8 cut-table membership pins (`n7_mem_*`, 148 kernel decides
over the 689-block list) and the witness discharges (`n7_hT_witness` 21 norm_num cases,
`n7_hM1_witness`/`n7_hM2_witness` N2c certificates verbatim, and the Pivot-level
integration check).
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Pivot

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The two-term column coefficients (Nat-indexed to match the extracted data). -/
def stairRunA (r : ℕ) : ℚ := ((stairAZL.getD r 0 : ℤ) : ℚ)
def stairRunB (r : ℕ) : ℚ := ((stairBZL.getD r 0 : ℤ) : ℚ)

/-- `l` as a Fin index (no hypotheses needed: `i % 23`); for `i < 23` this is `⟨i, _⟩`. -/
def n7Fin (i : ℕ) : Fin 23 := ⟨i % 23, by omega⟩

/-! #### witness discharges (all hypotheses hold at the extracted witness) -/

/-- hT at the witness: the 21 run-1 diagonal deviations are nonzero. -/
theorem n7_hT_witness : ∀ l : ℕ, 1 ≤ l → l ≤ 21 →
    stairRunA l * stairQX2 (n7Fin l) * stairQY2 (n7Fin (l + 1))
      + stairRunB l * stairQX1 (n7Fin l) * stairQY1 (n7Fin (l + 1)) ≠ 0 := by
  intro l h1 h2
  interval_cases l <;>
    simp only [stairRunA, stairRunB, n7Fin, stairQX1, stairQX2, stairQY1, stairQY2,
      stairWX1L, stairWX2L, stairWY1L, stairWY2L, stairAZL, stairBZL, List.getD,
      List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, Int.cast_ofNat,
      Int.cast_one, Int.cast_neg, Nat.reduceMod, Nat.reduceAdd] <;>
    norm_num

/-- hM1 at the witness: N2c certificate 1 verbatim. -/
theorem n7_hM1_witness : 25 ≤ rk stairCornerQ 25 20 :=
  n2c_rank_lower (by omega) n2cR1 n2cC1 (by decide) (by decide) (by decide)
    n2cS1 n2cT1 n2cChk1 n2cEnt1

/-- hM2 at the witness: N2c's 26-certificates verbatim (one per run-2 position). -/
theorem n7_hM2_witness : ∀ t : ℕ, t < 18 → 26 ≤ rk stairCornerQ (26 + t) (2 + t) := by
  intro t ht
  interval_cases t
  · exact n2c_rank_lower (by omega) n2cR12 n2cC12 (by decide) (by decide) (by decide)
      n2cS12 n2cT12 n2cChk12 n2cEnt12
  · exact n2c_rank_lower (by omega) n2cR16 n2cC16 (by decide) (by decide) (by decide)
      n2cS16 n2cT16 n2cChk16 n2cEnt16
  · exact n2c_rank_lower (by omega) n2cR8 n2cC8 (by decide) (by decide) (by decide)
      n2cS8 n2cT8 n2cChk8 n2cEnt8
  · exact n2c_rank_lower (by omega) n2cR11 n2cC11 (by decide) (by decide) (by decide)
      n2cS11 n2cT11 n2cChk11 n2cEnt11
  · exact n2c_rank_lower (by omega) n2cR14 n2cC14 (by decide) (by decide) (by decide)
      n2cS14 n2cT14 n2cChk14 n2cEnt14
  · exact n2c_rank_lower (by omega) n2cR18 n2cC18 (by decide) (by decide) (by decide)
      n2cS18 n2cT18 n2cChk18 n2cEnt18
  · exact n2c_rank_lower (by omega) n2cR21 n2cC21 (by decide) (by decide) (by decide)
      n2cS21 n2cT21 n2cChk21 n2cEnt21
  · exact n2c_rank_lower (by omega) n2cR13 n2cC13 (by decide) (by decide) (by decide)
      n2cS13 n2cT13 n2cChk13 n2cEnt13
  · exact n2c_rank_lower (by omega) n2cR17 n2cC17 (by decide) (by decide) (by decide)
      n2cS17 n2cT17 n2cChk17 n2cEnt17
  · exact n2c_rank_lower (by omega) n2cR20 n2cC20 (by decide) (by decide) (by decide)
      n2cS20 n2cT20 n2cChk20 n2cEnt20
  · exact n2c_rank_lower (by omega) n2cR22 n2cC22 (by decide) (by decide) (by decide)
      n2cS22 n2cT22 n2cChk22 n2cEnt22
  · exact n2c_rank_lower (by omega) n2cR10 n2cC10 (by decide) (by decide) (by decide)
      n2cS10 n2cT10 n2cChk10 n2cEnt10
  · exact n2c_rank_lower (by omega) n2cR19 n2cC19 (by decide) (by decide) (by decide)
      n2cS19 n2cT19 n2cChk19 n2cEnt19
  · exact n2c_rank_lower (by omega) n2cR9 n2cC9 (by decide) (by decide) (by decide)
      n2cS9 n2cT9 n2cChk9 n2cEnt9
  · exact n2c_rank_lower (by omega) n2cR23 n2cC23 (by decide) (by decide) (by decide)
      n2cS23 n2cT23 n2cChk23 n2cEnt23
  · exact n2c_rank_lower (by omega) n2cR24 n2cC24 (by decide) (by decide) (by decide)
      n2cS24 n2cT24 n2cChk24 n2cEnt24
  · exact n2c_rank_lower (by omega) n2cR15 n2cC15 (by decide) (by decide) (by decide)
      n2cS15 n2cT15 n2cChk15 n2cEnt15
  · exact n2c_rank_lower (by omega) n2cR7 n2cC7 (by decide) (by decide) (by decide)
      n2cS7 n2cT7 n2cChk7 n2cEnt7

end StaircasePort.Stair
