import StaircasePort.Pivot
import StaircasePort.Projector

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

/-! ### n7 part 1: list shapes and symbolic corner-entry lemmas -/

lemma n7_Lt_lt22 (l : ℕ) (hl : l < 22) :
    LtermsStair l = [(1, ((⟨l, by omega⟩, ⟨l, by omega⟩) : Pr 23))] := by
  simp only [LtermsStair, LtermsZStair, dif_pos hl, List.map_cons, List.map_nil,
    Int.cast_one]

lemma n7_Rt_44 :
    RtermsStair 44 = [(1, ((⟨22, by omega⟩, ⟨22, by omega⟩) : Pr 23))] := by
  have h1 : ¬((44 : ℕ) = 20) := by omega
  have h2 : ¬((44 : ℕ) = 21) := by omega
  have h3 : ¬((44 : ℕ) < 44) := by omega
  simp only [RtermsStair, RtermsZStair, dif_neg h1, dif_neg h2, dif_neg h3, dif_pos rfl,
    List.map_cons, List.map_nil, Int.cast_one]
  rfl

lemma n7_Rt_col (r : ℕ) (hr : r < 22) :
    RtermsStair (22 + r) =
      [(((stairAZL.getD r 0 : ℤ) : ℚ), ((⟨r, by omega⟩, ⟨r + 1, by omega⟩) : Pr 23)),
       (((stairBZL.getD r 0 : ℤ) : ℚ), ((⟨r + 1, by omega⟩, ⟨r, by omega⟩) : Pr 23))] := by
  have h1 : ¬((22 + r : ℕ) < 20) := by omega
  have h2 : ¬((22 + r : ℕ) = 20) := by omega
  have h3 : ¬((22 + r : ℕ) = 21) := by omega
  have h4 : (22 + r : ℕ) < 44 := by omega
  unfold RtermsStair RtermsZStair
  rw [dif_neg h1, if_neg h2, if_neg h3, dif_pos h4]
  simp only [show (22 + r) - 22 = (r : ℕ) from by omega,
    show (22 + r) - 21 = r + 1 from by omega, List.map_cons, List.map_nil]

/-- Row 0 (single anchor E(0,0)) × column 44 (single E(22,22)): the entry is `hu·hv`. -/
lemma n7_E1 (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    corStairQ (stairPairM x₁ y₁ x₂ y₂) 0 44
      = x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ * (y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩) := by
  simp only [corStairQ, n7_Rt_44, n7_Lt_lt22 0 (by omega), List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, stairPairM, Matrix.kroneckerMap_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.vecMulVec_apply, one_mul, mul_one, mul_neg, neg_mul, neg_neg]
  norm_num [↓reduceIte, Fin.isValue, Fin.mk.injEq]
  ring

/-- Row `l < 22` (single anchor E(l,l)) × column 44: `x₁ l · x₂ l · hv`. -/
lemma n7_E2 (l : ℕ) (hl : l < 22) (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    corStairQ (stairPairM x₁ y₁ x₂ y₂) l 44
      = x₁ ⟨l, by omega⟩ * x₂ ⟨l, by omega⟩ * (y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩) := by
  simp only [corStairQ, n7_Rt_44, n7_Lt_lt22 l hl, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, stairPairM, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, one_mul, mul_one, mul_neg, neg_mul, neg_neg]
  rw [if_neg (show ¬((⟨l, by omega⟩ : Fin 23) = ⟨22, by omega⟩) from by
    simp only [Fin.mk.injEq]; omega)]
  ring

/-- The two-term column coefficients (Nat-indexed to match the extracted data). -/
def stairRunA (r : ℕ) : ℚ := ((stairAZL.getD r 0 : ℤ) : ℚ)
def stairRunB (r : ℕ) : ℚ := ((stairBZL.getD r 0 : ℤ) : ℚ)

/-- Row 0 × column `22 + r` (`1 ≤ r < 22`): `u₀ · v_r`. -/
lemma n7_E3 (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r < 22) (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    corStairQ (stairPairM x₁ y₁ x₂ y₂) 0 (22 + r)
      = x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩
          * (stairRunA r * y₁ ⟨r, by omega⟩ * y₂ ⟨r + 1, by omega⟩
            + stairRunB r * y₁ ⟨r + 1, by omega⟩ * y₂ ⟨r, by omega⟩) := by
  simp only [corStairQ, n7_Rt_col r hr2, n7_Lt_lt22 0 (by omega), stairRunA, stairRunB,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, stairPairM,
    Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    one_mul, mul_one, mul_neg, neg_mul, neg_neg]
  rw [if_neg (show ¬((⟨0, by omega⟩ : Fin 23) = ⟨r, by omega⟩) from by
        simp only [Fin.mk.injEq]; omega),
    if_neg (show ¬((⟨0, by omega⟩ : Fin 23) = ⟨r + 1, by omega⟩) from by
        simp only [Fin.mk.injEq]; omega)]
  ring

/-- Row `l` × column `22 + l` (`1 ≤ l < 22`): the run-1 diagonal `u_l · v_l − dev_l`. -/
lemma n7_E4 (l : ℕ) (hl1 : 1 ≤ l) (hl2 : l < 22) (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    corStairQ (stairPairM x₁ y₁ x₂ y₂) l (22 + l)
      = (x₁ ⟨l, by omega⟩ * x₂ ⟨l, by omega⟩)
          * (stairRunA l * y₁ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
            + stairRunB l * y₁ ⟨l + 1, by omega⟩ * y₂ ⟨l, by omega⟩)
        - (stairRunA l * x₂ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
            + stairRunB l * x₁ ⟨l, by omega⟩ * y₁ ⟨l + 1, by omega⟩) := by
  simp only [corStairQ, n7_Rt_col l hl2, n7_Lt_lt22 l hl2, stairRunA, stairRunB, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, stairPairM, Matrix.kroneckerMap_apply,
    Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, one_mul, mul_one, mul_neg,
    neg_mul, neg_neg]
  rw [if_neg (show ¬((⟨l, by omega⟩ : Fin 23) = ⟨l + 1, by omega⟩) from by
    simp only [Fin.mk.injEq]; omega)]
  norm_num
  ring

/-! ### n7 part 2: the symbolic corner clause (four-rank route) -/

/-- N2b's cut bound, symbolically for the pair-matrix corner. -/
lemma rkQ_le_of_block_gen (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (X Y c r : ℕ) (hX : 1 ≤ X)
    (h : (X - 1, Y, r, c) ∈ stairNEBlocks) :
    rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) X Y ≤ c := by
  have hb := stairNE_rk_le x₁ y₁ x₂ y₂ (X - 1, Y, r, c) h
  rwa [Nat.sub_add_cancel hX] at hb

/-! #### cut-table membership pins (kernel-decided per interval case) -/

lemma n7_mem_A1 : ∀ l : ℕ, 2 ≤ l → l ≤ 21 → (l - 1, 22 + l, 1, 1) ∈ stairNEBlocks := by
  intro l _ _; interval_cases l <;> decide

lemma n7_mem_B1 : ∀ l : ℕ, 2 ≤ l → l ≤ 20 → (l, 22 + l, 2, 2) ∈ stairNEBlocks := by
  intro l _ _; interval_cases l <;> decide

lemma n7_mem_C1 : ∀ l : ℕ, 2 ≤ l → l ≤ 21 → (l - 1, 23 + l, 1, 1) ∈ stairNEBlocks := by
  intro l _ _; interval_cases l <;> decide

lemma n7_mem_D1 : ∀ l : ℕ, 1 ≤ l → l ≤ 20 → (l, 23 + l, 1, 1) ∈ stairNEBlocks := by
  intro l _ _; interval_cases l <;> decide

lemma n7_mem_A2 : ∀ t : ℕ, 1 ≤ t → t ≤ 17 → (24 + t, 2 + t, 25, 25) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide

lemma n7_mem_B2 : ∀ t : ℕ, 1 ≤ t → t ≤ 17 → (25 + t, 2 + t, 26, 26) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide

lemma n7_mem_C2 : ∀ t : ℕ, 1 ≤ t → t ≤ 16 → (24 + t, 3 + t, 25, 25) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide

lemma n7_mem_D2 : ∀ t : ℕ, 1 ≤ t → t ≤ 16 → (25 + t, 3 + t, 25, 25) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide

/-! #### the M1/M2 minor index functions -/

/-- hM1 minor: rows `0..24` × cols `20..44` of the corner (N2c certificate 1's shape). -/
def n7M1row (i : Fin 25) : Fin 45 := ⟨i.val, i.isLt⟩
def n7M1col (j : Fin 25) : Fin 45 := ⟨20 + j.val, by omega⟩

/-- hM2 minor: rows `0..24 ++ [25+t]` × cols `2+t .. 27+t` (N2c 26-certificates' shape). -/
def n7M2row (t : ℕ) (ht : t < 18) (i : Fin 26) : Fin 45 :=
  ⟨if i.val < 25 then i.val else 25 + t, by
    rcases Nat.lt_or_ge i.val 25 with h | h
    · omega
    · have := ht; omega⟩
def n7M2col (t : ℕ) (j : Fin 26) : Fin 45 := ⟨2 + t + j.val, by omega⟩

/-- run-1 hBlo minor rows: `0` and `l`. -/
def n7R2 (l : ℕ) (hl : l < 45) : Fin 2 → {r : Fin 45 // r.val < l + 1} := fun i =>
  ⟨⟨if i.val = 0 then 0 else l, by have := i.isLt; split <;> omega⟩, by
    have := i.isLt; split <;> omega⟩
/-- run-1 hBlo minor cols: `22+l` and `44`. -/
def n7C2 (l : ℕ) (hl : l ≤ 21) : Fin 2 → {c : Fin 45 // 22 + l ≤ c.val} := fun i =>
  ⟨⟨if i.val = 0 then 22 + l else 44, by have := i.isLt; split <;> omega⟩, by
    have := i.isLt; split <;> omega⟩

/-- run-1 hClo minor: the single entry `(0, 44)`. -/
def n7R1 (l : ℕ) : Fin 1 → {r : Fin 45 // r.val < l} := fun _ => ⟨⟨0, by omega⟩, by omega⟩
def n7C1 (l : ℕ) (hl : l ≤ 21) : Fin 1 → {c : Fin 45 // 23 + l ≤ c.val} := fun _ =>
  ⟨⟨44, by omega⟩, by omega⟩

/-- run-2 hBlo minor rows: `0..24 ++ [25+t]`. -/
def n7R26 (t : ℕ) (ht : t < 18) : Fin 26 → {r : Fin 45 // r.val < 26 + t} := fun i =>
  ⟨n7M2row t ht i, by
    rcases Nat.lt_or_ge i.val 25 with h | h
    · omega
    · have := ht; omega⟩
/-- run-2 hBlo minor cols: `2+t .. 27+t`. -/
def n7C26 (t : ℕ) : Fin 26 → {c : Fin 45 // 2 + t ≤ c.val} := fun j =>
  ⟨n7M2col t j, by omega⟩

/-! #### run 1: the 21 above-diagonal positions (l, 22+l) -/

/-- **Run 1** of the corner clause: `IsPiv q l (22+l)` for `1 ≤ l ≤ 21`, from `hu`, `hv`
and the 21 diagonal-deviation nonvanishing facts. -/
lemma n7_run1 (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hu : x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ ≠ 0)
    (hv : y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
        + stairRunB l * x₁ ⟨l, by omega⟩ * y₁ ⟨l + 1, by omega⟩ ≠ 0) :
    ∀ l, 1 ≤ l → l ≤ 21 → IsPiv (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) l (22 + l) := by
  intro l hl1 hl2
  have hlt22 : l < 22 := by omega
  -- the four entries of the 2x2 lower-bound minor
  have e1 := n7_E1 x₁ y₁ x₂ y₂
  have e2 := n7_E2 l hlt22 x₁ y₁ x₂ y₂
  have e3 := n7_E3 l hl1 hlt22 x₁ y₁ x₂ y₂
  have e4 := n7_E4 l hl1 hlt22 x₁ y₁ x₂ y₂
  have hdev := hT l hl1 hl2
  refine isPiv_of_bounds (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) l (22 + l) 1 ?_ ?_ ?_ ?_ ?_ ?_
  · -- A ≤ 1
    rcases Nat.lt_or_ge l 2 with h | h
    · exact (rk_le_height _ l (22 + l)).trans (by omega)
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ l (22 + l) 1 1 (by omega) (n7_mem_A1 l h hl2)
      rwa [show l - 1 + 1 = l from by omega] at hb
  · -- B ≤ 2
    rcases Nat.lt_or_ge l 2 with h | h
    · exact (rk_le_height _ (l + 1) (22 + l)).trans (by omega)
    · rcases Nat.lt_or_ge l 21 with h' | h'
      · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (l + 1) (22 + l) 2 2 (by omega)
          (n7_mem_B1 l h (by omega))
        rwa [show l + 1 - 1 = l from by omega] at hb
      · exact (rk_le_width _ (l + 1) (22 + l) (by omega)).trans (by omega)
  · -- C ≤ 1
    rcases Nat.lt_or_ge l 2 with h | h
    · exact (rk_le_height _ l (23 + l)).trans (by omega)
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ l (23 + l) 1 1 (by omega) (n7_mem_C1 l h hl2)
      rwa [show l - 1 + 1 = l from by omega] at hb
  · -- D ≤ 1
    rcases Nat.lt_or_ge l 21 with h | h
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (l + 1) (23 + l) 1 1 (by omega)
        (n7_mem_D1 l hl1 h)
      rwa [show l + 1 - 1 = l from by omega] at hb
    · exact (rk_le_width _ (l + 1) (23 + l) (by omega)).trans (by omega)
  · -- B ≥ 2: the 2x2 minor rows {0, l} × cols {22+l, 44}, det = hu·hv·dev_l
    refine rk_ge_of_det _ (l + 1) (22 + l) (n7R2 l (by omega)) (n7C2 l hl2) ?_
    have hdet : (Matrix.of fun i j : Fin 2 =>
          stairCornerQOf (stairPairM x₁ y₁ x₂ y₂) (n7R2 l (by omega) i).1
            (n7C2 l hl2 j).1).det
        = (x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩) * (y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩)
          * (stairRunA l * x₂ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
            + stairRunB l * x₁ ⟨l, by omega⟩ * y₁ ⟨l + 1, by omega⟩) := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, e1, e2, e3, e4]
      ring
    rw [hdet]
    exact mul_ne_zero (mul_ne_zero hu hv) hdev
  · -- C ≥ 1: the entry (0,44) = hu·hv
    refine rk_ge_of_det _ l (23 + l) (n7R1 l) (n7C1 l hl2) ?_
    rw [Matrix.det_fin_one]
    simp only [Matrix.of_apply, e1]
    exact hu

/-! #### witness discharges (all hypotheses hold at the extracted witness) -/

/-- hT at the witness: the 21 run-1 diagonal deviations are nonzero. -/
theorem n7_hT_witness : ∀ l : ℕ, 1 ≤ l → l ≤ 21 →
    stairRunA l * stairQX2 ⟨l, by omega⟩ * stairQY2 ⟨l + 1, by omega⟩
      + stairRunB l * stairQX1 ⟨l, by omega⟩ * stairQY1 ⟨l + 1, by omega⟩ ≠ 0 := by
  intro l h1 h2
  interval_cases l <;>
    simp only [stairRunA, stairRunB, stairQX1, stairQX2, stairQY1, stairQY2, stairWX1L,
      stairWX2L, stairWY1L, stairWY2L, stairAZL, stairBZL, List.getD, List.getD_cons,
      List.getD_nil, Int.cast_ofNat, Int.cast_one, Int.cast_neg] <;>
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

/-- **The 39 corner positions at the witness, through the symbolic clause** — all five
hypotheses of `isPiv_stairCorner_rk` discharged (integration check of the witness chain;
the corner coordinates here match the global runs (1,507,21) and (25,486,18) shifted by
484 = 23*23 - 45). -/
theorem isPiv_stairCorner_rk_witness :
    ∀ p ∈ runPairs [(1, 23, 21), (25, 2, 18)], IsPiv stairCornerQ p.1 p.2 :=
  isPiv_stairCorner_rk stairQX1 stairQY1 stairQX2 stairQY2 stair_hu stair_hv n7_hT_witness
    n7_hM1_witness n7_hM2_witness

/-! #### block transfer -/

/-- NE-block ranks transfer through a top-left block reindexing: `B` is `C`'s rows
`0..a'-1` and cols `c0..c0+b'-1`, so the NE blocks agree and so do the ranks. -/
lemma n7_rk_block {a b a' b' c0 X Y : ℕ} (C : Matrix (Fin a) (Fin b) ℚ)
    (B : Matrix (Fin a') (Fin b') ℚ) (ha : a' ≤ a) (hb : c0 + b' = b) (hX : X ≤ a')
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C (⟨i.val, by have := i.isLt; omega⟩ : Fin a)
        (⟨c0 + j.val, by have := j.isLt; omega⟩ : Fin b)) :
    rk C X (c0 + Y) = rk B X Y := by
  rw [rk, rk]
  have hSB : (B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
        (fun c : {c : Fin b' // Y ≤ c.val} => c.1)
      = (C.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // c0 + Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a' // r.val < X} =>
          (⟨⟨r.1.val, by have := r.2; omega⟩, r.2⟩ : {r : Fin a // r.val < X}))
        (fun c : {c : Fin b' // Y ≤ c.val} =>
          (⟨⟨c0 + c.1.val, by have := c.1.isLt; omega⟩,
            by have := c.1.isLt; have := c.2; omega⟩ :
            {c : Fin b // c0 + Y ≤ c.val})) := by
    ext r c
    simp only [Matrix.submatrix_apply]
    exact hCB r.1 c.1
  have hSC : ((C.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // c0 + Y ≤ c.val} => c.1))
      = (B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
        (fun c : {c : Fin b' // Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a // r.val < X} =>
          (⟨⟨r.1.val, by have := r.2; omega⟩, by have := r.2; omega⟩ :
            {r : Fin a' // r.val < X}))
        (fun c : {c : Fin b // c0 + Y ≤ c.val} =>
          (⟨⟨c.1.val - c0, by have := c.2; have := c.1.isLt; omega⟩,
            by have := c.2; have := c.1.isLt; omega⟩ :
            {c : Fin b' // Y ≤ c.val})) := by
    ext r c
    simp only [Matrix.submatrix_apply]
    rw [← hCB (⟨⟨r.1.val, by have := r.2; omega⟩, by have := r.2; omega⟩ : Fin a')
      (⟨⟨c.1.val - c0, by have := c.2; have := c.1.isLt; omega⟩,
        by have := c.2; have := c.1.isLt; omega⟩ : Fin b')]
    congr 1
    exact Fin.ext (by have := c.2; have := c.1.isLt; omega)
  exact le_antisymm
    (by rw [hSC]; exact Matrix.rank_submatrix_le _ _)
    (by rw [hSB]; exact Matrix.rank_submatrix_le _ _)

/-- **`isPiv_block` (ported from nb_data_edge_solution.lean:227-238)**: a pivot of the
top-left block `B` is a pivot of `C` at the shifted column. -/
lemma n7_isPiv_block {a b a' b' c0 : ℕ} (C : Matrix (Fin a) (Fin b) ℚ)
    (B : Matrix (Fin a') (Fin b') ℚ) (ha : a' ≤ a) (hb : c0 + b' = b)
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C (⟨i.val, by have := i.isLt; omega⟩ : Fin a)
        (⟨c0 + j.val, by have := j.isLt; omega⟩ : Fin b))
    {i j : ℕ} (hi : i < a') (h : IsPiv B i j) : IsPiv C i (c0 + j) := by
  unfold IsPiv at h ⊢
  rw [show c0 + j + 1 = c0 + (j + 1) from by omega,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB]
  exact h

end StaircasePort.Stair



/-! #### run 2: the 18 below-diagonal positions (25+t, 2+t) -/

/-- **Run 2** of the corner clause: `IsPiv q (25+t) (2+t)` for `t < 18`, from the two
lower-bound hypotheses `hM1` (the top 25 rows are independent on cols >= 20: at the
witness N2c certificate 1) and `hM2` (row `25+t` is independent on cols >= `2+t`: at the
witness N2c's 26-certificates); the upper bounds are the unconditional cut table. -/
lemma n7_run2 (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hM1 : 25 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) 25 20)
    (hM2 : ∀ t : ℕ, t < 18 →
      26 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (26 + t) (2 + t)) :
    ∀ t, t < 18 → IsPiv (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (25 + t) (2 + t) := by
  intro t ht
  have hle : t ≤ 17 := by omega
  refine isPiv_of_bounds (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (25 + t) (2 + t) 25
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- A ≤ 25
    rcases Nat.lt_or_ge t 1 with h | h
    · exact rk_le_height _ (25 + t) (2 + t)
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (25 + t) (2 + t) 25 25 (by omega)
        (n7_mem_A2 t h hle)
      rwa [show 25 + t - 1 = 24 + t from by omega] at hb
  · -- B ≤ 26
    rcases Nat.lt_or_ge t 1 with h | h
    · exact rk_le_height _ (26 + t) (2 + t)
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (26 + t) (2 + t) 26 26 (by omega)
        (n7_mem_B2 t h hle)
      rwa [show 26 + t - 1 = 25 + t from by omega] at hb
  · -- C ≤ 25
    rcases Nat.lt_or_ge t 1 with h | h
    · exact rk_le_height _ (25 + t) (3 + t)
    · rcases Nat.lt_or_ge t 17 with h' | h'
      · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (25 + t) (3 + t) 25 25 (by omega)
          (n7_mem_C2 t h (by omega))
        rwa [show 25 + t - 1 = 24 + t from by omega] at hb
      · exact (rk_le_width _ (25 + t) (3 + t) (by omega)).trans (by omega)
  · -- D ≤ 25
    rcases Nat.lt_or_ge t 17 with h | h
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (26 + t) (3 + t) 25 25 (by omega)
        (n7_mem_D2 t (by omega) h)
      rwa [show 26 + t - 1 = 25 + t from by omega] at hb
    · exact (rk_le_width _ (26 + t) (3 + t) (by omega)).trans (by omega)
  · -- B >= 26
    exact hM2 t ht
  · -- C >= 25: hM1 + monotonicity (rows 25 <= 25+t, cols 3+t <= 20)
    exact hM1.trans ((rk_rows_mono _ (by omega)).trans (rk_cols_mono _ (by omega)))

/-! #### the corner-level clause -/

/-- **N7 — the symbolic 39-position CORNER CLAUSE** (corner coordinates).

For arbitrary labels, the 39 run positions of the two staircase corner runs are pivots of
the pair-matrix corner, given: `hu`, `hv`, the 21 run-1 diagonal deviations, and the two
independence hypotheses `hM1`/`hM2`. Note `h₁`/`h₂` (`y·x = 1`) and `hdet` are NOT needed
for the corner clause (they are the middle-run's fuel, `isPiv_stairMid`). -/
theorem isPiv_stairCorner_rk (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hu : x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ ≠ 0)
    (hv : y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
        + stairRunB l * x₁ ⟨l, by omega⟩ * y₁ ⟨l + 1, by omega⟩ ≠ 0)
    (hM1 : 25 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) 25 20)
    (hM2 : ∀ t : ℕ, t < 18 →
      26 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (26 + t) (2 + t)) :
    ∀ p ∈ runPairs [(1, 23, 21), (25, 2, 18)],
      IsPiv (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) p.1 p.2 := by
  intro p hp
  rw [runPairs, List.mem_flatMap] at hp
  obtain ⟨ρ, hρ, hp2⟩ := hp
  obtain ⟨i, j, r⟩ := ρ
  rw [List.mem_cons, List.mem_cons, List.mem_nil] at hρ
  rcases hρ with rfl | rfl | hr
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    rw [show 23 + k = 22 + (1 + k) from by omega]
    exact n7_run1 x₁ y₁ x₂ y₂ hu hv hT (1 + k) (by omega) (by omega)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    exact n7_run2 x₁ y₁ x₂ y₂ hM1 hM2 k hk
  · exact absurd hr (by simp)

/-! #### witness discharges (all hypotheses hold at the extracted witness) -/

/-- hT at the witness: the 21 run-1 diagonal deviations are nonzero. -/
theorem n7_hT_witness : ∀ l : ℕ, 1 ≤ l → l ≤ 21 →
    stairRunA l * stairQX2 ⟨l, by omega⟩ * stairQY2 ⟨l + 1, by omega⟩
      + stairRunB l * stairQX1 ⟨l, by omega⟩ * stairQY1 ⟨l + 1, by omega⟩ ≠ 0 := by
  intro l h1 h2
  interval_cases l <;>
    simp only [stairRunA, stairRunB, stairQX1, stairQX2, stairQY1, stairQY2, stairWX1L,
      stairWX2L, stairWY1L, stairWY2L, stairAZL, stairBZL, List.getD, List.getD_cons,
      List.getD_nil, Int.cast_ofNat, Int.cast_one, Int.cast_neg] <;>
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

/-- **The 39 corner positions at the witness, through the symbolic clause** — all five
hypotheses of `isPiv_stairCorner_rk` discharged (integration check of the witness chain;
the corner coordinates here match the global runs (1,507,21) and (25,486,18) shifted by
484 = 23*23 - 45). -/
theorem isPiv_stairCorner_rk_witness :
    ∀ p ∈ runPairs [(1, 23, 21), (25, 2, 18)], IsPiv stairCornerQ p.1 p.2 :=
  isPiv_stairCorner_rk stairQX1 stairQY1 stairQX2 stairQY2 stair_hu stair_hv n7_hT_witness
    n7_hM1_witness n7_hM2_witness

/-! #### block transfer -/

/-- NE-block ranks transfer through a top-left block reindexing: `B` is `C`'s rows
`0..a'-1` and cols `c0..c0+b'-1`, so the NE blocks agree and so do the ranks. -/
lemma n7_rk_block {a b a' b' c0 X Y : ℕ} (C : Matrix (Fin a) (Fin b) ℚ)
    (B : Matrix (Fin a') (Fin b') ℚ) (ha : a' ≤ a) (hb : c0 + b' = b) (hX : X ≤ a')
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C (⟨i.val, by have := i.isLt; omega⟩ : Fin a)
        (⟨c0 + j.val, by have := j.isLt; omega⟩ : Fin b)) :
    rk C X (c0 + Y) = rk B X Y := by
  rw [rk, rk]
  have hSB : (B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
        (fun c : {c : Fin b' // Y ≤ c.val} => c.1)
      = (C.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // c0 + Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a' // r.val < X} =>
          (⟨⟨r.1.val, by have := r.2; omega⟩, r.2⟩ : {r : Fin a // r.val < X}))
        (fun c : {c : Fin b' // Y ≤ c.val} =>
          (⟨⟨c0 + c.1.val, by have := c.1.isLt; omega⟩,
            by have := c.1.isLt; have := c.2; omega⟩ :
            {c : Fin b // c0 + Y ≤ c.val})) := by
    ext r c
    simp only [Matrix.submatrix_apply]
    exact hCB r.1 c.1
  have hSC : ((C.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // c0 + Y ≤ c.val} => c.1))
      = (B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
        (fun c : {c : Fin b' // Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a // r.val < X} =>
          (⟨⟨r.1.val, by have := r.2; omega⟩, by have := r.2; omega⟩ :
            {r : Fin a' // r.val < X}))
        (fun c : {c : Fin b // c0 + Y ≤ c.val} =>
          (⟨⟨c.1.val - c0, by have := c.2; have := c.1.isLt; omega⟩,
            by have := c.2; have := c.1.isLt; omega⟩ :
            {c : Fin b' // Y ≤ c.val})) := by
    ext r c
    simp only [Matrix.submatrix_apply]
    rw [← hCB (⟨⟨r.1.val, by have := r.2; omega⟩, by have := r.2; omega⟩ : Fin a')
      (⟨⟨c.1.val - c0, by have := c.2; have := c.1.isLt; omega⟩,
        by have := c.2; have := c.1.isLt; omega⟩ : Fin b')]
    congr 1
    exact Fin.ext (by have := c.2; have := c.1.isLt; omega)
  exact le_antisymm
    (by rw [hSC]; exact Matrix.rank_submatrix_le _ _)
    (by rw [hSB]; exact Matrix.rank_submatrix_le _ _)

/-- **`isPiv_block` (ported from nb_data_edge_solution.lean:227-238)**: a pivot of the
top-left block `B` is a pivot of `C` at the shifted column. -/
lemma n7_isPiv_block {a b a' b' c0 : ℕ} (C : Matrix (Fin a) (Fin b) ℚ)
    (B : Matrix (Fin a') (Fin b') ℚ) (ha : a' ≤ a) (hb : c0 + b' = b)
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C (⟨i.val, by have := i.isLt; omega⟩ : Fin a)
        (⟨c0 + j.val, by have := j.isLt; omega⟩ : Fin b))
    {i j : ℕ} (hi : i < a') (h : IsPiv B i j) : IsPiv C i (c0 + j) := by
  unfold IsPiv at h ⊢
  rw [show c0 + j + 1 = c0 + (j + 1) from by omega,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB]
  exact h

end StaircasePort.Stair



/-! #### run 2: the 18 below-diagonal positions (25+t, 2+t) -/

/-- **Run 2** of the corner clause: `IsPiv q (25+t) (2+t)` for `t < 18`, from the two
minor hypotheses `hM1` (top-right 25x25) and `hM2` (the 18 26x26 minors). -/
lemma n7_run2 (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hM1 : (Matrix.of fun i j : Fin 25 =>
        stairCornerQOf (stairPairM x₁ y₁ x₂ y₂) (n7M1row i) (n7M1col j)).det ≠ 0)
    (hM2 : ∀ t : ℕ, t < 18 → (Matrix.of fun i j : Fin 26 =>
        stairCornerQOf (stairPairM x₁ y₁ x₂ y₂) (n7M2row t ‹t < 18› i) (n7M2col t j)).det ≠ 0) :
    ∀ t, t < 18 → IsPiv (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (25 + t) (2 + t) := by
  intro t ht
  have hle : t ≤ 17 := by omega
  refine isPiv_of_bounds (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (25 + t) (2 + t) 25
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- A ≤ 25
    rcases Nat.lt_or_ge t 1 with h | h
    · exact rk_le_height _ (25 + t) (2 + t)
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (25 + t) (2 + t) 25 25 (by omega)
        (n7_mem_A2 t h hle)
      rwa [show 25 + t - 1 = 24 + t from by omega] at hb
  · -- B ≤ 26
    rcases Nat.lt_or_ge t 1 with h | h
    · exact rk_le_height _ (26 + t) (2 + t)
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (26 + t) (2 + t) 26 26 (by omega)
        (n7_mem_B2 t h hle)
      rwa [show 26 + t - 1 = 25 + t from by omega] at hb
  · -- C ≤ 25
    rcases Nat.lt_or_ge t 1 with h | h
    · exact rk_le_height _ (25 + t) (3 + t)
    · rcases Nat.lt_or_ge t 17 with h' | h'
      · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (25 + t) (3 + t) 25 25 (by omega)
          (n7_mem_C2 t h (by omega))
        rwa [show 25 + t - 1 = 24 + t from by omega] at hb
      · exact (rk_le_width _ (25 + t) (3 + t) (by omega)).trans (by omega)
  · -- D ≤ 25
    rcases Nat.lt_or_ge t 17 with h | h
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (26 + t) (3 + t) 25 25 (by omega)
        (n7_mem_D2 t (by omega) h)
      rwa [show 26 + t - 1 = 25 + t from by omega] at hb
    · exact (rk_le_width _ (26 + t) (3 + t) (by omega)).trans (by omega)
  · -- B ≥ 26: the 26x26 minor rows 0..24 ++ [25+t] × cols 2+t..27+t
    refine rk_ge_of_det _ (26 + t) (2 + t) (n7R26 t ht) (n7C26 t) ?_
    exact hM2 t ht
  · -- C ≥ 25: hM1's 25x25 minor + monotonicity
    have h1 := rk_ge_of_det (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) 25 20
      (fun i : Fin 25 => ⟨n7M1row i, i.isLt⟩) (fun j : Fin 25 => ⟨n7M1col j, by omega⟩) hM1
    exact h1.trans ((rk_rows_mono _ (by omega)).trans (rk_cols_mono _ (by omega)))

/-! #### the corner-level clause -/

/-- **N7 — the symbolic 39-position CORNER CLAUSE** (corner coordinates).

For arbitrary labels, the 39 run positions of the two staircase corner runs are pivots of
the pair-matrix corner, given: `hu`, `hv`, the 21 run-1 diagonal deviations, the
top-right 25x25 minor `hM1`, and the 18 minors `hM2` (all dischargeable at the extracted
witness by N2c's certificates). -/
theorem isPiv_stairCorner_rk (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hu : x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ ≠ 0)
    (hv : y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
        + stairRunB l * x₁ ⟨l, by omega⟩ * y₁ ⟨l + 1, by omega⟩ ≠ 0)
    (hM1 : (Matrix.of fun i j : Fin 25 =>
        stairCornerQOf (stairPairM x₁ y₁ x₂ y₂) (n7M1row i) (n7M1col j)).det ≠ 0)
    (hM2 : ∀ t : ℕ, t < 18 → (Matrix.of fun i j : Fin 26 =>
        stairCornerQOf (stairPairM x₁ y₁ x₂ y₂) (n7M2row t ‹t < 18› i) (n7M2col t j)).det ≠ 0) :
    ∀ p ∈ runPairs [(1, 23, 21), (25, 2, 18)],
      IsPiv (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) p.1 p.2 := by
  intro p hp
  rw [runPairs, List.mem_flatMap] at hp
  obtain ⟨ρ, hρ, hp2⟩ := hp
  obtain ⟨i, j, r⟩ := ρ
  rw [List.mem_cons, List.mem_cons, List.mem_nil] at hρ
  rcases hρ with rfl | rfl | hr
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    rw [show 23 + k = 22 + (1 + k) from by omega]
    exact n7_run1 x₁ y₁ x₂ y₂ hu hv hT (1 + k) (by omega) (by omega)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    exact n7_run2 x₁ y₁ x₂ y₂ hM1 hM2 k hk
  · exact absurd hr (by simp)

/-! #### witness discharges (all hypotheses hold at the extracted witness) -/

/-- hT at the witness: the 21 run-1 diagonal deviations are nonzero. -/
theorem n7_hT_witness : ∀ l : ℕ, 1 ≤ l → l ≤ 21 →
    stairRunA l * stairQX2 ⟨l, by omega⟩ * stairQY2 ⟨l + 1, by omega⟩
      + stairRunB l * stairQX1 ⟨l, by omega⟩ * stairQY1 ⟨l + 1, by omega⟩ ≠ 0 := by
  intro l h1 h2
  interval_cases l <;>
    simp only [stairRunA, stairRunB, stairQX1, stairQX2, stairQY1, stairQY2, stairWX1L,
      stairWX2L, stairWY1L, stairWY2L, stairAZL, stairBZL, List.getD, List.getD_cons,
      List.getD_nil, Int.cast_ofNat, Int.cast_one, Int.cast_neg] <;>
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

/-- **The 39 corner positions at the witness, through the symbolic clause** — all five
hypotheses of `isPiv_stairCorner_rk` discharged (integration check of the witness chain;
the corner coordinates here match the global runs (1,507,21) and (25,486,18) shifted by
484 = 23*23 - 45). -/
theorem isPiv_stairCorner_rk_witness :
    ∀ p ∈ runPairs [(1, 23, 21), (25, 2, 18)], IsPiv stairCornerQ p.1 p.2 :=
  isPiv_stairCorner_rk stairQX1 stairQY1 stairQX2 stairQY2 stair_hu stair_hv n7_hT_witness
    n7_hM1_witness n7_hM2_witness

/-! #### block transfer -/

/-- NE-block ranks transfer through a top-left block reindexing: `B` is `C`'s rows
`0..a'-1` and cols `c0..c0+b'-1`, so the NE blocks agree and so do the ranks. -/
lemma n7_rk_block {a b a' b' c0 X Y : ℕ} (C : Matrix (Fin a) (Fin b) ℚ)
    (B : Matrix (Fin a') (Fin b') ℚ) (ha : a' ≤ a) (hb : c0 + b' = b) (hX : X ≤ a')
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C (⟨i.val, by have := i.isLt; omega⟩ : Fin a)
        (⟨c0 + j.val, by have := j.isLt; omega⟩ : Fin b)) :
    rk C X (c0 + Y) = rk B X Y := by
  rw [rk, rk]
  have hSB : (B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
        (fun c : {c : Fin b' // Y ≤ c.val} => c.1)
      = (C.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // c0 + Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a' // r.val < X} =>
          (⟨⟨r.1.val, by have := r.2; omega⟩, r.2⟩ : {r : Fin a // r.val < X}))
        (fun c : {c : Fin b' // Y ≤ c.val} =>
          (⟨⟨c0 + c.1.val, by have := c.1.isLt; omega⟩,
            by have := c.1.isLt; have := c.2; omega⟩ :
            {c : Fin b // c0 + Y ≤ c.val})) := by
    ext r c
    simp only [Matrix.submatrix_apply]
    exact hCB r.1 c.1
  have hSC : ((C.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // c0 + Y ≤ c.val} => c.1))
      = (B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
        (fun c : {c : Fin b' // Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a // r.val < X} =>
          (⟨⟨r.1.val, by have := r.2; omega⟩, by have := r.2; omega⟩ :
            {r : Fin a' // r.val < X}))
        (fun c : {c : Fin b // c0 + Y ≤ c.val} =>
          (⟨⟨c.1.val - c0, by have := c.2; have := c.1.isLt; omega⟩,
            by have := c.2; have := c.1.isLt; omega⟩ :
            {c : Fin b' // Y ≤ c.val})) := by
    ext r c
    simp only [Matrix.submatrix_apply]
    rw [← hCB (⟨⟨r.1.val, by have := r.2; omega⟩, by have := r.2; omega⟩ : Fin a')
      (⟨⟨c.1.val - c0, by have := c.2; have := c.1.isLt; omega⟩,
        by have := c.2; have := c.1.isLt; omega⟩ : Fin b')]
    congr 1
    exact Fin.ext (by have := c.2; have := c.1.isLt; omega)
  exact le_antisymm
    (by rw [hSC]; exact Matrix.rank_submatrix_le _ _)
    (by rw [hSB]; exact Matrix.rank_submatrix_le _ _)

/-- **`isPiv_block` (ported from nb_data_edge_solution.lean:227-238)**: a pivot of the
top-left block `B` is a pivot of `C` at the shifted column. -/
lemma n7_isPiv_block {a b a' b' c0 : ℕ} (C : Matrix (Fin a) (Fin b) ℚ)
    (B : Matrix (Fin a') (Fin b') ℚ) (ha : a' ≤ a) (hb : c0 + b' = b)
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C (⟨i.val, by have := i.isLt; omega⟩ : Fin a)
        (⟨c0 + j.val, by have := j.isLt; omega⟩ : Fin b))
    {i j : ℕ} (hi : i < a') (h : IsPiv B i j) : IsPiv C i (c0 + j) := by
  unfold IsPiv at h ⊢
  rw [show c0 + j + 1 = c0 + (j + 1) from by omega,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB]
  exact h

end StaircasePort.Stair



/-! #### the projector-level clause (N7 rewire contract) -/

namespace StaircasePort.Stair

/-- **N7 — `isPiv_stairCorner`: the 39-position CORNER CLAUSE on the staircase
projector** (the statement the N7 rewire consumes; global coordinates, corner runs
(1,507,21) and (25,486,18) of `stairDataRuns 23 529`).

Hypotheses (all dischargeable at the extracted witness — see
`isPiv_stairCorner_witness`): `hu`, `hv`, the 21 run-1 diagonal deviations `hT`,
`hM1` (top 25 corner rows independent on cols >= 20; witness: N2c cert 1), and `hM2`
(row `25+t` independent on cols >= `2+t` for `t < 18`; witness: N2c's 26-certs).
Note: `h₁`/`h₂` (`y·x = 1`) and `hdet` are NOT needed here — they are the middle-run's
fuel (`isPiv_stairMid`). -/
theorem isPiv_stairCorner (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hu : x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ ≠ 0)
    (hv : y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ ⟨l, by omega⟩ * y₂ ⟨l + 1, by omega⟩
        + stairRunB l * x₁ ⟨l, by omega⟩ * y₁ ⟨l + 1, by omega⟩ ≠ 0)
    (hM1 : 25 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) 25 20)
    (hM2 : ∀ t : ℕ, t < 18 →
      26 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (26 + t) (2 + t)) :
    ∀ p ∈ runPairs [(1, 507, 21), (25, 486, 18)],
      IsPiv (qMStair (stairPairM x₁ y₁ x₂ y₂)) p.1 p.2 := by
  intro p hp
  rw [runPairs, List.mem_flatMap] at hp
  obtain ⟨ρ, hρ, hp2⟩ := hp
  obtain ⟨i, j, r⟩ := ρ
  rw [List.mem_cons, List.mem_cons, List.mem_nil] at hρ
  rcases hρ with rfl | rfl | hr
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    refine n7_isPiv_block _ _ (by omega) (by omega) (fun l m => ?_) ?_ (by omega)
    · rw [show (484 : ℕ) + m.val = 529 - 45 + m.val from by omega]
      exact qMStair_corner (stairPairM x₁ y₁ x₂ y₂) l.val m.val l.isLt m.isLt
    · rw [show 23 + k = 22 + (1 + k) from by omega]
      exact n7_run1 x₁ y₁ x₂ y₂ hu hv hT (1 + k) (by omega) (by omega)
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    refine n7_isPiv_block _ _ (by omega) (by omega) (fun l m => ?_) ?_ (by omega)
    · rw [show (484 : ℕ) + m.val = 529 - 45 + m.val from by omega]
      exact qMStair_corner (stairPairM x₁ y₁ x₂ y₂) l.val m.val l.isLt m.isLt
    · exact n7_run2 x₁ y₁ x₂ y₂ hM1 hM2 k hk
  · exact absurd hr (by simp)

/-- **The 39 corner positions at the witness through the symbolic clause** — every
hypothesis discharged; the integration check for the N7 rewire. -/
theorem isPiv_stairCorner_witness :
    ∀ p ∈ runPairs [(1, 507, 21), (25, 486, 18)],
      IsPiv (qMStair (stairPairM stairQX1 stairQY1 stairQX2 stairQY2)) p.1 p.2 :=
  isPiv_stairCorner stairQX1 stairQY1 stairQX2 stairQY2 stair_hu stair_hv n7_hT_witness
    n7_hM1_witness n7_hM2_witness

end StaircasePort.Stair
