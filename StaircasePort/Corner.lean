/-
# N7 — the symbolic 39-position CORNER CLAUSE (corner runs (1,507,21) + (25,486,18))

The corner clause for the staircase projector `qMStair`: the 39 corner-run positions of
`stairDataRuns 23 529` are pivots of `qMStair (stairPairM x₁ y₁ x₂ y₂)` for ARBITRARY
labels under the hypotheses documented at `isPiv_stairCorner` (Projector.lean).

## Route (measured `n7_probe.py`, proved here; see SCAFFOLD.md "## CORNER NOTES")
Both runs go through N2c's four-rank method (`isPiv_of_bounds`); the r6
`isPiv_rank1_lower` route is structurally impossible for run 2 (below-diagonal band).
* Run 1 (l, 22+l), k = 1: cut-table uppers; lowers from the 2x2 minor whose determinant
  is exactly `hu·hv·dev_l` (entries `n7_E1..E4`) and the entry `corner[0][44] = hu·hv`.
* Run 2 (25+t, 2+t), k = 25: cut-table uppers; lowers from `hM1` (top-25 rows
  independent on cols ≥ 20; N2c cert 1 at the witness) and `hM2` (row 25+t independent
  on cols ≥ 2+t; N2c's 18 26-certificates at the witness — `CornerData.lean`).
`n7_rk_block`/`n7_isPiv_block` port `isPiv_block`
(nb_data_edge_solution.lean:227-238) via two submatrix-composition rank inequalities
(they live in `CornerData.lean` for build economy; so do the kernel-decided pins and
the witness discharges).

NOTE (2026-11-05): this block was first spliced into Pivot.lean (commit "N7 SPLICE") —
but under host load 75-140 every `lake build` was killed inside Pivot's long rebuild,
so the block moved to these NEW modules importing Pivot.
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.CornerData

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

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

lemma n7_mem_C1 : ∀ l : ℕ, 2 ≤ l → l ≤ 20 → (l - 1, 23 + l, 1, 1) ∈ stairNEBlocks := by
  intro l _ _; interval_cases l <;> decide

lemma n7_mem_D1 : ∀ l : ℕ, 1 ≤ l → l ≤ 20 → (l, 23 + l, 1, 1) ∈ stairNEBlocks := by
  intro l _ _; interval_cases l <;> decide

lemma n7_mem_A2 : ∀ t : ℕ, 1 ≤ t → t ≤ 17 → (24 + t, 2 + t, 25, 25) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide

lemma n7_mem_B2 : ∀ t : ℕ, 1 ≤ t → t ≤ 16 → (25 + t, 2 + t, 26, 26) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide

lemma n7_mem_C2 : ∀ t : ℕ, 1 ≤ t → t ≤ 16 → (24 + t, 3 + t, 25, 25) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide

lemma n7_mem_D2 : ∀ t : ℕ, 1 ≤ t → t ≤ 16 → (25 + t, 3 + t, 25, 25) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide

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

-- COMPOSE (2026-11-05): the dead `n7R26`/`n7C26` defs (leftovers of the ABANDONED
-- n7_rk_block/isPiv_block route, never referenced by any proof) are DELETED — they
-- referenced the never-defined `n7M2row`/`n7M2col` and broke the integration build.
-- The run-2 minor indices live in the N2c certificate lists (`n2cR12`.., Pivot.lean).

/-! #### run 1: the 21 above-diagonal positions (l, 22+l) -/

/-- **Run 1** of the corner clause: `IsPiv q l (22+l)` for `1 ≤ l ≤ 21`, from `hu`, `hv`
and the 21 diagonal-deviation nonvanishing facts. -/
lemma n7_run1 (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hu : x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ ≠ 0)
    (hv : y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ (n7Fin l) * y₂ (n7Fin (l + 1))
        + stairRunB l * x₁ (n7Fin l) * y₁ (n7Fin (l + 1)) ≠ 0) :
    ∀ l, 1 ≤ l → l ≤ 21 → IsPiv (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) l (22 + l) := by
  intro l hl1 hl2
  have hlt22 : l < 22 := by omega
  -- the four entries of the 2x2 lower-bound minor
  have e1 := n7_E1 x₁ y₁ x₂ y₂
  have e2 := n7_E2 l hlt22 x₁ y₁ x₂ y₂
  have e3 := n7_E3 l hl1 hlt22 x₁ y₁ x₂ y₂
  have e4 := n7_E4 l hl1 hlt22 x₁ y₁ x₂ y₂
  have hdev0 := hT l hl1 hl2
  have hnF : n7Fin l = (⟨l, by omega⟩ : Fin 23) := by
    refine Fin.ext ?_
    rw [n7Fin]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hnF] at hdev0
  have hdev := hdev0
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
    · rcases Nat.lt_or_ge l 21 with h' | h'
      · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ l (23 + l) 1 1 (by omega)
          (n7_mem_C1 l h (by omega))
        rwa [show l - 1 + 1 = l from by omega] at hb
      · exact (rk_le_width _ l (23 + l) (by omega)).trans (by omega)
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
    · rcases Nat.lt_or_ge t 17 with h' | h'
      · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (26 + t) (2 + t) 26 26 (by omega)
          (n7_mem_B2 t h (by omega))
        rwa [show 26 + t - 1 = 25 + t from by omega] at hb
      · exact (rk_le_width _ (26 + t) (2 + t) (by omega)).trans (by omega)
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
      stairRunA l * x₂ (n7Fin l) * y₂ (n7Fin (l + 1))
        + stairRunB l * x₁ (n7Fin l) * y₁ (n7Fin (l + 1)) ≠ 0)
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

end StaircasePort.Stair
