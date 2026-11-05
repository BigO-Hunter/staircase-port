/-
# N4 — hu/hv/hT analogues + flag-diagonal nonvanishing (check_stair item 1)

check_stair.py item 1 (docstring :7-10, flag_factors :110-135): the sparse staircase flag
family members satisfy all trace conditions, and "the flag diagonal factors f1..f4 are
nonzero on every line at the point (U,V of point(h,1)) and the inner corners of the
rank-(h−1) data classes are nonzero" — run output on this machine (2026-11-04, REPORT.md
§4): `f1..f4 zeros 0 over 1771 lines × 23 rows; inner-corner zeros 0`, with the `--control`
negative control discriminating.

Line parameterization here is the EXPLICIT `--ij` basis U = V = I + J (check_stair.py:157;
extract verified the --ij run certifies with the identical pivot pattern,
staircase_data.json ij_control). With U = V = I + J:
  a = Vᵀ·tv = tv + 3·1,  c = Uᵀ·tv = tv + 3·1,
  b = Vi·g = g + 7/72·1, d = Ui·g = g + 7/72·1,  g = (tv − 1/3)/2
(check_stair.py:129-131; (I+J)⁻¹ = I − J/24 over ℚ, Σg = −7/3 at |t| = 3.)
The f1..f4 evaluations follow check_stair.py:126-133 with the staircase family rows/cols
(Rrow/Rcol diagonals and columns, Crow/Ccol of μ_j = a_j E(j,j+1) + b_j E(j+1,j)).

The hu/hv/hT analogues at the LABEL level mirror data_edge_sol_aux's hyps
(nb_data_edge_solution.lean:505-511: hu x₁₀·x₂₀ ≠ 0, hv y₁₍ₕ₊₃₎·y₂₍ₕ₊₃₎ ≠ 0, hT over
l ∈ [1, h+2]) at the extracted witness labels; gen_lean_data.py verified all three TRUE
numerically (hu=True hv=True hT(1..21)=True) — routes are decide/norm_num on literals.
EXACTNESS NOTE (SCAFFOLD.md N4): whether the staircase 21-run/18-run deviation steps need
further nonzero factors (RC/CC cell conditions) is N2 proof work; flag_gen's Pall product
(nb_flag_gen_solution.lean:977-988) absorbs any extra factors structurally.
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.CertData

namespace StaircasePort.Stair

open Matrix IntMul.Kappa.R6.Bit.NB

/-! ## The explicit --ij line data over ℚ -/

def stairTv (t : Finset (Fin 23)) (i : Fin 23) : ℚ := if i ∈ t then 1 else 0

def stairG (t : Finset (Fin 23)) (i : Fin 23) : ℚ := (stairTv t i - 1 / 3) / 2

def stairA (t : Finset (Fin 23)) (i : Fin 23) : ℚ := stairTv t i + 3
def stairC (t : Finset (Fin 23)) (i : Fin 23) : ℚ := stairTv t i + 3
def stairB (t : Finset (Fin 23)) (i : Fin 23) : ℚ := stairG t i + 7 / 72
def stairD (t : Finset (Fin 23)) (i : Fin 23) : ℚ := stairG t i + 7 / 72

def stairCoeffA (k : ℕ) : ℚ := (stairAZL.getD k 0 : ℚ)
def stairCoeffB (k : ℕ) : ℚ := (stairBZL.getD k 0 : ℚ)

/-- f1 = Rrow·a (check_stair.py:126,132): k < 22 → a_k; k = 22 → al·a₀ (row λ₂₂ =
al·E(22,0) + be·E(0,22), diagonal row = al·e₀ᵀ). -/
def stairF1 (t : Finset (Fin 23)) (k : Fin 23) : ℚ :=
  if k.val < 22 then stairA t k
  else (stairAlZ : ℚ) * stairA t ⟨0, by omega⟩

/-- f2 = Crow·b: k < 22 → aCoeff_k·b_{k+1} (μ_k diagonal row = a_k at position k+1);
k = 22 → b₂₂ (μ₂₂ = E(22,22)). -/
def stairF2 (t : Finset (Fin 23)) (k : Fin 23) : ℚ :=
  if h : k.val < 22 then stairCoeffA k.val * stairB t ⟨k.val + 1, by omega⟩
  else stairB t ⟨22, by omega⟩

/-- f3 = Rcol·c: k < 22 → c_k; k = 22 → be·c₀ (column 22 of λ₂₂ = be·e₀). -/
def stairF3 (t : Finset (Fin 23)) (k : Fin 23) : ℚ :=
  if k.val < 22 then stairC t k
  else (stairBeZ : ℚ) * stairC t ⟨0, by omega⟩

/-- f4 = Ccol·d: k < 22 → bCoeff_k·d_{k+1} (column k of μ_k = b_k at row k+1);
k = 22 → d₂₂. -/
def stairF4 (t : Finset (Fin 23)) (k : Fin 23) : ℚ :=
  if h : k.val < 22 then stairCoeffB k.val * stairD t ⟨k.val + 1, by omega⟩
  else stairD t ⟨22, by omega⟩

/-! ### Nonvanishing helpers (N4 route)

`stairTv t i ∈ {0,1}` for ANY t (membership if-then-else), so `stairA/stairC ∈ {3,4}`,
`stairG ∈ {−1/6, 1/3}`, `stairB/stairD ∈ {−5/72, 31/72}` — all nonzero, independently of
`t.card = 3` (the line hypothesis is honored in the statement but the nonvanishing is
cardinality-free; check_stair.py evaluates it on 3-subsets). Coefficients are nonzero
literals: `interval_cases` + kernel `decide` on the concrete 22-entry lists. -/

theorem stairTv_mem (t : Finset (Fin 23)) (i : Fin 23) : stairTv t i = 0 ∨ stairTv t i = 1 := by
  by_cases h : i ∈ t <;> simp [stairTv, h]

theorem stairG_val (t : Finset (Fin 23)) (i : Fin 23) :
    stairG t i = -((1 : ℚ) / 6) ∨ stairG t i = (1 : ℚ) / 3 := by
  rcases stairTv_mem t i with h | h <;> simp [stairG, h] <;> norm_num

theorem stairA_ne_zero (t : Finset (Fin 23)) (i : Fin 23) : stairA t i ≠ 0 := by
  rcases stairTv_mem t i with h | h <;> simp [stairA, h] <;> norm_num

theorem stairC_ne_zero (t : Finset (Fin 23)) (i : Fin 23) : stairC t i ≠ 0 := by
  rcases stairTv_mem t i with h | h <;> simp [stairC, h] <;> norm_num

theorem stairB_ne_zero (t : Finset (Fin 23)) (i : Fin 23) : stairB t i ≠ 0 := by
  rcases stairG_val t i with h | h <;> simp [stairB, h] <;> norm_num

theorem stairD_ne_zero (t : Finset (Fin 23)) (i : Fin 23) : stairD t i ≠ 0 := by
  rcases stairG_val t i with h | h <;> simp [stairD, h] <;> norm_num

/-- All 22 entries of stairAZL are nonzero literals (kernel-checked case-by-case). -/
theorem stairCoeffA_ne_zero (n : ℕ) (hn : n < 22) : stairCoeffA n ≠ 0 := by
  interval_cases n <;> decide

/-- All 22 entries of stairBZL are nonzero literals (kernel-checked case-by-case). -/
theorem stairCoeffB_ne_zero (n : ℕ) (hn : n < 22) : stairCoeffB n ≠ 0 := by
  interval_cases n <;> decide

/-- **N4-1** — f1..f4 nonzero on every line + inner corners nonzero: the exact Lean content
of check_stair.py item 1 (zeros = 0 over C(23,3) = 1771 lines × 23 rows; inner-corner
products c₀·d₂₂ = f3-inner and a₀·b₂₂ = f2-inner nonzero, check_stair.py:134).
Route: tv ∈ {0,1} with Σtv = 3 (t.card = 3) ⇒ a,c ∈ {3,4}, g ∈ {−1/6, 1/3},
b,d ∈ {−5/72, 31/72}, coefficients in [1, P) ⇒ nonzero; case split + norm_num. -/
theorem stair_f_nonvanishing (t : Finset (Fin 23)) (_ht : t.card = 3) :
    (∀ k : Fin 23, stairF1 t k ≠ 0 ∧ stairF2 t k ≠ 0 ∧ stairF3 t k ≠ 0 ∧ stairF4 t k ≠ 0) ∧
    stairC t ⟨0, by omega⟩ * stairD t ⟨22, by omega⟩ ≠ 0 ∧
    stairA t ⟨0, by omega⟩ * stairB t ⟨22, by omega⟩ ≠ 0 := by
  refine ⟨fun k => ⟨?f1, ?f2, ?f3, ?f4⟩, ?ic1, ?ic2⟩
  · -- f1 = Rrow·a: k < 22 → a_k ∈ {3,4}; k = 22 → al·a₀ with al = 53462342 ≠ 0
    simp only [stairF1]
    split
    · exact stairA_ne_zero t k
    · exact mul_ne_zero (by simp [stairAlZ]) (stairA_ne_zero t _)
  · -- f2 = Crow·b: k < 22 → aCoeff_k (nonzero literal) · b_{k+1}; k = 22 → b₂₂
    simp only [stairF2]
    split
    · rename_i h
      exact mul_ne_zero (stairCoeffA_ne_zero k.val h) (stairB_ne_zero t _)
    · exact stairB_ne_zero t _
  · -- f3 = Rcol·c: symmetric to f1 with be = 62316488
    simp only [stairF3]
    split
    · exact stairC_ne_zero t k
    · exact mul_ne_zero (by simp [stairBeZ]) (stairC_ne_zero t _)
  · -- f4 = Ccol·d: symmetric to f2
    simp only [stairF4]
    split
    · rename_i h
      exact mul_ne_zero (stairCoeffB_ne_zero k.val h) (stairD_ne_zero t _)
    · exact stairD_ne_zero t _
  · -- inner corner c₀·d₂₂ (f3-inner)
    exact mul_ne_zero (stairC_ne_zero t _) (stairD_ne_zero t _)
  · -- inner corner a₀·b₂₂ (f2-inner)
    exact mul_ne_zero (stairA_ne_zero t _) (stairB_ne_zero t _)

/-! ## hu/hv/hT analogues at the extracted witness labels (all verified TRUE numerically) -/

/-- **N4-2** — hu analogue (data_edge_sol_aux hu, nb_data_edge_solution.lean:505):
x₁₀·x₂₀ ≠ 0 at the staircase witness. Route: norm_num on stairWX1L/stairWX2L literals. -/
theorem stair_hu : stairX1 0 * stairX2 0 ≠ 0 := by
  simp [stairX1, stairX2, stairWX1L, stairWX2L] <;> norm_num

/-- **N4-3** — hv analogue (nb_data_edge_solution.lean:506, y₁₍ₕ₊₃₎·y₂₍ₕ₊₃₎ with h+3 = 22). -/
theorem stair_hv : stairY1 22 * stairY2 22 ≠ 0 := by
  simp [stairY1, stairY2, stairWY1L, stairWY2L] <;> norm_num

/-- **N4-4** — hT analogue (nb_data_edge_solution.lean:507-508, l ∈ [1, h+2] = [1,21]):
the 21-run diagonal-deviation products. Route: Fin interval case analysis + norm_num. -/
theorem stair_hT : ∀ l, 1 ≤ l → l ≤ 21 →
    stairX1 l * stairY1 22 + stairX2 l * stairY2 22 ≠ 0 := by
  intro l h1 h2
  interval_cases l <;>
    simp [stairX1, stairX2, stairY1, stairY2, stairWX1L, stairWX2L, stairWY1L, stairWY2L] <;>
    norm_num

end StaircasePort.Stair
