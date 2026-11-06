import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Data
import StaircasePort.Cert
import StaircasePort.Pivot
import StaircasePort.Signature
import StaircasePort.Projector

/-!
# N7 — the REWIRE: staircase-frame flag basis

The r6-frame route for `data_edge_stair`/`flagBasis_stair` was REFUTED (N2d: at the staircase
witness the r6-frame corner of `qM M` is singular, rank 44; 18 of the 39 corner positions are
not pivots). This file rebuilds the flag basis in the STAIRCASE frame:

* the staircase frame matrices `TeStair`/`TeStair'` (r6 `Te`/`Te'` analogues) and the
  conjugation identity `SbStair_conj` (r6 `Sb_conj` analogue);
* the generic edges restated at `qMStair`: `aux_edge_of_Stair` / `side_edge_of_Stair`
  (r6 bodies with `qM_corner` → `qMStair_corner`, `cor` → `corStairQ`);
* the staircase support computations (aux/side corner patterns over
  `LtermsStair`/`RtermsStair` — verified numerically first, `n7_auxside_probe.py`): the diag
  values are monomials `-stairAZL.getD β 0 · x β · y (β+1)` etc., so the aux/side clauses need
  the label facts `y l ≠ 0` for ALL `l` (r6 needed only `y 22`), obtained by widening the Pall
  `pA` factors to all `(β, l)` pairs via the `wP_l` witness (`pA_all_ne`);
* `data_edge_stair` restated: conclusion `DataE' (qMStair M)`, the `hpiv` slot replaced by
  `(hdet, hcorner)` — the middle clause is `isPiv_stairMid` (Projector.lean, PROVED) and the
  corner clause is the corner-hole contract `isPiv_stairCorner_contract` (being proved by a
  parallel agent; consumed here as the local `sorry` placeholder);
* `flag_gen_stair_aux` + `flagBasis_stair`: the N5-2 port with `S := SbStair U V` (one
  witness pair serves all three classes; the DataE clause cannot move alone — see
  SCAFFOLD.md "## N7 NOTES"). `flagBasis_stair`'s statement is BYTE-IDENTICAL.
-/

set_option maxRecDepth 20000

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker
open N52

set_option maxHeartbeats 1000000

/-! ## R7-1 — the staircase flag frame -/

/-- The staircase frame rows: `PmStair` read in the staircase flag order (r6 `Te` analogue). -/
noncomputable def TeStair : Matrix (Fin (23 * 23)) (Pr 23) ℚ := PmStair.submatrix flagEquivStair id

/-- The staircase frame columns: `QmStair` read in the staircase flag order (r6 `Te'`). -/
noncomputable def TeStair' : Matrix (Pr 23) (Fin (23 * 23)) ℚ := QmStair.submatrix id flagEquivStair

lemma PmStair_mul_QmStair : PmStair * QmStair = 1 := by
  rw [PmStair, QmStair, Matrix.mul_assoc (Matrix.diagonal dv) TmStair,
    ← Matrix.mul_assoc TmStair TiStair (Matrix.diagonal fun u : Pr 23 => (dv u)⁻¹),
    TmStair_TiStair, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
  ext u
  simp [dv_ne_zero]

lemma TeStair_TeStair' : TeStair * TeStair' = 1 := by
  rw [TeStair, TeStair', ← Matrix.submatrix_mul PmStair QmStair flagEquivStair id flagEquivStair
    Function.bijective_id, PmStair_mul_QmStair]
  ext i j; simp [Matrix.one_apply]

lemma TeStair'_TeStair : TeStair' * TeStair = 1 := by
  rw [TeStair', TeStair, ← Matrix.submatrix_mul QmStair PmStair id flagEquivStair id
    flagEquivStair.bijective, QmStair_mul_PmStair]
  ext i j; simp [Matrix.one_apply]

/-- The flag-basis form of the staircase projector (r6 `qM_eq` analogue). -/
lemma qMStair_eq (M : Matrix (Pr 23) (Pr 23) ℚ) : qMStair M = TeStair * M * TeStair' := by
  unfold qMStair TeStair TeStair'
  rw [Matrix.submatrix_mul _ _ flagEquivStair id flagEquivStair Function.bijective_id,
    Matrix.submatrix_mul _ _ flagEquivStair id id Function.bijective_id, submatrix_id_id]

/-- The staircase-frame basis change (r6 `Sb` analogue). -/
noncomputable def SbStair (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    Matrix (Fin ((19 + 4) * (19 + 4))) (Pr (19 + 4)) ℚ := TeStair * Kf U V

/-- The staircase-frame basis change, inverse side (r6 `Sbi` analogue). -/
noncomputable def SbiStair (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    Matrix (Pr (19 + 4)) (Fin ((19 + 4) * (19 + 4))) ℚ := Kfi U V * TeStair'

/-- The conjugation identity in the staircase frame (r6 `Sb_conj` analogue, same proof). -/
lemma SbStair_conj (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (A B : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) :
    SbStair U V * (A ⊗ₖ B) * SbiStair U V =
      qMStair ((Uᵀ * A * U⁻¹ᵀ) ⊗ₖ (Vᵀ * B * V⁻¹ᵀ)) := by
  rw [qMStair_eq, mul_kronecker_mul, mul_kronecker_mul, SbStair, SbiStair, Kf, Kfi]
  simp only [Matrix.mul_assoc]

/-- The staircase-frame witness pair is a basis change (r6 `Sb_inv` analogue, same proof). -/
lemma SbStair_inv (U V : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (hU : U.det ≠ 0)
    (hV : V.det ≠ 0) : SbStair U V * SbiStair U V = 1 ∧ SbiStair U V * SbStair U V = 1 := by
  have k1 : Kf U V * Kfi U V = 1 := by
    rw [Kf, Kfi, ← mul_kronecker_mul, conj_one U hU, conj_one V hV, one_kronecker_one]
  have k2 : Kfi U V * Kf U V = 1 := by
    rw [Kf, Kfi, ← mul_kronecker_mul, conj_one' U hU, conj_one' V hV, one_kronecker_one]
  constructor
  · rw [SbStair, SbiStair, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Kf U V) (Kfi U V) TeStair', k1, Matrix.one_mul, TeStair_TeStair']
  · rw [SbStair, SbiStair, Matrix.mul_assoc,
      ← Matrix.mul_assoc TeStair' TeStair (Kf U V), TeStair'_TeStair, Matrix.one_mul, k2]

/-! ## R7-2 — the staircase aux-class support computations (over the staircase family) -/

section AuxStair

variable (x y : Fin (19 + 4) → ℚ)

/-- Staircase-frame analogue of `aux1_upper` (N52, r6-frame). The zero pattern is the same;
verified numerically (`n7_auxside_probe.py`). -/
lemma aux1_upper_Stair (β γ : ℕ) (hβγ : β < γ) (hγ : γ < 19 + 4) :
    corStairQ (1 ⊗ₖ (1 - vecMulVec x y)) β (19 + 3 + γ) = 0 := by
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
      dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
      mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
      dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  · obtain rfl : γ = 19 + 3 := by omega
    simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
      dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
      mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
      dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]

/-- Staircase-frame analogue of `aux2_upper`. -/
lemma aux2_upper_Stair (β γ : ℕ) (hβγ : β < γ) (hγ : γ < 19 + 4) :
    corStairQ ((1 - vecMulVec x y) ⊗ₖ 1) β (19 + 3 + γ) = 0 := by
  rcases Nat.lt_or_ge γ (19 + 3) with h1 | h1
  · simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
      dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
      mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
      dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  · obtain rfl : γ = 19 + 3 := by omega
    simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
      dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
      mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
      dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]

/-- Staircase-frame analogue of `aux1_diag`: the diagonal value is the label monomial
`-a_β · x β · y (β+1)` (r6: `-x β · y 22`). Measured exact (`n7_auxside_probe.py`). -/
lemma aux1_diag_Stair (β : ℕ) (hβ : β < 19 + 3) :
    corStairQ (1 ⊗ₖ (1 - vecMulVec x y)) β (19 + 3 + β) =
      -((stairAZL.getD β 0 : ℤ) : ℚ) * x ⟨β, by omega⟩ * y ⟨β + 1, by omega⟩ := by
  have hfin : ((⟨19 + 3 + β - 21, by omega⟩ : Fin (19 + 4)) = ⟨β + 1, by omega⟩) := by
    simp only [Fin.mk.injEq]; omega
  simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
    dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
    mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
    dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  rw [hfin]; try ring

/-- Staircase-frame analogue of `aux1_diag_last`. -/
lemma aux1_diag_last_Stair :
    corStairQ (1 ⊗ₖ (1 - vecMulVec x y)) (19 + 3) (19 + 3 + (19 + 3)) =
      -(stairAlZ : ℚ) * x ⟨0, by omega⟩ * y ⟨19 + 3, by omega⟩ := by
  have hfin : ((⟨22, by omega⟩ : Fin (19 + 4)) = ⟨19 + 3, by omega⟩) := by simp
  simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
    dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
    mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
    dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  rw [hfin]; try ring

/-- Staircase-frame analogue of `aux2_diag`: `-b_β · x β · y (β+1)`. -/
lemma aux2_diag_Stair (β : ℕ) (hβ : β < 19 + 3) :
    corStairQ ((1 - vecMulVec x y) ⊗ₖ 1) β (19 + 3 + β) =
      -((stairBZL.getD β 0 : ℤ) : ℚ) * x ⟨β, by omega⟩ * y ⟨β + 1, by omega⟩ := by
  have hfin : ((⟨19 + 3 + β - 21, by omega⟩ : Fin (19 + 4)) = ⟨β + 1, by omega⟩) := by
    simp only [Fin.mk.injEq]; omega
  simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
    dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
    mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
    dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  rw [hfin]; try ring

/-- Staircase-frame analogue of `aux2_diag_last`. -/
lemma aux2_diag_last_Stair :
    corStairQ ((1 - vecMulVec x y) ⊗ₖ 1) (19 + 3) (19 + 3 + (19 + 3)) =
      -(stairBeZ : ℚ) * x ⟨0, by omega⟩ * y ⟨19 + 3, by omega⟩ := by
  have hfin : ((⟨22, by omega⟩ : Fin (19 + 4)) = ⟨19 + 3, by omega⟩) := by simp
  simp (disch := omega) only [corStairQ, LtermsStair, LtermsZStair, RtermsStair, RtermsZStair,
    dif_pos, dif_neg, if_pos, if_neg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    kronecker_apply, Matrix.one_apply, Matrix.sub_apply, vecMulVec_apply, Fin.mk.injEq,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, neg_mul,
    mul_neg, neg_neg, neg_zero, sub_self, Pi.one_apply, ite_true, ite_false, dite_true,
    dite_false, ↓reduceIte, ↓reduceDIte, kroneckerMap_apply, Nat.add_sub_cancel_left]
  rw [hfin]; try ring

end AuxStair

/-! ## R7-3 — the staircase aux-class edge (r6 `aux_edge_of` at `qMStair`) -/

/-- Staircase-frame analogue of `N52.aux_edge_of` (same body; `qM_corner` → `qMStair_corner`,
`cor` → `corStairQ`, `qM_idem`/`qM_trace` → `qMStair_*`). -/
theorem aux_edge_of_Stair (M : Matrix (Pr 23) (Pr 23) ℚ) (hM : M * M = M)
    (htr : M.trace = ((19 + 4) * (19 + 3) : ℕ))
    (hlow : ∀ β γ : ℕ, β < γ → γ < 19 + 4 → corStairQ M β (19 + 3 + γ) = 0)
    (hdiag : ∀ β : ℕ, β < 19 + 4 → corStairQ M β (19 + 3 + β) ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair M) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  have hk := two_k_le_23
  have hmm : (19 + 4) * (19 + 4) = (19 + 4) * (19 + 3) + (19 + 4) := by ring
  have hq := qMStair_idem hM
  have hrank : (qMStair M).rank = (19 + 4) * (19 + 4) - (19 + 4) := by
    have h1 := rank_eq_trace (qMStair M) hq
    rw [qMStair_trace, htr] at h1
    have := Nat.cast_injective h1
    omega
  set Cp : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ := (qMStair M).submatrix
    (fun l : Fin (19 + 4) => (⟨l.val, by omega⟩ : Fin ((19 + 4) * (19 + 4))))
    (fun r : Fin (19 + 4) => (⟨(19 + 4) * (19 + 4) - (19 + 4) + r.val, by omega⟩ :
      Fin ((19 + 4) * (19 + 4)))) with hCp
  have hCe : ∀ β γ : Fin (19 + 4), Cp β γ = corStairQ M β.val (19 + 3 + γ.val) := by
    intro β γ
    have e : (⟨(19 + 4) * (19 + 4) - (19 + 4) + γ.val, by omega⟩ : Fin ((19 + 4) * (19 + 4))) =
        ⟨23 * 23 - 45 + (19 + 3 + γ.val), by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hCp, submatrix_apply, e, ← qMStair_corner M β.val (19 + 3 + γ.val) (by omega) (by omega)]
  have hCl : ∀ β γ : Fin (19 + 4), β < γ → Cp β γ = 0 := fun β γ hβγ => by
    rw [hCe]; exact hlow _ _ hβγ γ.isLt
  have hCd : ∀ β : Fin (19 + 4), Cp β β ≠ 0 := fun β => by rw [hCe]; exact hdiag _ β.isLt
  have hdet : Cp.det ≠ 0 := by
    rw [det_of_isLowerTriangular Cp (fun a b hab => hCl a b hab)]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hCd a
  have hmid := fun i (h1 : 19 + 4 ≤ i) (h2 : i < (19 + 4) * (19 + 4) - (19 + 4)) =>
    Platform.isPiv_mid (k := 19 + 4) (by omega) (qMStair M) hq hrank hdet h1 h2
  have hcorner : ∀ l : Fin (19 + 4), IsPiv (qMStair M) l.val ((19 + 4) * (19 + 4) - (19 + 4) + l.val) :=
    fun l => isPiv_block (qMStair M) Cp (by omega) (by omega) (fun i j => rfl)
      (isPiv_diag_of_lower Cp hCl hCd l)
  refine edge_exact (by omega) (qMStair M) hq _ ?_ ?_ ?_ ?_
  · intro ρ hρ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
    rcases hρ with rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> omega
  · rw [DEPort.runPairs_cons, DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil,
      List.nodup_append]
    refine ⟨DEPort.nodup_run _ _ _, DEPort.nodup_run _ _ _, ?_⟩
    intro a ha b hb hab
    rw [DEPort.mem_run] at ha hb
    obtain ⟨k, hk1, rfl⟩ := ha
    obtain ⟨k', hk2, rfl⟩ := hb
    simp only [Prod.mk.injEq] at hab
    omega
  · intro p hp
    rw [DEPort.runPairs_cons, DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil,
      List.mem_append, DEPort.mem_run, DEPort.mem_run] at hp
    rcases hp with ⟨k, hk1, rfl⟩ | ⟨k, hk1, rfl⟩
    · simpa using hcorner ⟨k, hk1⟩
    · exact hmid _ (by simp only; omega) (by simp only; omega)
  · rw [hrank, DEPort.runPairs_cons, DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil,
      List.length_append, DEPort.length_run, DEPort.length_run]

/-- Staircase-frame aux edge of the first kind (r6 `aux1_edge`; the label facts are the
strengthened all-coordinate nonvanishing the staircase diag values need). -/
lemma stairBeZ_ne : (stairBeZ : ℚ) ≠ 0 := by
  simp only [stairBeZ]; norm_num

lemma stairBZL_ne (r : ℕ) (hr : r < 22) : ((stairBZL.getD r 0 : ℤ) : ℚ) ≠ 0 := by
  interval_cases r <;> norm_num [stairBZL]

theorem aux1_edge_Stair (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : ∀ l : Fin (19 + 4), y l ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair (1 ⊗ₖ (1 - vecMulVec x y))) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  refine aux_edge_of_Stair _ ?_ ?_ (fun β γ h1 h2 => aux1_upper_Stair x y β γ h1 h2) ?_
  · rw [← mul_kronecker_mul, Matrix.one_mul, one_sub_vmv_idem x y hxy]
  · rw [trace_kronecker, trace_one, trace_one_sub_vmv x y hxy, Fintype.card_fin]; push_cast; ring
  · intro β hβ
    rcases Nat.lt_or_ge β (19 + 3) with h1 | h1
    · rw [aux1_diag_Stair x y β h1]
      exact mul_ne_zero
        (mul_ne_zero (neg_ne_zero.2 (stairAZL_ne β (by omega))) (hx ⟨β, by omega⟩ h1))
        (hy ⟨β + 1, by omega⟩)
    · obtain rfl : β = 19 + 3 := by omega
      rw [aux1_diag_last_Stair]
      exact mul_ne_zero
        (mul_ne_zero (neg_ne_zero.2 stairAlZ_ne) (hx ⟨0, by omega⟩ (by simp only; omega)))
        (hy ⟨19 + 3, by omega⟩)

/-- Staircase-frame aux edge of the second kind (r6 `aux2_edge`). -/
theorem aux2_edge_Stair (x y : Fin (19 + 4) → ℚ) (hxy : y ⬝ᵥ x = 1)
    (hx : ∀ β : Fin (19 + 4), β.val < 19 + 3 → x β ≠ 0) (hy : ∀ l : Fin (19 + 4), y l ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qMStair ((1 - vecMulVec x y) ⊗ₖ 1)) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  refine aux_edge_of_Stair _ ?_ ?_ (fun β γ h1 h2 => aux2_upper_Stair x y β γ h1 h2) ?_
  · rw [← mul_kronecker_mul, Matrix.one_mul, one_sub_vmv_idem x y hxy]
  · rw [trace_kronecker, trace_one, trace_one_sub_vmv x y hxy, Fintype.card_fin]; push_cast; ring
  · intro β hβ
    rcases Nat.lt_or_ge β (19 + 3) with h1 | h1
    · rw [aux2_diag_Stair x y β h1]
      exact mul_ne_zero
        (mul_ne_zero (neg_ne_zero.2 (stairBZL_ne β (by omega))) (hx ⟨β, by omega⟩ h1))
        (hy ⟨β + 1, by omega⟩)
    · obtain rfl : β = 19 + 3 := by omega
      rw [aux2_diag_last_Stair]
      exact mul_ne_zero
        (mul_ne_zero (neg_ne_zero.2 stairBeZ_ne) (hx ⟨0, by omega⟩ (by simp only; omega)))
        (hy ⟨19 + 3, by omega⟩)

end StaircasePort.Stair
