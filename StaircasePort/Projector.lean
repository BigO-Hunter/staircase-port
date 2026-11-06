/-
# N6 — the R7/staircase data-entrance PROJECTOR

N2d's frame delta (`n2d_frame_delta`, Pivot.lean) showed the r6/Defs4 projector `qM` reads the
r6 flag family (`Lterms`/`Rterms`), NOT the staircase one, so `qM M`'s corner is `cor`, never
`corStairQ`.  The honest route recorded in SCAFFOLD.md "## N2d RESUME" is a DIFFERENT OBJECT:
the same construction as `Tm`/`Ti`/`flagEquiv`/`qM` built from the staircase family
(`LtermsStair`/`RtermsStair`, Cert.lean) instead.  This file builds it and proves its
`qM_corner` analogue, so the staircase corner factor (`corStairQ`, `stair_data_cert`) becomes
usable by the SAME generic machinery r6 uses.

## The construction (derived, then verified numerically — `n6_proj_probe.py`)

r6's corner identity is: `qM M (aL i) (bL j) = cor M i j` where `aL`/`bL` are the pair
coordinates whose `Tm`-row / `Ti`-column carry the family vectors `Lterms i` / `Rterms j`
(`Tm = 1 - Nm`, `Ti = 1 + Nm`, `Nm² = 0`).  The same three ingredients exist here:

* anchors `aLsStair i` / `bLsStair j` = the FIRST listed term of `LtermsStair i` /
  `RtermsStair j` (the coordinate whose coefficient is the family's leading coefficient);
* `NsStair` — one entry per multi-term family vector (the staircase has only 23: the row
  family is multi-term only at `i = 22`, the column family only at `j = 22..43`), with entry
  = (other term) / (leading term) so that `Tm`-row/`Ti`-column reproduce the vector UP TO the
  leading coefficient;
* `NsStair² = 0` (no 2-path: source rows are `(r+1,r)`, target columns `(r,r+1)`, and the
  single extra entry goes `(22,0) → (0,22)`), hence `TiStair * TmStair = 1`.

Two facts differ from r6 and are handled by the diagonal scaling `Ds`/`Di`: the staircase
leading coefficients are NOT 1 (`al`, `a_r`), so the unscaled `Tm`-row is `LtermsStair i / leadL i`.
`qMStair M = (Ds * TmStair) * M * (TiStair * Di)` with `Ds = diagonal dv`,
`dv (aLsStair i) = leadL i`, `dv (bLsStair j) = (leadR j)⁻¹` makes the corner EXACT:

  `qMStair_corner : qMStair M ⟨i⟩ ⟨23*23 - 45 + j⟩ = corStairQ M i j`  (i, j < 45)

Numerics (`n6_proj_probe.py`, exact `Fraction`): at the extracted witness the corner is
`corStairQ` on 2025/2025 entries, has rank 45, and its pivot set is the extracted permutation
`pc` (45/45 positions, the 39 run positions included); the r6 frame gives rank 44 / 21-of-21
as its own theorem says — a two-frame control.

## Axioms
Every theorem here is `[propext, Classical.choice, Quot.sound]`; the only `sorry` reachable is
`Platform.isPiv_mid`'s documented stub (Pivot.lean), used by `isPiv_stairMid`.
-/
import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Cert
import StaircasePort.Signature
import StaircasePort.Corner

namespace StaircasePort.Stair

open Matrix IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

/-! ## N6-2a — anchors: the family term that carries the leading coefficient -/

/-- The coordinate carrying row `i` of the staircase flag family: the first listed term of
`LtermsStair i` (Cert.lean). -/
def aLsStair (i : ℕ) : Pr 23 :=
  if h1 : i < 22 then (⟨i, by omega⟩, ⟨i, by omega⟩)
  else if i = 22 then (⟨22, by omega⟩, ⟨0, by omega⟩)
  else if i = 23 then (⟨0, by omega⟩, ⟨3, by omega⟩)
  else if h2 : i < 45 then (⟨i - 22, by omega⟩, ⟨i - 24, by omega⟩)
  else (⟨0, by omega⟩, ⟨0, by omega⟩)

/-- The coordinate carrying column `j`: the first listed term of `RtermsStair j`. -/
def bLsStair (j : ℕ) : Pr 23 :=
  if h1 : j < 20 then (⟨j + 1, by omega⟩, ⟨j + 3, by omega⟩)
  else if j = 20 then (⟨0, by omega⟩, ⟨20, by omega⟩)
  else if j = 21 then (⟨0, by omega⟩, ⟨21, by omega⟩)
  else if h2 : j < 44 then (⟨j - 22, by omega⟩, ⟨j - 21, by omega⟩)
  else (⟨22, by omega⟩, ⟨22, by omega⟩)

set_option linter.unusedSimpArgs false in
lemma aLsStair_inj {i i' : ℕ} (hi : i < 45) (hi' : i' < 45) (e : aLsStair i = aLsStair i') :
    i = i' := by
  simp only [aLsStair] at e
  split_ifs at e <;> simp only [pr_eq_iff] at e <;> omega

set_option linter.unusedSimpArgs false in
lemma bLsStair_inj {j j' : ℕ} (hj : j < 45) (hj' : j' < 45) (e : bLsStair j = bLsStair j') :
    j = j' := by
  simp only [bLsStair] at e
  split_ifs at e <;> simp only [pr_eq_iff] at e <;> omega

set_option linter.unusedSimpArgs false in
lemma aLsStair_ne_bLsStair {i j : ℕ} (hi : i < 45) (hj : j < 45) : aLsStair i ≠ bLsStair j := by
  intro e
  simp only [aLsStair, bLsStair] at e
  split_ifs at e <;> simp only [pr_eq_iff] at e <;> omega

lemma two_k_le_23 : 2 * 45 ≤ 23 * 23 := by norm_num

/-- The first `45` indices of the staircase ordering are the anchors `aLsStair`, the last `45`
are the anchors `bLsStair` (the r6 `exists_flagEquiv` argument, at `h = 19`). -/
lemma exists_flagEquivStair : ∃ e : Fin (23 * 23) ≃ Pr 23,
    (∀ i (hi : i < 45), e ⟨i, by have := two_k_le_23; omega⟩ = aLsStair i) ∧
    (∀ j (hj : j < 45), e ⟨23 * 23 - 45 + j, by have := two_k_le_23; omega⟩ = bLsStair j) := by
  classical
  have hk := two_k_le_23
  let φ : Fin 45 ⊕ Fin 45 → Pr 23 := Sum.elim (fun i => aLsStair i) (fun j => bLsStair j)
  let ψ : Fin 45 ⊕ Fin 45 → Fin (23 * 23) :=
    Sum.elim (fun i => ⟨i.val, by omega⟩) (fun j => ⟨23 * 23 - 45 + j.val, by omega⟩)
  have hφ : Function.Injective φ := by
    rintro (i | i) (j | j) e <;> simp only [φ, Sum.elim_inl, Sum.elim_inr] at e
    · exact congrArg Sum.inl (Fin.ext (aLsStair_inj i.isLt j.isLt e))
    · exact absurd e (aLsStair_ne_bLsStair i.isLt j.isLt)
    · exact absurd e.symm (aLsStair_ne_bLsStair j.isLt i.isLt)
    · exact congrArg Sum.inr (Fin.ext (bLsStair_inj i.isLt j.isLt e))
  let F₀ : Fin (23 * 23) ≃ Pr 23 := finProdFinEquiv.symm
  have hψ : Function.Injective (F₀ ∘ ψ) := by
    refine F₀.injective.comp ?_
    rintro (i | i) (j | j) e <;> simp only [ψ, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at e
    · exact congrArg Sum.inl (Fin.ext e)
    · have := i.isLt; omega
    · have := j.isLt; omega
    · exact congrArg Sum.inr (Fin.ext (by omega))
  let E : {x // x ∈ Set.range (F₀ ∘ ψ)} ≃ {x // x ∈ Set.range φ} :=
    (Equiv.ofInjective _ hψ).symm.trans (Equiv.ofInjective _ hφ)
  let σ := E.extendSubtype
  have key : ∀ s, F₀.trans σ (ψ s) = φ s := by
    intro s
    simp only [Equiv.trans_apply, σ]
    rw [Equiv.extendSubtype_apply_of_mem E (F₀ (ψ s)) ⟨s, rfl⟩]
    have h1 : (Equiv.ofInjective _ hψ).symm ⟨F₀ (ψ s), ⟨s, rfl⟩⟩ = s := by
      apply hψ
      exact Equiv.apply_ofInjective_symm hψ _
    simp only [E, Equiv.trans_apply, h1]
    rfl
  exact ⟨F₀.trans σ, fun i hi => key (Sum.inl ⟨i, hi⟩), fun j hj => key (Sum.inr ⟨j, hj⟩)⟩

/-- The staircase ordering of the pairs. -/
noncomputable def flagEquivStair : Fin (23 * 23) ≃ Pr 23 :=
  Classical.choose exists_flagEquivStair

lemma flagEquivStair_top (i : ℕ) (hi : i < 45) :
    flagEquivStair ⟨i, by have := two_k_le_23; omega⟩ = aLsStair i :=
  (Classical.choose_spec exists_flagEquivStair).1 i hi

lemma flagEquivStair_bot (j : ℕ) (hj : j < 45) :
    flagEquivStair ⟨23 * 23 - 45 + j, by have := two_k_le_23; omega⟩ = bLsStair j :=
  (Classical.choose_spec exists_flagEquivStair).2 j hj

/-! ## N6-2b — the leading coefficients of the staircase family -/

/-- Leading coefficient of row `i` (the coefficient of `aLsStair i` in `LtermsStair i`). -/
def leadL (i : ℕ) : ℚ := if i = 22 then (stairAlZ : ℚ) else 1

/-- Leading coefficient of column `j` (the coefficient of `bLsStair j` in `RtermsStair j`). -/
def leadR (j : ℕ) : ℚ :=
  if 22 ≤ j ∧ j < 44 then ((stairAZL.getD (j - 22) 0 : ℤ) : ℚ) else 1

lemma stairAlZ_ne : (stairAlZ : ℚ) ≠ 0 := by
  simp only [stairAlZ]
  norm_num

lemma stairAZL_ne (r : ℕ) (hr : r < 22) : ((stairAZL.getD r 0 : ℤ) : ℚ) ≠ 0 := by
  interval_cases r <;> norm_num [stairAZL]

/-! ## N6-2c — the nilpotent `NsStair` (`NsStair² = 0`) -/

/-- The staircase analogue of `Nm` (Defs4:869): one entry per multi-term family vector.
Row side: `LtermsStair 22 = al·E(22,0) + be·E(0,22)` needs `(22,0) → (0,22)` with `-be/al`.
Column side: `RtermsStair (22+r) = a_r·E(r,r+1) + b_r·E(r+1,r)` needs `(r+1,r) → (r,r+1)` with
`b_r/a_r`. Every other family vector is a single coordinate (its anchor), so it needs no entry. -/
def NsStair : Matrix (Pr 23) (Pr 23) ℚ := Matrix.of fun u v =>
  if u.1.val = u.2.val + 1 ∧ v.1 = u.2 ∧ v.2 = u.1 then
    ((stairBZL.getD u.2.val 0 : ℤ) : ℚ) / ((stairAZL.getD u.2.val 0 : ℤ) : ℚ)
  else if u = (⟨22, by omega⟩, ⟨0, by omega⟩) ∧ v = (⟨0, by omega⟩, ⟨22, by omega⟩) then
    -((stairBeZ : ℚ) / (stairAlZ : ℚ))
  else 0

/-- No 2-path through the column-side entries: targets `(r,r+1)` are not sources `(s+1,s)`,
nor the extra source `(22,0)`. -/
lemma nstair_no_2path_cc (u v w : Pr 23)
    (h1 : u.1.val = u.2.val + 1 ∧ v.1 = u.2 ∧ v.2 = u.1)
    (h2 : v.1.val = v.2.val + 1 ∧ w.1 = v.2 ∧ w.2 = v.1) : False := by
  obtain ⟨e1, e2, e3⟩ := h1
  obtain ⟨f1, -, -⟩ := h2
  rw [e2, e3] at f1
  omega

/-- No 2-path from a column-side entry into the row-side entry: its source `(22,0)` has
first coordinate `22` but a target `(r,r+1)` has second coordinate `≤ 22` with first `≤ 21`. -/
lemma nstair_no_2path_cL (u v w : Pr 23)
    (h1 : u.1.val = u.2.val + 1 ∧ v.1 = u.2 ∧ v.2 = u.1)
    (h3 : v = (⟨22, by omega⟩, ⟨0, by omega⟩)) : False := by
  obtain ⟨e1, e2, e3⟩ := h1
  have hv1 : v.1 = (⟨22, by omega⟩ : Fin 23) := by rw [h3]
  have hv2 : v.2 = (⟨0, by omega⟩ : Fin 23) := by rw [h3]
  rw [e2] at hv1
  rw [e3] at hv2
  have : u.1.val = 0 := by rw [hv2]
  omega

lemma NsStair_sq : NsStair * NsStair = 0 := by
  ext u w
  simp only [Matrix.mul_apply, NsStair, of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  by_cases h1 : u.1.val = u.2.val + 1 ∧ v.1 = u.2 ∧ v.2 = u.1
  · rw [if_pos h1]
    by_cases h2 : v.1.val = v.2.val + 1 ∧ w.1 = v.2 ∧ w.2 = v.1
    · exact absurd (nstair_no_2path_cc u v w h1 h2) not_false
    · rw [if_neg h2]
      by_cases h3 : v = (⟨22, by omega⟩, ⟨0, by omega⟩) ∧
          w = (⟨0, by omega⟩, ⟨22, by omega⟩)
      · obtain ⟨h3a, -⟩ := h3
        exact absurd (nstair_no_2path_cL u v w h1 h3a) not_false
      · rw [if_neg h3, mul_zero]
  · rw [if_neg h1]
    by_cases hL : u = (⟨22, by omega⟩, ⟨0, by omega⟩) ∧
        v = (⟨0, by omega⟩, ⟨22, by omega⟩)
    · rw [if_pos hL]
      obtain ⟨-, hv⟩ := hL
      have e2 : ¬ (v.1.val = v.2.val + 1 ∧ w.1 = v.2 ∧ w.2 = v.1) := by
        rintro ⟨e, -⟩
        rw [hv] at e
        simp only [Fin.val_mk] at e
        omega
      have e3 : ¬ (v = (⟨22, by omega⟩, ⟨0, by omega⟩) ∧
          w = (⟨0, by omega⟩, ⟨22, by omega⟩)) := by
        rintro ⟨e, -⟩
        rw [hv] at e
        simp only [Prod.mk.injEq, Fin.mk.injEq] at e
        omega
      rw [if_neg e2, if_neg e3, mul_zero]
    · rw [if_neg hL, zero_mul]

/-! ## N6-2d — `TmStair`/`TiStair` and the family rows/columns -/

/-- `T = 1 - N`, `T⁻¹ = 1 + N` (r6 `Tm`/`Ti`, Defs4:871-872). -/
def TmStair : Matrix (Pr 23) (Pr 23) ℚ := 1 - NsStair
def TiStair : Matrix (Pr 23) (Pr 23) ℚ := 1 + NsStair

lemma TmStair_TiStair : TmStair * TiStair = 1 := by
  rw [TmStair, TiStair, sub_mul, one_mul, mul_add, mul_one, NsStair_sq]; abel

lemma TiStair_TmStair : TiStair * TmStair = 1 := by
  rw [TmStair, TiStair, add_mul, one_mul, mul_sub, mul_one, NsStair_sq]; abel

set_option linter.unusedSimpArgs false in
/-- Row `aLsStair i` of `TmStair` is `LtermsStair i` up to its leading coefficient. -/
lemma TmStair_row (i : ℕ) (hi : i < 45) (u : Pr 23) :
    leadL i * TmStair (aLsStair i) u = sv (LtermsStair i) u := by
  obtain ⟨u1, u2⟩ := u
  simp only [TmStair, NsStair, Matrix.sub_apply, of_apply, Matrix.one_apply, aLsStair,
    LtermsStair, LtermsZStair, sv, leadL]
  split_ifs <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] <;>
    (try split_ifs) <;>
    simp only [Prod.ext_iff, Fin.ext_iff, true_and, and_true] at * <;>
    first
      | (exfalso; omega)
      | (tauto)
      | norm_num [stairAlZ, stairBeZ]

set_option linter.unusedSimpArgs false in
/-- Column `bLsStair j` of `TiStair` is `RtermsStair j` up to its leading coefficient. -/
lemma TiStair_col (j : ℕ) (hj : j < 45) (u : Pr 23) :
    leadR j * TiStair u (bLsStair j) = sv (RtermsStair j) u := by
  obtain ⟨u1, u2⟩ := u
  simp only [TiStair, NsStair, Matrix.add_apply, of_apply, Matrix.one_apply, bLsStair,
    RtermsStair, RtermsZStair, sv, leadR]
  split_ifs <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] <;>
    (try split_ifs) <;>
    simp only [Prod.ext_iff, Fin.ext_iff, true_and, and_true] at * <;>
    first
      | (exfalso; omega)
      | (tauto)
      | (rw [show (u2 : ℕ) = j - 22 from by omega]
         have hz : ((stairAZL.getD (j - 22) 0 : ℤ) : ℚ) ≠ 0 := stairAZL_ne (j - 22) (by omega)
         field_simp
         ring)
      | norm_num [stairAlZ, stairBeZ]

/-! ## N6-2e — the diagonal scaling that makes the corner exact -/

/-- `∑ u, sv l u * f u` as a sparse sum (ported from Signature.lean:473). -/
lemma n6_sum_sv_mul {n : ℕ} (l : List (ℚ × Pr n)) (f : Pr n → ℚ) :
    ∑ u, sv l u * f u = (l.map fun s => s.1 * f s.2).sum := by
  induction l with
  | nil => simp [sv]
  | cons s l ih =>
    simp only [sv, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib] at ih ⊢
    rw [ih]
    congr 1
    simp [ite_mul]

/-- `∑ u, f u * sv l u` as a sparse sum (ported from Signature.lean:483). -/
lemma n6_sum_mul_sv {n : ℕ} (l : List (ℚ × Pr n)) (f : Pr n → ℚ) :
    ∑ u, f u * sv l u = (l.map fun s => f s.2 * s.1).sum := by
  rw [show (∑ u, f u * sv l u) = ∑ u, sv l u * f u from
    Finset.sum_congr rfl fun u _ => mul_comm _ _, n6_sum_sv_mul]
  congr 1
  exact List.map_congr_left fun s _ => mul_comm _ _

/-- The scaling: `lead` on the row anchors, `lead⁻¹` on the column anchors, `1` elsewhere.
(Called `dv` because it is `Tᵥ`-shaped: `Pm = diag dv * TmStair` produces the exact family
rows, `Qm = TiStair * diag dv⁻¹` the exact family columns.) -/
def dv (u : Pr 23) : ℚ :=
  if u.2.val = u.1.val + 1 then ((stairAZL.getD u.1.val 0 : ℤ) : ℚ)⁻¹
  else if u = (⟨22, by omega⟩, ⟨0, by omega⟩) then (stairAlZ : ℚ) else 1

lemma dv_ne_zero (u : Pr 23) : dv u ≠ 0 := by
  by_cases h : u.2.val = u.1.val + 1
  · rw [dv, if_pos h]
    exact inv_ne_zero (stairAZL_ne u.1.val (by omega))
  · rw [dv, if_neg h]
    by_cases h2 : u = (⟨22, by omega⟩, ⟨0, by omega⟩)
    · rw [if_pos h2]; exact stairAlZ_ne
    · rw [if_neg h2]; norm_num

set_option linter.unusedSimpArgs false in
lemma dv_aLs (i : ℕ) (hi : i < 45) : dv (aLsStair i) = leadL i := by
  simp only [dv, aLsStair, leadL]
  split_ifs <;> simp only [Prod.ext_iff, Fin.ext_iff, true_and, and_true] at * <;>
    first | (exfalso; omega) | (simp_all) | norm_num [stairAlZ]

set_option linter.unusedSimpArgs false in
lemma dv_bLs (j : ℕ) (hj : j < 45) : dv (bLsStair j) = (leadR j)⁻¹ := by
  simp only [dv, bLsStair, leadR]
  split_ifs <;> simp only [Prod.ext_iff, Fin.ext_iff, true_and, and_true] at * <;>
    first | (exfalso; omega) | (simp_all) | norm_num

/-! ## N6-2f — the projector and its corner -/

/-- The row factor: `diagonal dv * TmStair`; its rows at the anchors are exactly the family
vectors (`PmStair_apply` with `dv_aLs` and `TmStair_row`). -/
noncomputable def PmStair : Matrix (Pr 23) (Pr 23) ℚ := Matrix.diagonal dv * TmStair

/-- The column factor: `TiStair * diagonal dv⁻¹`; its columns at the anchors are exactly the
family vectors. -/
noncomputable def QmStair : Matrix (Pr 23) (Pr 23) ℚ :=
  TiStair * Matrix.diagonal fun u => (dv u)⁻¹

lemma PmStair_apply (a u : Pr 23) : PmStair a u = dv a * TmStair a u := by
  rw [PmStair, Matrix.diagonal_mul]

lemma QmStair_apply (v b : Pr 23) : QmStair v b = TiStair v b * (dv b)⁻¹ := by
  rw [QmStair, Matrix.mul_diagonal]

lemma diagonal_inv_mul_diagonal :
    (Matrix.diagonal fun u : Pr 23 => (dv u)⁻¹) * Matrix.diagonal dv = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun u : Pr 23 => (dv u)⁻¹ * dv u) = fun _ => (1 : ℚ) := by
    ext u; exact inv_mul_cancel₀ (dv_ne_zero u)
  rw [h, Matrix.diagonal_one]

/-- `QmStair * PmStair = 1` — the two factors are mutually inverse. -/
lemma QmStair_mul_PmStair : QmStair * PmStair = 1 := by
  rw [QmStair, PmStair, Matrix.mul_assoc,
    ← Matrix.mul_assoc (Matrix.diagonal fun u => (dv u)⁻¹) (Matrix.diagonal dv) TmStair,
    diagonal_inv_mul_diagonal, Matrix.one_mul, TiStair_TmStair]

/-- The staircase (R7) data-entrance projector: the exact analogue of r6's `qM`. -/
noncomputable def qMStair (M : Matrix (Pr 23) (Pr 23) ℚ) :
    Matrix (Fin (23 * 23)) (Fin (23 * 23)) ℚ :=
  (PmStair * M * QmStair).submatrix flagEquivStair flagEquivStair

set_option linter.unusedSimpArgs false in
/-- **`qM_corner`'s staircase analogue**: the top-right `45 × 45` corner of the staircase
projector IS the staircase frame `corStairQ` — the identity N2d measured FALSE for `qM`
(`n2d_frame_delta`: the two frames read different matrix entries). -/
theorem qMStair_corner (M : Matrix (Pr 23) (Pr 23) ℚ) (i j : ℕ) (hi : i < 45) (hj : j < 45) :
    qMStair M ⟨i, by have := two_k_le_23; omega⟩
      ⟨23 * 23 - 45 + j, by have := two_k_le_23; omega⟩ = corStairQ M i j := by
  unfold qMStair
  rw [submatrix_apply, flagEquivStair_top i hi, flagEquivStair_bot j hj, Matrix.mul_apply]
  simp only [Matrix.mul_apply, PmStair_apply, QmStair_apply, dv_aLs i hi, dv_bLs j hj, inv_inv]
  have hrow : ∀ u x, leadL i * TmStair (aLsStair i) u * M u x =
      sv (LtermsStair i) u * M u x := by
    intro u x; rw [TmStair_row i hi]
  have hcol : ∀ x, TiStair x (bLsStair j) * leadR j = sv (RtermsStair j) x := by
    intro x; rw [mul_comm, TiStair_col j hj]
  simp only [hrow, hcol]
  unfold corStairQ
  rw [show (∑ x, (∑ u, sv (LtermsStair i) u * M u x) * sv (RtermsStair j) x) =
      ∑ x, ((LtermsStair i).map fun s => s.1 * M s.2 x).sum * sv (RtermsStair j) x from
    Finset.sum_congr rfl fun x _ => by rw [n6_sum_sv_mul], n6_sum_mul_sv]

/-! ## N6-2g — the projector is an idempotent with `M`'s trace -/

lemma qMStair_mul (M M' : Matrix (Pr 23) (Pr 23) ℚ) :
    qMStair M * qMStair M' = qMStair (M * M') := by
  unfold qMStair
  rw [submatrix_mul_equiv]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc QmStair PmStair (M' * QmStair), QmStair_mul_PmStair, Matrix.one_mul]

lemma qMStair_idem {M : Matrix (Pr 23) (Pr 23) ℚ} (hM : M * M = M) :
    qMStair M * qMStair M = qMStair M := by
  rw [qMStair_mul, hM]

lemma qMStair_trace (M : Matrix (Pr 23) (Pr 23) ℚ) : (qMStair M).trace = M.trace := by
  unfold qMStair
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.submatrix_apply]
  have hs := Equiv.sum_comp flagEquivStair
    (fun u => (PmStair * M * QmStair : Matrix (Pr 23) (Pr 23) ℚ) u u)
  rw [hs]
  change (PmStair * M * QmStair).trace = M.trace
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle,
    Matrix.mul_assoc M QmStair PmStair, QmStair_mul_PmStair, Matrix.mul_one]

/-! ## N6-2h — the corner block, and the MIDDLE RUN in the new frame (N2d's open question) -/

/-- The top-right `45 × 45` corner block of the staircase projector is `stairCornerQOf M`. -/
lemma qMStair_cornerBlock (M : Matrix (Pr 23) (Pr 23) ℚ) :
    (qMStair M).submatrix
        (fun l : Fin 45 => (⟨l.val, by have := two_k_le_23; omega⟩ : Fin (23 * 23)))
        (fun r : Fin 45 =>
          (⟨23 * 23 - 45 + r.val, by have := two_k_le_23; omega⟩ : Fin (23 * 23))) =
      stairCornerQOf M := by
  ext l r
  rw [submatrix_apply, qMStair_corner M l.val r.val l.isLt r.isLt, stairCornerQOf, of_apply]

/-- **N6-3a — the 439 middle-run positions in the NEW frame.**  N2d left these open: they are
not decidable in the r6 frame (`isPiv_mid`'s invertible-corner hypothesis fails there, rank 44),
but in the staircase frame the corner IS invertible (`stairCornerQOf M`'s determinant is the
hypothesis; at the witness it is N3's `stair_data_cert`), so `Platform.isPiv_mid` applies and
every middle diagonal position `(i,i)`, `45 ≤ i < 484`, is a pivot of the staircase projector.
`hrank` is the r6 trace computation (`qM_trace`'s port): `trace M = (23-1)² = 484`. -/
theorem isPiv_stairMid (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (h₁ : y₁ ⬝ᵥ x₁ = 1) (h₂ : y₂ ⬝ᵥ x₂ = 1)
    (hdet : (stairCornerQOf ((1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂))).det ≠ 0) :
    ∀ i, 45 ≤ i → i < 484 →
      IsPiv (qMStair ((1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂))) i i := by
  intro i hi1 hi2
  have hk : 2 * 45 ≤ 529 := two_k_le_23
  set M := (1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂) with hMdef
  have hMM : M * M = M := by
    rw [hMdef, ← mul_kronecker_mul, DEPort.one_sub_vmv_idem x₁ y₁ h₁,
      DEPort.one_sub_vmv_idem x₂ y₂ h₂]
  have hq : qMStair M * qMStair M = qMStair M := qMStair_idem hMM
  have htr : M.trace = 484 := by
    rw [hMdef, trace_kronecker, DEPort.trace_one_sub_vmv x₁ y₁ h₁,
      DEPort.trace_one_sub_vmv x₂ y₂ h₂]
    norm_num
  have hrank : (qMStair M).rank = 529 - 45 := by
    have h1 := DEPort.rank_eq_trace (qMStair M) hq
    rw [qMStair_trace, htr] at h1
    have h2 : ((qMStair M).rank : ℚ) = ((529 - 45 : ℕ) : ℚ) := by rw [h1]; norm_num
    exact Nat.cast_injective h2
  have hC : ((qMStair M).submatrix (fun l : Fin 45 => (⟨l.val, by omega⟩ : Fin (23 * 23)))
      (fun r : Fin 45 =>
        (⟨529 - 45 + r.val, by omega⟩ : Fin (23 * 23)))).det ≠ 0 := by
    rw [qMStair_cornerBlock M]; exact hdet
  exact StaircasePort.Platform.isPiv_mid hk (qMStair M) hq hrank hC hi1 hi2


/-! #### the projector-level clause (N7 rewire contract) -/

/-- **N7 — the NE-block rank transfer at corner positions**: for `X ≤ 45`, `Y ≤ 45` the
NE-block of the staircase projector at `(X, 484 + Y)` IS the NE-block of the corner
(the rows `< X ≤ 45` and the cols `≥ 484 + Y` are corner rows/cols, and the entries
match by `qMStair_corner`). -/
lemma n7_rk_qm (M : Matrix (Pr 23) (Pr 23) ℚ) (X Y : ℕ) (hX : X ≤ 45) (hY : Y ≤ 45) :
    rk (qMStair M) X (484 + Y) = rk (stairCornerQOf M) X Y := by
  rw [rk, rk]
  have hE : ((qMStair M).submatrix (fun r : {r : Fin 529 // r.val < X} => r.1)
        (fun c : {c : Fin 529 // 484 + Y ≤ c.val} => c.1)
      = (stairCornerQOf M).submatrix (fun r : {r : Fin 45 // r.val < X} => r.1)
        (fun c : {c : Fin 45 // Y ≤ c.val} => c.1)).submatrix
        (fun i => (⟨⟨i.1.val, by omega⟩, by omega⟩ :
          {r : Fin 45 // r.val < X}))
        (fun c => (⟨⟨c.1.val - 484, by omega⟩, by omega⟩ :
          {c : Fin 45 // Y ≤ c.val})) := by
    ext i j
    simp only [Matrix.submatrix_apply, stairCornerQOf, Matrix.of_apply]
    rw [show (↑j.1 : ℕ) = 529 - 45 + (j.1.val - 484) from by have := j.2; omega,
      qMStair_corner M (↑i.1) (j.1.val - 484) (by have := i.2; omega)
        (by have := j.1.isLt; omega)]
  have hE' : ((stairCornerQOf M).submatrix (fun r : {r : Fin 45 // r.val < X} => r.1)
        (fun c : {c : Fin 45 // Y ≤ c.val} => c.1)
      = (qMStair M).submatrix (fun r : {r : Fin 529 // r.val < X} => r.1)
        (fun c : {c : Fin 529 // 484 + Y ≤ c.val} => c.1)).submatrix
        (fun r => (⟨⟨r.1.val, by omega⟩, by omega⟩ :
          {r : Fin 529 // r.val < X}))
        (fun c => (⟨⟨484 + c.1.val, by omega⟩, by omega⟩ :
          {c : Fin 529 // 484 + Y ≤ c.val})) := by
    ext i j
    simp only [Matrix.submatrix_apply, stairCornerQOf, Matrix.of_apply]
    rw [show (484 + ↑c.1 : ℕ) = 529 - 45 + c.1.val from by omega,
      qMStair_corner M (↑r.1.val) c.1.val (by have := r.2; omega) (by have := c.1.isLt; omega)]
  exact le_antisymm
    (by rw [hE]; exact Matrix.rank_submatrix_le _ _ _)
    (by rw [hE']; exact Matrix.rank_submatrix_le _ _ _)

/-- **N7 — the pivot transfer**: a corner pivot is a projector pivot at the shifted
column (the four NE-block ranks transfer by `n7_rk_qm`). -/
theorem n7_isPiv_transfer (M : Matrix (Pr 23) (Pr 23) ℚ) (i j : ℕ) (hi : i < 45)
    (hj : j < 45) (h : IsPiv (stairCornerQOf M) i j) :
    IsPiv (qMStair M) i (484 + j) := by
  unfold IsPiv at h ⊢
  rw [n7_rk_qm M (i + 1) j (by omega) (by omega),
    n7_rk_qm M i j (by omega) (by omega),
    n7_rk_qm M (i + 1) (j + 1) (by omega) (by omega),
    n7_rk_qm M i (j + 1) (by omega) (by omega)]
  exact h

/-- **N7 — `isPiv_stairCorner`: the 39-position CORNER CLAUSE on the staircase
projector** (the statement the N7 rewire consumes; global coordinates, corner runs
(1,507,21) and (25,486,18) of `stairDataRuns 23 529`).

Hypotheses (all dischargeable at the extracted witness — see
`isPiv_stairCorner_witness`): `hu`, `hv`, the 21 run-1 diagonal deviations `hT`,
`hM1` (top 25 corner rows independent on cols ≥ 20; witness: N2c cert 1), and `hM2`
(row `25+t` independent on cols ≥ `2+t` for `t < 18`; witness: N2c's 26-certs).
Note: `h₁`/`h₂` (`y·x = 1`) and `hdet` are NOT needed here — they are the middle-run's
fuel (`isPiv_stairMid`). -/
theorem isPiv_stairCorner (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hu : x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ ≠ 0)
    (hv : y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ (n7Fin l) * y₂ (n7Fin (l + 1))
        + stairRunB l * x₁ (n7Fin l) * y₁ (n7Fin (l + 1)) ≠ 0)
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
    rw [show 507 + k = 484 + (23 + k) from by omega]
    exact n7_isPiv_transfer _ _ _ (by omega)
      (n7_run1 x₁ y₁ x₂ y₂ hu hv hT (1 + k) (by omega) (by omega))
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    rw [show 486 + k = 484 + (2 + k) from by omega]
    exact n7_isPiv_transfer _ _ _ (by omega)
      (n7_run2 x₁ y₁ x₂ y₂ hM1 hM2 k hk)
  · exact absurd hr (by simp)

/-- **The 39 corner positions at the witness through the symbolic clause** — every
hypothesis discharged; the integration check for the N7 rewire. -/
theorem isPiv_stairCorner_witness :
    ∀ p ∈ runPairs [(1, 507, 21), (25, 486, 18)],
      IsPiv (qMStair (stairPairM stairQX1 stairQY1 stairQX2 stairQY2)) p.1 p.2 :=
  isPiv_stairCorner stairQX1 stairQY1 stairQX2 stairQY2 stair_hu stair_hv n7_hT_witness
    n7_hM1_witness n7_hM2_witness



end StaircasePort.Stair
