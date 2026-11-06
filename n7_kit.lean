import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Data
import StaircasePort.Cert
import StaircasePort.Pivot
import StaircasePort.Signature

set_option maxRecDepth 20000

namespace StaircasePort.Stair.N52Kit

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

/-! ## N7 toolkit — generic pivot/edge machinery (ported from the fetched platform bodies
ref/nb_data_edge_solution.lean + ref/nb_aux_edge_of_solution.lean, R6BitNBPiv/R6BitNBEdges). -/

section PivKit

variable {K : Type*} [Field K]

/-- Ported nb_aux_edge_of_solution.lean:31-40 (RunsLib.PSwapAux.rank_eq_of_range_rows). -/
lemma rank_eq_of_range_rows {m m' n : Type*} [Fintype m] [Fintype m'] [Fintype n]
    {A : Matrix m n K} {B : Matrix m' n K} (h : Set.range A.row = Set.range B.row) :
    A.rank = B.rank := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, h]

/-- Ported nb_aux_edge_of_solution.lean:41-48 (RunsLib.PSwapAux.rank_eq_of_range_cols). -/
lemma rank_eq_of_range_cols {m n n' : Type*} [Fintype m] [Fintype n] [Fintype n']
    {A : Matrix m n K} {B : Matrix m n' K} (h : Set.range A.col = Set.range B.col) :
    A.rank = B.rank := by
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols, h]

/-- Ported nb_aux_edge_of_solution.lean:131-141 (RunsLib.RunsAux.rank_submatrix_range). -/
lemma rank_submatrix_range {ι κ α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : Matrix ι κ K) (f : α → ι) (f' : β → ι) (g : γ → κ) (g' : δ → κ)
    (hf : Set.range f = Set.range f') (hg : Set.range g = Set.range g') :
    (A.submatrix f g).rank = (A.submatrix f' g').rank := by
  trans (A.submatrix f' g).rank
  · apply rank_eq_of_range_rows
    have h1 : (A.submatrix f g).row = (fun i c => A i (g c)) ∘ f := rfl
    have h2 : (A.submatrix f' g).row = (fun i c => A i (g c)) ∘ f' := rfl
    rw [h1, h2, Set.range_comp, Set.range_comp, hf]
  · apply rank_eq_of_range_cols
    have h1 : (A.submatrix f' g).col = (fun j r => A (f' r) j) ∘ g := rfl
    have h2 : (A.submatrix f' g').col = (fun j r => A (f' r) j) ∘ g' := rfl
    rw [h1, h2, Set.range_comp, Set.range_comp, hg]

/-- Ported nb_data_edge_solution.lean:109-114. -/
lemma rk_congr (q : Matrix (Fin a) (Fin b) K) {X X' Y Y' : ℕ}
    (hX : ∀ r : Fin a, r.val < X ↔ r.val < X') (hY : ∀ c : Fin b, Y ≤ c.val ↔ Y' ≤ c.val) :
    rk q X Y = rk q X' Y' := by
  unfold rk
  apply rank_submatrix_range
  · ext r; simp [hX]
  · ext c; simp [hY]

/-- Ported nb_data_edge_solution.lean:116-121. -/
lemma not_isPiv_of_le_row (q : Matrix (Fin a) (Fin b) K) {i : ℕ} (hi : a ≤ i) (j : ℕ) :
    ¬ IsPiv q i j := by
  unfold IsPiv
  have h1 : ∀ Y, rk q (i + 1) Y = rk q i Y := fun Y =>
    rk_congr q (fun r => by have := r.isLt; omega) (fun _ => Iff.rfl)
  rw [h1, h1]; omega

/-- Ported nb_data_edge_solution.lean:123-128. -/
lemma rk_zero_of_le_col (q : Matrix (Fin a) (Fin b) K) (X : ℕ) {Y : ℕ} (hY : b ≤ Y) :
    rk q X Y = 0 := by
  unfold rk
  apply Nat.eq_zero_of_le_zero
  refine (Matrix.rank_le_card_width _).trans ?_
  rw [Nat.le_zero, Fintype.card_eq_zero_iff]
  exact ⟨fun c => by have := c.1.isLt; have := c.2; omega⟩

/-- Ported nb_data_edge_solution.lean:130-135. -/
lemma not_isPiv_of_le_col (q : Matrix (Fin a) (Fin b) K) (i : ℕ) {j : ℕ} (hj : b ≤ j) :
    ¬ IsPiv q i j := by
  unfold IsPiv
  rw [rk_zero_of_le_col q _ hj, rk_zero_of_le_col q _ hj, rk_zero_of_le_col q _ (by omega),
    rk_zero_of_le_col q _ (by omega)]
  omega

/-- Ported nb_data_edge_solution.lean:156-161. -/
lemma isPiv_lt {q : Matrix (Fin a) (Fin b) K} {i j : ℕ} (h : IsPiv q i j) : i < a ∧ j < b := by
  by_contra hc
  rcases not_and_or.1 hc with h' | h'
  · exact not_isPiv_of_le_row q (by omega) j h
  · exact not_isPiv_of_le_col q i (by omega) h

/-- **NEW (N7)** — the rows `< X` / cols `≥ Y` submatrix of an upper-zero matrix is zero, so
its rank vanishes. Replaces the platform `isPiv_iff` route of isPiv_diag_of_lower (platform
body not fetched; this direct route covers exactly the instances the aux edge needs). -/
lemma rk_upper_zero {k : ℕ} (C : Matrix (Fin k) (Fin k) K)
    (hC : ∀ i j : Fin k, (i : ℕ) < (j : ℕ) → C i j = 0) {X Y : ℕ} (hXY : X ≤ Y) :
    rk C X Y = 0 := by
  unfold rk
  have h0 : (C.submatrix (fun r : {r : Fin k // r.val < X} => r.1)
      (fun c : {c : Fin k // Y ≤ c.val} => c.1)) = 0 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.zero_apply]
    exact hC i.1 j.1 (by have := i.2; have := j.2; omega)
  rw [h0, Matrix.rank_zero]

/-- **NEW (N7)** — the `(l+1, l)` subblock rank: rows `< l+1`, cols `≥ l` of an upper-zero
matrix with nonzero `(l,l)` entry has rank 1 (rows `< l` vanish; row `l` is nonzero). -/
lemma rk_diag_one {k : ℕ} (C : Matrix (Fin k) (Fin k) K)
    (hC : ∀ i j : Fin k, (i : ℕ) < (j : ℕ) → C i j = 0)
    (hd : ∀ i : Fin k, C i i ≠ 0) (l : Fin k) : rk C (l.val + 1) l.val = 1 := by
  have hlk : l.val < k := l.isLt
  unfold rk
  set B : Matrix {r : Fin k // r.val < l.val + 1} {c : Fin k // l.val ≤ c.val} K :=
    C.submatrix (fun r : {r : Fin k // r.val < l.val + 1} => r.1)
      (fun c : {c : Fin k // l.val ≤ c.val} => c.1) with hB
  have hrow : ∀ i : {r : Fin k // r.val < l.val + 1}, (i.1 : ℕ) < l.val → B i = 0 := by
    intro i hi
    ext j
    simp only [hB, Matrix.submatrix_apply]
    exact hC i.1 j.1 (by have := i.2; have := j.2; omega)
  have hwne : (B ⟨⟨l.val, hlk⟩, by simp⟩ : {c : Fin k // l.val ≤ c.val} → K) ≠ 0 := by
    intro h0
    have h2 : B ⟨⟨l.val, hlk⟩, by simp⟩ ⟨⟨l.val, hlk⟩, by simp⟩ =
        C ⟨l.val, hlk⟩ ⟨l.val, hlk⟩ := by
      simp only [hB, Matrix.submatrix_apply]
    rw [h0, Pi.zero_apply] at h2
    exact (hd ⟨l.val, hlk⟩) h2.symm
  have hspan : Submodule.span K (Set.range B.row) = K ∙ (B ⟨⟨l.val, hlk⟩, by simp⟩) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro x ⟨i, rfl⟩
      simp only [Matrix.row]
      rcases Nat.lt_or_ge (i.1 : ℕ) l.val with hi | hi
      · rw [hrow i hi]
        exact Submodule.zero_mem _
      · have hiEq : (i.1 : ℕ) = l.val := by have := i.2; omega
        have hi2 : i = ⟨⟨l.val, hlk⟩, by simp⟩ := Subtype.ext (Fin.ext hiEq)
        rw [hi2]
        exact Submodule.mem_span_singleton_self _
    · intro x hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨l.val, hlk⟩, by simp⟩, rfl⟩)
  rw [Matrix.rank_eq_finrank_span_row, hspan, finrank_span_singleton hwne]

/-- Ported nb_data_edge_solution.lean:196-215 (rk_block). -/
lemma rk_block {a b a' b' c0 : ℕ} (C : Matrix (Fin a) (Fin b) K) (B : Matrix (Fin a') (Fin b') K)
    (ha : a' ≤ a) (hb : c0 + b' = b)
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C ⟨i.val, lt_of_lt_of_le i.isLt ha⟩ ⟨c0 + j.val, by have := j.isLt; omega⟩)
    {X : ℕ} (hX : X ≤ a') (y : ℕ) : rk C X (c0 + y) = rk B X y := by
  unfold rk
  have e : B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
      (fun c : {c : Fin b' // y ≤ c.val} => c.1) =
      C.submatrix (fun r : {r : Fin a' // r.val < X} => (⟨r.1.val, lt_of_lt_of_le r.1.isLt ha⟩ : Fin a))
        (fun c : {c : Fin b' // y ≤ c.val} =>
          (⟨c0 + c.1.val, by have := c.1.isLt; omega⟩ : Fin b)) := by
    ext r c; simp [hCB]
  rw [e]
  apply rank_submatrix_range
  · ext x
    simp only [Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨x', hx', rfl⟩
      exact ⟨⟨x'.val, by omega⟩, hx', rfl⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨_, hx', rfl⟩
  · ext x
    simp only [Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨x', hx', rfl⟩
      refine ⟨⟨x'.val - c0, by have := x'.isLt; omega⟩, by simp only; omega, ?_⟩
      ext; simp only; omega
    · rintro ⟨x', hx', rfl⟩
      exact ⟨_, by simp only; omega, rfl⟩

/-- Ported nb_data_edge_solution.lean:217-228 (isPiv_block). -/
lemma isPiv_block {a b a' b' c0 : ℕ} (C : Matrix (Fin a) (Fin b) K) (B : Matrix (Fin a') (Fin b') K)
    (ha : a' ≤ a) (hb : c0 + b' = b)
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C ⟨i.val, lt_of_lt_of_le i.isLt ha⟩ ⟨c0 + j.val, by have := j.isLt; omega⟩)
    {i j : ℕ} (h : IsPiv B i j) : IsPiv C i (c0 + j) := by
  have hi := (isPiv_lt h).1
  unfold IsPiv at h ⊢
  rw [show c0 + j + 1 = c0 + (j + 1) by omega, rk_block C B ha hb hCB (X := i + 1) (by omega),
    rk_block C B ha hb hCB (X := i + 1) (by omega), rk_block C B ha hb hCB (X := i) (by omega),
    rk_block C B ha hb hCB (X := i) (by omega)]
  exact h

/-- **N7 direct port of nb_aux_edge_of_solution.lean:309-330** (isPiv_diag_of_lower): a lower
triangular matrix with nonzero diagonal pivots on its diagonal. The platform proof consumes
`isPiv_iff` (Bruhat factorization, body not fetched); this direct route computes the four rk
values at `(l, l)` from rk_upper_zero/rk_diag_one. -/
lemma isPiv_diag_of_lower [DecidableEq K] {k : ℕ} (C : Matrix (Fin k) (Fin k) K)
    (hC : ∀ i j : Fin k, (i : ℕ) < (j : ℕ) → C i j = 0) (hd : ∀ i : Fin k, C i i ≠ 0)
    (l : Fin k) : IsPiv C l.val l.val := by
  unfold IsPiv
  rw [rk_upper_zero C hC (X := l.val + 1) (Y := l.val + 1) (by omega),
    rk_upper_zero C hC (X := l.val) (Y := l.val) (by omega),
    rk_upper_zero C hC (X := l.val) (Y := l.val + 1) (by omega),
    rk_diag_one C hC hd l]


/-- Ported ref/nb_side_edge_of_solution.lean:92-95 (qM_fac). -/
lemma qM_fac (C : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (R : Matrix (Fin (19 + 4)) (Pr (19 + 4)) ℚ) :
    qM (C * A * R) = (Te (h := 19) * C) * A * (R * Te' (h := 19)) := by
  rw [qM_eq]; simp only [Matrix.mul_assoc]

/-- Ported nb_aux_edge_of_solution.lean:527-534 (edge_exact). -/
theorem edge_exact {m : ℕ} (hm : 1 < m) (q : Matrix (Fin m) (Fin m) ℚ) (hq : q * q = q)
    (rs : List (ℕ × ℕ × ℕ)) (hok : ∀ ρ ∈ rs, RunOK m ρ) (hnd : (runPairs rs).Nodup)
    (hp : ∀ x ∈ runPairs rs, IsPiv q x.1 x.2) (hlen : (runPairs rs).length = q.rank) :
    ∃ e : Edge m, EdgeQ e q ∧ e.runs = rs := by
  obtain ⟨e, he, rs', h1, -, h3⟩ := DEPort.edge_singles hm q hq rs hok hnd hp
  have : rs' = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst this
  exact ⟨e, he, by simpa using h1⟩

end PivKit


section Ports

/-! ## N7 stub ports — the r6-frame generic edges (bodies verbatim from the fetched platform
bodies, specialized to h = 19; these replace the `sorry` stubs `N52.aux_edge_of` and
`N52.side_edge_of` in Signature.lean). -/

/-- Ported ref/nb_aux_edge_of_solution.lean:561-631 (aux_edge_of_sol_aux at h = 19). -/
theorem aux_edge_of_port (M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) (hM : M * M = M)
    (htr : M.trace = ((19 + 4) * (19 + 3) : ℕ))
    (hlow : ∀ β γ : ℕ, β < γ → γ < 19 + 4 → cor M β (19 + 3 + γ) = 0)
    (hdiag : ∀ β : ℕ, β < 19 + 4 → cor M β (19 + 3 + β) ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM M) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  have hk := two_k_le (h := 19)
  have hmm : (19 + 4) * (19 + 4) = (19 + 4) * (19 + 3) + (19 + 4) := by ring
  have hq := qM_idem hM
  have hrank : (qM M).rank = (19 + 4) * (19 + 4) - (19 + 4) := by
    have h1 := rank_eq_trace (qM M) hq
    rw [qM_trace, htr] at h1
    have := Nat.cast_injective h1
    omega
  set Cp : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ := (qM M).submatrix
    (fun l : Fin (19 + 4) => (⟨l.val, by omega⟩ : Fin ((19 + 4) * (19 + 4))))
    (fun r : Fin (19 + 4) => (⟨(19 + 4) * (19 + 4) - (19 + 4) + r.val, by omega⟩ :
      Fin ((19 + 4) * (19 + 4)))) with hCp
  have hCe : ∀ β γ : Fin (19 + 4), Cp β γ = cor M β.val (19 + 3 + γ.val) := by
    intro β γ
    have e : (⟨(19 + 4) * (19 + 4) - (19 + 4) + γ.val, by omega⟩ : Fin ((19 + 4) * (19 + 4))) =
        ⟨(19 + 4) * (19 + 4) - (2 * 19 + 7) + (19 + 3 + γ.val), by omega⟩ :=
      Fin.ext (by simp only; omega)
    rw [hCp, submatrix_apply, e, ← qM_corner M β.val (19 + 3 + γ.val) (by omega) (by omega)]
  have hCl : ∀ β γ : Fin (19 + 4), β < γ → Cp β γ = 0 := fun β γ hβγ => by
    rw [hCe]; exact hlow _ _ hβγ γ.isLt
  have hCd : ∀ β : Fin (19 + 4), Cp β β ≠ 0 := fun β => by rw [hCe]; exact hdiag _ β.isLt
  have hdet : Cp.det ≠ 0 := by
    rw [det_of_isLowerTriangular Cp (fun a b hab => hCl a b hab)]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hCd a
  have hmid := fun i (h1 : 19 + 4 ≤ i) (h2 : i < (19 + 4) * (19 + 4) - (19 + 4)) =>
    isPiv_mid (k := 19 + 4) (by omega) (qM M) hq hrank hdet h1 h2
  have hcorner : ∀ l : Fin (19 + 4), IsPiv (qM M) l.val ((19 + 4) * (19 + 4) - (19 + 4) + l.val) :=
    fun l => isPiv_block (qM M) Cp (by omega) (by omega) (fun i j => rfl)
      (isPiv_diag_of_lower Cp hCl hCd l)
  refine edge_exact (by omega) (qM M) hq _ ?_ ?_ ?_ ?_
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
    omega

/-- Ported ref/nb_side_edge_of_solution.lean:175-218 (side_edge_of_sol_aux at h = 19). -/
theorem side_edge_of_port (C : Matrix (Pr (19 + 4)) (Fin (19 + 4)) ℚ)
    (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (R : Matrix (Fin (19 + 4)) (Pr (19 + 4)) ℚ)
    (hB : ∀ i j : Fin (19 + 4), i < j →
      (Te (h := 19) * C) ⟨i.val, by have := two_k_le (h := 19); omega⟩ j = 0)
    (hBd : ∀ i : Fin (19 + 4),
      (Te (h := 19) * C) ⟨i.val, by have := two_k_le (h := 19); omega⟩ i ≠ 0)
    (hA : ∀ i j : Fin (19 + 4), i < j → (R * Te' (h := 19)) i
      ⟨(19 + 4) * (19 + 4) - (19 + 4) + j.val, by have := two_k_le (h := 19); omega⟩ = 0)
    (hAd : ∀ i : Fin (19 + 4), (R * Te' (h := 19)) i
      ⟨(19 + 4) * (19 + 4) - (19 + 4) + i.val, by have := two_k_le (h := 19); omega⟩ ≠ 0)
    (hM : C * A * R * (C * A * R) = C * A * R) (hAA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (hrM : (qM (C * A * R)).rank = r)
    (hcor : 19 + 4 < 2 * r →
      (A.submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
        (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ :
          Fin (19 + 4)))).det ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM (C * A * R)) ∧ ∃ rs',
      e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length = r := by
  have hk := two_k_le (h := 19)
  have hq : qM (C * A * R) * qM (C * A * R) = qM (C * A * R) := qM_idem hM
  have hrn : r ≤ 19 + 4 := hr ▸ rank_le_width A |>.trans (by simp)
  obtain ⟨e, he, rs', h1, h2, h3⟩ : ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM (C * A * R)) ∧
      ∃ rs', e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length =
        (qM (C * A * R)).rank := by
    refine DEPort.edge_singles (by nlinarith) _ hq _ ?_ ?_ ?_
    · intro ρ hρ
      unfold sideRuns at hρ
      split_ifs at hρ with hr2
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
        subst hρ
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only <;> omega
      · simp at hρ
    · unfold sideRuns
      split_ifs
      · rw [DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil]
        exact DEPort.nodup_run _ _ _
      · exact List.nodup_nil
    · intro p hp
      unfold sideRuns at hp
      split_ifs at hp with hr2
      · rw [DEPort.runPairs_cons, DEPort.runPairs_nil, List.append_nil, DEPort.mem_run] at hp
        obtain ⟨t, ht, rfl⟩ := hp
        have hpiv : IsPiv A (19 + 4 - r + t) (19 + 4 - r + t) :=
          isPiv_mid (m := 19 + 4) (k := 19 + 4 - r) (by omega) A hAA (by omega) (hcor hr2)
            (by omega) (by omega)
        have his := isPiv_side (by nlinarith) (Te (h := 19) * C) A (R * Te' (h := 19)) hB hBd hA hAd
          hpiv
        rw [qM_fac]
        have key : (19 + 4) * (19 + 4) - r + t =
            (19 + 4) * (19 + 4) - (19 + 4) + (19 + 4 - r + t) := by
          generalize (19 + 4) * (19 + 4) = M2 at hk ⊢; omega
        rw [key]; exact his
      · rw [DEPort.runPairs_nil] at hp; simp at hp
  exact ⟨e, he, rs', h1, h2, h3.trans hrM⟩

end Ports

end StaircasePort.Stair.N52Kit
