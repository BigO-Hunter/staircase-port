/-
# N2 — the staircase-B pivot lemmas (the only new math) + platform restatements

## Platform restatements (verbatim formal_statements fetched 2026-11-04 from prove2.me
search results, extract/statements/pivot_statements.lean; all status Proved):
* `isPiv_rank1_lower` — e90110dd-d54a-4a36-8bd0-607e7517918e
* `isPiv_mid` — 06f02169-dc57-49b7-bc3b-9d78025b9214
* `edge_of_pivs` — f66c9619-b320-4663-99d3-50c9a27fbcd2
* `isPiv_side` — ef7049d3-13bf-4740-82a1-71225465f744
Restated in namespace `StaircasePort.Platform` so this skeleton builds WITHOUT the platform
Theorems stack; at submission time these sorries are replaced by imports of the platform
children (Thm_IntMul_Kappa_R6_Bit_NB_* — same statements, Proved bodies).
`isPiv_rank1_lower`'s rank-one hypothesis (hB) is FALSE for the staircase corner
(REPORT.md FLAGBASIS BODY VERDICT: nb_data_edge_solution.lean:536-552 is THE one
corner-touching step) — hence the new staircase lemmas below.

## The new lemmas (Lean mirror of check_stair.py items 2-3, certified green on this machine
2026-11-04 with discriminating --control negative: RESULT h=23 kind=stair runs=[21,18,1⁶]
certified=True; 689 nontrivial NE blocks, cut ≥ evaluated rank on all):
* N2a `rank_le_support_cut` — generic NE-rank upper bound via row/col/term-support
  factorization (the rank-toolkit route; min-cut itself is NOT formalized — the cut VALUES
  are extracted data, stairNEBlocks).
* N2b `stairNE_rk_le` — instantiation: every extracted nontrivial NE block of the symbolic
  staircase corner obeys its cut bound (check_stair item 2, "identically in all
  parameters": cut sizes depend only on the RC/CC supports, and the extracted family
  coefficients are nonzero).
* N2c `stairCorner_pivots_witness` — lower bound at the extracted witness: the rightmost
  pivot pattern pc (staircase_data.json) makes all 45 corner pivots IsPiv
  (check_stair item 3; single pivot pattern over 20 sampled pairs, invertible).
* N2d `isPiv_stair_lower` — the drop-in generalization consumed by data_edge_stair (N5):
  all 478 run positions of stairDataRuns are IsPiv of qM M. Combines isPiv_mid (middle
  439-run — GENERIC, needs only hdet; platform-Proved) + the corner transfer (isPiv_block,
  PROVED with full proof at nb_data_edge_solution.lean:227-238, ports verbatim) + N2b/N2c
  lifted from the witness to generic labels by the flag_gen Zariski/Pall mechanism
  (nb_flag_gen_solution.lean:977-993 exists_eval_ne).

Proof-route summary and fallback (max-flow formalization, +weeks) in SCAFFOLD.md §N2.
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.Data
import StaircasePort.Cert
import StaircasePort.NEBlocks

namespace StaircasePort

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

/-! ## Platform restatements (verbatim; see header) -/

namespace Platform

variable {K : Type*} [Field K]

/-- Verbatim formal_statement of platform theorem IntMul.Kappa.R6.Bit.NB.isPiv_rank1_lower
(e90110dd, Proved). Its rank-one hyp hB FAILS for the staircase B — this restatement is the
signature N2 generalizes (SCAFFOLD.md). -/
theorem isPiv_rank1_lower {a b : ℕ} (B : Matrix (Fin a) (Fin b) K) (u : Fin a → K)
    (v : Fin b → K)
    (hB : ∀ (i : Fin a) (j : Fin b), i.val < j.val → B i j = u i * v j)
    (h0 : 0 < a) (hb : 0 < b) (hu : u ⟨0, h0⟩ ≠ 0) (hv : v ⟨b - 1, by omega⟩ ≠ 0)
    (l : ℕ) (hl1 : 1 ≤ l) (hla : l < a) (hlb : l + 1 < b)
    (hT : B ⟨l, hla⟩ ⟨l, by omega⟩ ≠ u ⟨l, hla⟩ * v ⟨l, by omega⟩) : IsPiv B l l := by sorry

/-- Verbatim formal_statement of platform theorem IntMul.Kappa.R6.Bit.NB.isPiv_mid
(06f02169, Proved). GENERIC — the staircase reuses it unchanged for the middle-block run
(45,45,439): needs only k = 45, rank = m − k, and corner det ≠ 0 (stair_data_cert, N3). -/
theorem isPiv_mid {m k : ℕ} (hk : 2 * k ≤ m) (p : Matrix (Fin m) (Fin m) K) (hp : p * p = p)
    (hrank : p.rank = m - k)
    (hC : (p.submatrix (fun l : Fin k => (⟨l.val, by omega⟩ : Fin m))
        (fun r : Fin k => (⟨m - k + r.val, by omega⟩ : Fin m))).det ≠ 0)
    {i : ℕ} (hi1 : k ≤ i) (hi2 : i < m - k) : IsPiv p i i := by sorry

/-- Verbatim formal_statement of platform theorem IntMul.Kappa.R6.Bit.NB.edge_of_pivs
(f66c9619, Proved). GENERIC — consumes the 478 IsPiv positions (N2d) and returns the edge
with rs' singletons, |rs| + |rs'| = rank ⇒ rs'.length = 6 with stairDataRuns (478 + 6 = 484,
Data.lean stair_pivot_budget). -/
theorem edge_of_pivs {m : ℕ} (hm : 1 < m) (q : Matrix (Fin m) (Fin m) ℚ) (hq : q * q = q)
    (rs : List (ℕ × ℕ × ℕ)) (hok : ∀ ρ ∈ rs, RunOK m ρ) (hnd : (runPairs rs).Nodup)
    (hp : ∀ x ∈ runPairs rs, IsPiv q x.1 x.2) :
    ∃ e : Edge m, (∃ rs', e.runs = rs ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
        (runPairs rs).length + rs'.length = q.rank) ∧
      (∀ ρ ∈ e.runs, RunOK m ρ) ∧
      (∀ i j, i < j → e.E₁ i j = 0) ∧ (∀ i, e.E₁ i i ≠ 0) ∧
      (∀ i j, i < j → e.E₂ i j = 0) ∧ (∀ i, e.E₂ i i ≠ 0) ∧
      e.E₁ * ((e.runs.flatMap (runPiv m)).map fun p => Equiv.swap p.1 p.2).prod.permMatrix ℚ *
        e.E₂ = pswQ q := by sorry

/-- Verbatim formal_statement of platform theorem IntMul.Kappa.R6.Bit.NB.isPiv_side
(ef7049d3, Proved). GENERIC — the staircase per-slot corner ranks flow through the
rank-parameterized SideE unchanged (REPORT.md §2 of PORTABILITY PROBE). -/
theorem isPiv_side {m n : ℕ} (hnm : n ≤ m) (Bm : Matrix (Fin m) (Fin n) K)
    (M : Matrix (Fin n) (Fin n) K) (Am : Matrix (Fin n) (Fin m) K)
    (hB : ∀ i j : Fin n, i < j → Bm ⟨i.val, by omega⟩ j = 0)
    (hBd : ∀ i : Fin n, Bm ⟨i.val, by omega⟩ i ≠ 0)
    (hA : ∀ i j : Fin n, i < j → Am i ⟨m - n + j.val, by omega⟩ = 0)
    (hAd : ∀ i : Fin n, Am i ⟨m - n + i.val, by omega⟩ ≠ 0)
    {i j : ℕ} (h : IsPiv M i j) : IsPiv (Bm * M * Am) i (m - n + j) := by sorry

end Platform

/-! ## N2: the staircase pivot lemmas -/

namespace Stair

/-! ### N2a rank-toolkit helpers

Matrix-level rank lemmas missing from Mathlib d13f23b7 (rank subadditivity lives there only
for `LinearMap`). The row/col-cardinality bounds themselves are Mathlib-native
(`Matrix.rank_le_card_of_support_subset`, `Matrix.rank_transpose`); the ported
nb_data_edge_solution.lean:26-30/:83 toolkit (rank_eq_of_range_rows/cols, rank_submatrix_range)
turns out NOT to be needed for N2a and its single carrier stays in sp-n51's DEPort (merge
hygiene — no duplicate port here). -/

namespace RankKit

variable {K : Type*} [Field K]

/-- Rank subadditivity for matrices (Mathlib d13f23b7 has only the `LinearMap` version). -/
lemma rank_add_le {ι κ : Type*} [Fintype ι] [Fintype κ] (A B : Matrix ι κ K) :
    (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank_eq_finrank_span_row (A + B), Matrix.rank_eq_finrank_span_row A,
    Matrix.rank_eq_finrank_span_row B]
  refine (Submodule.finrank_mono (Submodule.span_le.mpr ?_)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  intro c hc
  obtain ⟨r, hr⟩ := hc
  rw [← hr]
  have hrow : (A + B).row r = A.row r + B.row r := rfl
  rw [hrow]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨r, rfl⟩) (Submodule.subset_span ⟨r, rfl⟩)

/-- The rank of a Finset sum of matrices is at most the sum of the ranks. -/
lemma rank_sum_le {ι κ τ : Type*} [Fintype ι] [Fintype κ] [DecidableEq τ]
    (s : Finset τ) (M : τ → Matrix ι κ K) :
    (∑ t ∈ s, M t).rank ≤ ∑ t ∈ s, (M t).rank := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Matrix.rank_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (rank_add_le _ _).trans (add_le_add le_rfl ih)

/-- A Finset filter on `ι` whose predicate pushes injectively into `S` has card ≤ |S|. -/
lemma card_filter_le_of_injective {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (p : ι → Prop) [DecidablePred p] (S : Finset α) (f : ι → α) (hf : Function.Injective f)
    (hS : ∀ r, p r → f r ∈ S) :
    ((Finset.univ : Finset ι).filter p).card ≤ S.card := by
  have him : (((Finset.univ : Finset ι).filter p).image f).card =
      ((Finset.univ : Finset ι).filter p).card := Finset.card_image_of_injective _ hf
  rw [← him]
  refine Finset.card_le_card ?_
  intro x hx
  obtain ⟨r, hr, e⟩ := Finset.mem_image.mp hx
  rw [← e]
  exact hS r (Finset.mem_filter.mp hr).2

/-- Rank ≤ |R| when every row outside `R` (pulled back along an injection `f`) vanishes —
the "rows factor through a row-support set" bound. -/
lemma rank_le_card_row_support {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq α] (R : Finset α) (f : ι → α) (hf : Function.Injective f)
    (B : Matrix ι κ K) (hB : ∀ r, f r ∉ R → B r = 0) : B.rank ≤ R.card := by
  refine (Matrix.rank_le_card_of_support_subset B
    ((Finset.univ : Finset ι).filter fun r => f r ∈ R) ?sup).trans ?card
  · rw [Function.support_subset_iff']
    intro r hr
    show B r = 0
    exact hB r fun h => hr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ r, h⟩))
  · exact card_filter_le_of_injective (fun r => f r ∈ R) R f hf fun _ h => h

/-- Rank ≤ |C| when every column outside `C` vanishes (transpose of the row version). -/
lemma rank_le_card_col_support {ι κ α : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [DecidableEq α] (C : Finset α) (g : κ → α) (hg : Function.Injective g)
    (B : Matrix ι κ K) (hB : ∀ c, g c ∉ C → ∀ r, B r c = 0) : B.rank ≤ C.card := by
  rw [← Matrix.rank_transpose]
  refine rank_le_card_row_support C g hg Bᵀ ?_
  intro c hc
  ext r
  rw [Matrix.transpose_apply, Pi.zero_apply]
  exact hB c hc r

end RankKit

/-- **N2a** — the generic NE-rank upper bound via row/col/term-support factorization: the
Lean formalization of check_stair.py's `cut_bound` certificate (:57-90). The NE block
`rk A X Y` is a sum of TERM matrices `M t` (`hsum` — in the application, the shared-parameter
groups of check_stair.structure :42-54, each a scalar times a rank-one cell pattern); a
vertex cut of the rows-terms-cols graph is supplied as data `(R₀, C₀, T₀)`, and `hcut` is
exactly cut_bound's certificate loop ("cut misses a term", :86-89): every term outside T₀
has all of its block rows inside R₀, or all of its block columns inside C₀. Splitting the
term sum along the cut then gives `rk ≤ |R₀| + |C₀| + |T₀|`: the R₀-row-supported part
factors through R₀ rows (`RankKit.rank_le_card_row_support`), the C₀-part likewise via
`Matrix.rank_transpose`, and the T₀-part is a sum of |T₀| rank-≤-1 matrices
(`RankKit.rank_sum_le`). The min-cut COMPUTATION stays offline: cut values (and for N2b the
cut SETS) are extracted data, never computed here.

SHAPE NOTE (2026-11-05, N2a agent): this replaces the scaffold's entry-level hypotheses
(`hcover`/`hrank1` quantifying over CELLS) with the term-level shape above — the structure
cut_bound's certificate actually produces, and the one N2b consumes. The entry-level form is
ill-posed under multi-coverage: it would assert `A r c = u t r * v t c` for EVERY cut term
`t` covering cell `(r, c)`, while a doubly-covered cell's value is the SUM of the covering
terms' contributions — forcing every other contribution to vanish on overlaps, a side
condition the term-level form never needs. Truth of the entry-level form for k ≥ 4 terms was
not established; the term-level bound below is the honest, sufficient version (weaker
hypotheses on the data, same conclusion, same genericity in `A`/dimensions). -/
theorem rank_le_support_cut {K : Type*} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) (R₀ : Finset (Fin a)) (C₀ : Finset (Fin b))
    {τ : Type*} [Fintype τ] [DecidableEq τ] (T₀ : Finset τ)
    (M : τ → Matrix {r : Fin a // r.val < X} {c : Fin b // Y ≤ c.val} K)
    (hsum : A.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1) = ∑ t, M t)
    (hcut : ∀ t ∉ T₀, (∀ r, r.1 ∉ R₀ → M t r = 0) ∨ (∀ c, c.1 ∉ C₀ → ∀ r, M t r c = 0))
    (hrank1 : ∀ t ∈ T₀, (M t).rank ≤ 1) :
    rk A X Y ≤ R₀.card + C₀.card + T₀.card := by
  classical
  show (A.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
    (fun c : {c : Fin b // Y ≤ c.val} => c.1)).rank ≤ R₀.card + C₀.card + T₀.card
  rw [hsum]
  -- split the term sum along the cut: T₀ / row-supported / col-supported
  let Sc : Finset τ := Finset.univ \ T₀
  let pRow : τ → Prop :=
    fun t => ∀ (r : {r : Fin a // r.val < X}), (r : Fin a) ∉ R₀ → M t r = 0
  let Srow : Finset τ := Sc.filter pRow
  let Scol : Finset τ := Sc \ Srow
  have memSrow (t : τ) : t ∈ Srow ↔ t ∈ Sc ∧ pRow t := Finset.mem_filter
  have hsplit : ∑ t, M t = ∑ t ∈ T₀, M t + (∑ t ∈ Srow, M t + ∑ t ∈ Scol, M t) := by
    have hd : Disjoint T₀ Sc :=
      Finset.disjoint_left.mpr fun t ht hs => (Finset.mem_sdiff.mp hs).2 ht
    have hu : T₀ ∪ Sc = Finset.univ := by
      ext t
      by_cases h : t ∈ T₀ <;> simp [Sc, h]
    have hcd : Disjoint Srow Scol :=
      Finset.disjoint_left.mpr fun t ht hs => (Finset.mem_sdiff.mp hs).2 ht
    have hcu : Srow ∪ Scol = Sc := by
      ext t
      constructor
      · intro h1
        rcases Finset.mem_union.mp h1 with h2 | h2
        · exact ((memSrow t).mp h2).1
        · exact (Finset.mem_sdiff.mp h2).1
      · intro h1
        by_cases h2 : t ∈ Srow
        · exact Finset.mem_union.mpr (Or.inl h2)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨h1, h2⟩))
    calc ∑ t, M t = ∑ t ∈ T₀ ∪ Sc, M t := by rw [← hu]
      _ = ∑ t ∈ T₀, M t + ∑ t ∈ Sc, M t := Finset.sum_union hd
      _ = ∑ t ∈ T₀, M t + (∑ t ∈ Srow, M t + ∑ t ∈ Scol, M t) := by
        rw [← hcu, Finset.sum_union hcd]
  rw [hsplit]
  have hN : (∑ t ∈ T₀, M t).rank ≤ T₀.card :=
    (RankKit.rank_sum_le T₀ M).trans
      ((Finset.sum_le_sum fun t ht => hrank1 t ht).trans
        (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id])))
  have hP : (∑ t ∈ Srow, M t).rank ≤ R₀.card :=
    RankKit.rank_le_card_row_support R₀ Subtype.val Subtype.val_injective _
      (fun r hr => (Finset.sum_apply r Srow M).trans
        (Finset.sum_eq_zero fun t ht => ((memSrow t).mp ht).2 r hr))
  have hQ : (∑ t ∈ Scol, M t).rank ≤ C₀.card :=
    RankKit.rank_le_card_col_support C₀ Subtype.val Subtype.val_injective _
      (fun c hc r =>
        (congrFun (Finset.sum_apply r Scol M) c).trans
          ((Finset.sum_apply c Scol fun t => M t r).trans
            (Finset.sum_eq_zero fun t ht => by
              have htS : t ∈ Sc \ Srow := ht
              have htSc : t ∈ Sc := (Finset.mem_sdiff.mp htS).1
              have htSrow : t ∉ Srow := (Finset.mem_sdiff.mp htS).2
              have htT : t ∉ T₀ := (Finset.mem_sdiff.mp htSc).2
              rcases hcut t htT with hrow | hcol
              · exact absurd ((memSrow t).mpr ⟨htSc, hrow⟩) htSrow
              · exact hcol c hc r)))
  calc ((∑ t ∈ T₀, M t) + (∑ t ∈ Srow, M t + ∑ t ∈ Scol, M t)).rank
      ≤ (∑ t ∈ T₀, M t).rank + (∑ t ∈ Srow, M t + ∑ t ∈ Scol, M t).rank :=
        RankKit.rank_add_le _ _
    _ ≤ (∑ t ∈ T₀, M t).rank + ((∑ t ∈ Srow, M t).rank + (∑ t ∈ Scol, M t).rank) :=
        add_le_add le_rfl (RankKit.rank_add_le _ _)
    _ ≤ R₀.card + C₀.card + T₀.card := by omega

/-! ### N2b — the blockwise NE-rank upper bound

STATEMENT SHAPE (2026-11-05, N2b): the scaffolded form `∀ M, rk (stairCornerQOf M) (i+1) j ≤ cut`
is FALSE for an arbitrary `M` — `corStairQ M` is only BILINEAR in `M`, so at block (1,24)
(cut = 1) the two block rows read disjoint sets of `M`-cells and a 2x2 identity minor gives
rank 2 (explicit witness in RESCUE_RESUME.md, verified independently in
extract/verify_n2b_statement.py). The bound holds identically in the LABELS for the PAIR
MATRIX `stairPairM x₁ y₁ x₂ y₂ = (1 - x₁y₁) ⊗ₖ (1 - x₂y₂)` — exactly the matrix N2c/N2d
consume. The proved theorem is `stairNE_rk_le` below (no sorry). -/




/-- **N2d — THE new lemma** (generalizes isPiv_rank1_lower's role at
nb_data_edge_solution.lean:536-552 hcorner): every run position of stairDataRuns 23 529 —
the unchanged middle-block run (45,45,439) AND both staircase corner runs (1,507,21),
(25,486,18) — is an IsPiv of the data-entrance projector qM M.
Route: middle run via Platform.isPiv_mid (generic; hrank = 484 by the trace computation of
nb_data_edge_solution.lean:521-531, ports verbatim; hdet = stair_data_cert for the witness,
generic labels via flag_gen Zariski); corner runs via N2c at the witness, transferred to
qM M's corner by isPiv_block (PROVED, nb_data_edge_solution.lean:227-238, ports verbatim:
Cp i j = cor M i j identity :534-537 restated with corStairQ), then witness → generic
labels by the flag_gen Pall/exists_eval_ne product structure
(nb_flag_gen_solution.lean:977-993; nonvanishing factors = N4 + hdet).

**REFUTED (N2d, 2026-11-05) — this statement is FALSE as written.** The `hdet` below is
the STAIRCASE-frame corner, but the corner of `qM M` is the R6 frame (`qM_corner`), and at
the extracted staircase witness all hypotheses hold while 18 of the 39 claimed corner
positions are not pivots (`n2d_refute.py`; the frame divergence is `n2d_frame_delta` at
the end of this namespace, and `n2d_qm_corner_check.py` reproduces the actual corner of
`qM stairMQ` independently). Consumers must not apply this theorem: see the "## N2d — THE
FRAME DELTA" block at the end of `namespace Stair`. The statement is deliberately left
byte-identical (the consumer arity/argument positions are right; only its truth is not). -/
theorem isPiv_stair_lower (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (h₁ : y₁ ⬝ᵥ x₁ = 1) (h₂ : y₂ ⬝ᵥ x₂ = 1)
    (hu : x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ ≠ 0)
    (hv : y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l (hl1 : 1 ≤ l) (hl2 : l ≤ 21),
      x₁ ⟨l, by omega⟩ * y₁ ⟨22, by omega⟩ + x₂ ⟨l, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hdet : (stairCornerQOf ((1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂))).det ≠ 0) :
    ∀ p ∈ runPairs (stairDataRuns 23 529),
      IsPiv (qM ((1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂))) p.1 p.2 := by sorry

set_option maxHeartbeats 0

/-! ## P1: generic List.sum helpers (GREEN pre-wipe) -/

lemma List.sum_map_add {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map fun s => f s + g s).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; abel

lemma List.sum_map_sub {α : Type*} (l : List α) (f g : α → ℚ) :
    (l.map fun s => f s - g s).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma List.sum_map_mul_right {α : Type*} (l : List α) (f : α → ℚ) (c : ℚ) :
    (l.map fun s => f s * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih]; rw [add_mul]

lemma List.sum_map_ite_eq_zero {α γ : Type*} [DecidableEq γ] (l : List α)
    (c : α → γ) (f : α → ℚ) (n : γ) (h : n ∉ l.map c) :
    (l.map fun s => if c s = n then f s else 0).sum = 0 := by
  induction l with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    simp only [List.mem_cons, not_or] at h
    rw [if_neg (Ne.symm h.1), ih h.2, add_zero]

/-- The regrouping lemma: Σ_t Σ_s [k₁ s = k₂ t]·f s·g t = Σ_c (Σ_{s: k₁s=c} f)(Σ_{t: k₂t=c} g). -/
lemma List.sum_sum_ite_eq_group {α β γ : Type*} [Fintype γ] [DecidableEq γ]
    (lR : List β) (lL : List α) (f : α → ℚ) (g : β → ℚ) (k₁ : α → γ) (k₂ : β → γ) :
    (lR.map fun t => (lL.map fun s => if k₁ s = k₂ t then f s * g t else (0 : ℚ)).sum).sum
    = ∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
        (lR.map fun t => if k₂ t = c then g t else 0).sum := by
  induction lR with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    have head_eq : (lL.map fun s => if k₁ s = k₂ t then f s * g t else 0).sum
        = (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t := by
      have hmap : lL.map (fun s => if k₁ s = k₂ t then f s * g t else 0)
          = lL.map (fun s => (if k₁ s = k₂ t then f s else 0) * g t) := by
        congr 1; funext s; split_ifs <;> ring
      rw [hmap, List.sum_map_mul_right]
    have key : ∑ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
          (if k₂ t = c then g t else 0)
        = (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t := by
      have hcong : ∀ c : γ, (lL.map fun s => if k₁ s = c then f s else 0).sum *
            (if k₂ t = c then g t else 0)
          = if k₂ t = c then (lL.map fun s => if k₁ s = k₂ t then f s else 0).sum * g t else 0 := by
        intro c
        split_ifs with h
        · rw [← h]
        · ring
      rw [Finset.sum_congr rfl (fun c _ => hcong c)]
      exact Fintype.sum_ite_eq (k₂ t) _
    rw [head_eq, ih]
    simp only [mul_add]
    rw [Finset.sum_add_distrib, key]

/-- Product-of-sums: Σ_t Σ_s f s · g t = (Σ_s f s)·(Σ_t g t). (GREEN pre-wipe) -/
lemma List.sum_sum_mul {α β : Type*} (lR : List β) (lL : List α) (f : α → ℚ) (g : β → ℚ) :
    (lR.map fun t => (lL.map fun s => f s * g t).sum).sum = (lL.map f).sum * (lR.map g).sum := by
  induction lR with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [List.sum_map_mul_right, ih, mul_add]

/-! ## P2: definitions, disjointness, coherence pins, vanishing (Nat-indexed rework;
the Fin-23-indexed predecessor ran GREEN pre-wipe; this rework NOT yet run) -/

/-- The pair matrix of the four label vectors (N2b's honest hypothesis shape — the
scaffold's arbitrary-M statement is FALSE, see RESUME.md counterexample). -/
noncomputable def stairPairM (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) : Matrix (Pr 23) (Pr 23) ℚ :=
  (1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂)

/-- Label-free Nat coordinate lists of the family cells. -/
def stairLfstN (i : ℕ) : List ℕ := (LtermsStair i).map fun s => (s.2.1 : ℕ)
def stairLsndN (i : ℕ) : List ℕ := (LtermsStair i).map fun s => (s.2.2 : ℕ)
def stairRfstN (j : ℕ) : List ℕ := (RtermsStair j).map fun s => (s.2.1 : ℕ)
def stairRsndN (j : ℕ) : List ℕ := (RtermsStair j).map fun s => (s.2.2 : ℕ)
def stairLcellN (i : ℕ) : List (ℕ × ℕ) :=
  (LtermsStair i).map fun s => ((s.2.1 : ℕ), (s.2.2 : ℕ))
def stairRcellN (j : ℕ) : List (ℕ × ℕ) :=
  (RtermsStair j).map fun s => ((s.2.1 : ℕ), (s.2.2 : ℕ))

/-- The l-group factors (shared SECOND coordinate l). Nat group index (matches the
pinned stairLsndN/stairRsndN data form). -/
noncomputable def stairUl (x₁ : Fin 23 → ℚ) (l i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => if (s.2.2 : ℕ) = l then s.1 * x₁ s.2.1 else 0).sum
noncomputable def stairVl (y₁ : Fin 23 → ℚ) (l j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => if (s.2.2 : ℕ) = l then s.1 * y₁ s.2.1 else 0).sum

/-- The k-group factors (shared FIRST coordinate k). -/
noncomputable def stairUk (x₂ : Fin 23 → ℚ) (k i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => if (s.2.1 : ℕ) = k then s.1 * x₂ s.2.2 else 0).sum
noncomputable def stairVk (y₂ : Fin 23 → ℚ) (k j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => if (s.2.1 : ℕ) = k then s.1 * y₂ s.2.2 else 0).sum

/-- The whole-term factors. -/
noncomputable def stairPw (x₁ x₂ : Fin 23 → ℚ) (i : ℕ) : ℚ :=
  ((LtermsStair i).map fun s => s.1 * x₁ s.2.1 * x₂ s.2.2).sum
noncomputable def stairQw (y₁ y₂ : Fin 23 → ℚ) (j : ℕ) : ℚ :=
  ((RtermsStair j).map fun s => s.1 * y₁ s.2.1 * y₂ s.2.2).sum

/-- The 47-term family, Nat-indexed entry function: n < 23 = l-groups, 23 ≤ n < 46 =
k-groups (k = n − 23), n = 46 = the whole term. -/
noncomputable def stairTermN (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (n i j : ℕ) : ℚ :=
  if n < 23 then -stairUl x₁ n i * stairVl y₁ n j
  else if n < 46 then -stairUk x₂ (n - 23) i * stairVk y₂ (n - 23) j
  else stairPw x₁ x₂ i * stairQw y₁ y₂ j

/-- Row/col factors of the n-th term (so stairTermM is literally a vecMulVec: rank ≤ 1). -/
noncomputable def stairTermRow (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (n : ℕ) (i : Fin 45) : ℚ :=
  if n < 23 then -stairUl x₁ n i.val
  else if n < 46 then -stairUk x₂ (n - 23) i.val
  else stairPw x₁ x₂ i.val

noncomputable def stairTermCol (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (n : ℕ) (j : Fin 45) : ℚ :=
  if n < 23 then stairVl y₁ n j.val
  else if n < 46 then stairVk y₂ (n - 23) j.val
  else stairQw y₁ y₂ j.val

/-- The Fin 47-indexed term matrices (consumed by rank_le_support_cut via submatrix). -/
noncomputable def stairTermM (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    Fin 47 → Matrix (Fin 45) (Fin 45) ℚ :=
  fun t => vecMulVec (stairTermRow x₁ y₁ x₂ y₂ t.val) (stairTermCol x₁ y₁ x₂ y₂ t.val)

lemma stairTermM_apply (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t : Fin 47) (i j : Fin 45) :
    stairTermM x₁ y₁ x₂ y₂ t i j = stairTermN x₁ y₁ x₂ y₂ t.val i.val j.val := by
  simp only [stairTermM, Matrix.vecMulVec_apply, stairTermRow, stairTermCol, stairTermN]
  split_ifs <;> ring

lemma stairTermM_rank_le (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t : Fin 47) :
    (stairTermM x₁ y₁ x₂ y₂ t).rank ≤ 1 :=
  Matrix.rank_vecMulVec_le _ _

lemma submatrix_vecMulVec {u : Fin 45 → ℚ} {v : Fin 45 → ℚ}
    {r : Type*} {c : Type*} (fr : r → Fin 45) (fc : c → Fin 45) :
    (vecMulVec u v).submatrix fr fc = vecMulVec (u ∘ fr) (v ∘ fc) := by
  ext a b
  simp [Matrix.submatrix_apply, Matrix.vecMulVec_apply]

/-! ## Disjointness pin: L-cells ∩ R-cells = ∅ everywhere (the design() assert) -/

theorem stairLR_disjoint_pin :
    ((List.range 45).all fun i => (List.range 45).all fun j =>
      decide (∀ p ∈ stairLcellN i, ∀ q ∈ stairRcellN j, p ≠ q)) = true := by decide

lemma mem_stairLcellN {i : ℕ} {s : ℚ × Pr 23} (hs : s ∈ LtermsStair i) :
    ((s.2.1 : ℕ), (s.2.2 : ℕ)) ∈ stairLcellN i :=
  List.mem_map.mpr ⟨s, hs, rfl⟩

lemma mem_stairRcellN {j : ℕ} {t : ℚ × Pr 23} (ht : t ∈ RtermsStair j) :
    ((t.2.1 : ℕ), (t.2.2 : ℕ)) ∈ stairRcellN j :=
  List.mem_map.mpr ⟨t, ht, rfl⟩

lemma stairLR_disjoint (i j : ℕ) (hi : i < 45) (hj : j < 45)
    (s : ℚ × Pr 23) (hs : s ∈ LtermsStair i)
    (t : ℚ × Pr 23) (ht : t ∈ RtermsStair j) : s.2 ≠ t.2 := by
  have hp : decide (∀ p ∈ stairLcellN i, ∀ q ∈ stairRcellN j, p ≠ q) = true :=
    List.all_eq_true.mp
      ((List.all_eq_true.mp stairLR_disjoint_pin) i (List.mem_range.mpr hi))
      j (List.mem_range.mpr hj)
  have hcert : ∀ p ∈ stairLcellN i, ∀ q ∈ stairRcellN j, p ≠ q := of_decide_eq_true hp
  intro hst
  exact hcert _ (mem_stairLcellN hs) _ (mem_stairRcellN ht)
    (Prod.ext (congrArg (fun c : Pr 23 => (c.1 : ℕ)) hst)
      (congrArg (fun c : Pr 23 => (c.2 : ℕ)) hst))

/-! ## Coherence pins: raw stairNESr/Sc data == the Lean family coordinate sets -/

theorem stairNESr_coh :
    ((List.range 47).all fun t => (List.range 45).all fun i =>
      decide ((i ∈ stairNESr.getD t [] ↔
        ((t < 23 ∧ t ∈ stairLsndN i) ∨ (23 ≤ t ∧ t < 46 ∧ t - 23 ∈ stairLfstN i) ∨ 46 ≤ t))))
      = true := by decide

theorem stairNESc_coh :
    ((List.range 47).all fun t => (List.range 45).all fun j =>
      decide ((j ∈ stairNESc.getD t [] ↔
        ((t < 23 ∧ t ∈ stairRsndN j) ∨ (23 ≤ t ∧ t < 46 ∧ t - 23 ∈ stairRfstN j) ∨ 46 ≤ t))))
      = true := by decide

/-! ## Vanishing lemmas (Nat-membership hypotheses match the pin data form) -/

lemma stairUl_eq_zero (x₁ : Fin 23 → ℚ) (l i : ℕ)
    (h : l ∉ stairLsndN i) : stairUl x₁ l i = 0 :=
  List.sum_map_ite_eq_zero (LtermsStair i) (fun s => (s.2.2 : ℕ))
    (fun s => s.1 * x₁ s.2.1) l (by simpa [stairLsndN] using h)

lemma stairVl_eq_zero (y₁ : Fin 23 → ℚ) (l j : ℕ)
    (h : l ∉ stairRsndN j) : stairVl y₁ l j = 0 :=
  List.sum_map_ite_eq_zero (RtermsStair j) (fun s => (s.2.2 : ℕ))
    (fun s => s.1 * y₁ s.2.1) l (by simpa [stairRsndN] using h)

lemma stairUk_eq_zero (x₂ : Fin 23 → ℚ) (k i : ℕ)
    (h : k ∉ stairLfstN i) : stairUk x₂ k i = 0 :=
  List.sum_map_ite_eq_zero (LtermsStair i) (fun s => (s.2.1 : ℕ))
    (fun s => s.1 * x₂ s.2.2) k (by simpa [stairLfstN] using h)

lemma stairVk_eq_zero (y₂ : Fin 23 → ℚ) (k j : ℕ)
    (h : k ∉ stairRfstN j) : stairVk y₂ k j = 0 :=
  List.sum_map_ite_eq_zero (RtermsStair j) (fun s => (s.2.1 : ℕ))
    (fun s => s.1 * y₂ s.2.2) k (by simpa [stairRfstN] using h)

/-! ## P3 part-1 helpers (written pre-wipe, NOT yet run) -/

lemma List.sum_map_neg {α : Type*} (l : List α) (f : α → ℚ) :
    (l.map fun s => -f s).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons s ss ih => simp only [List.map_cons, List.sum_cons, ih, neg_add]

lemma List.sum_map_const_zero (α : Type*) (l : List α) :
    (l.map fun _ : α => (0 : ℚ)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons _ ss ih => simp only [List.map_cons, List.sum_cons, ih, add_zero]

/-- (l.map f).sum = 0 when f vanishes on all of l (for the diagonal piece A). NOT yet run. -/
lemma List.sum_map_eq_zero {α : Type*} (l : List α) (f : α → ℚ)
    (h : ∀ x ∈ l, f x = 0) : (l.map f).sum = 0 := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons,
      h s (by simp), ih (fun x hx => h x (by simp [hx])), zero_add]

lemma mul_ite_one (P : Prop) [Decidable P] (a b : ℚ) :
    a * (if P then (1 : ℚ) else 0) * b = if P then a * b else 0 := by
  split_ifs <;> ring

/-- Per-entry Kronecker expansion of the corner summand into its 4 δ-pieces.
(Written pre-wipe; NOT yet run.) -/
lemma summand_normal (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (s t : ℚ × Pr 23) :
    s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2 * t.1
    = (if s.2 = t.2 then s.1 * t.1 else 0)
      - (if s.2.1 = t.2.1 then s.1 * x₂ s.2.2 * (t.1 * y₂ t.2.2) else 0)
      - (if s.2.2 = t.2.2 then s.1 * x₁ s.2.1 * (t.1 * y₁ t.2.1) else 0)
      + (s.1 * x₁ s.2.1 * x₂ s.2.2) * (t.1 * y₁ t.2.1 * y₂ t.2.2) := by
  have hδ : (if s.2.1 = t.2.1 then (1 : ℚ) else 0) * (if s.2.2 = t.2.2 then (1 : ℚ) else 0)
      = if s.2 = t.2 then (1 : ℚ) else 0 := by
    by_cases h1 : s.2.1 = t.2.1
    · by_cases h2 : s.2.2 = t.2.2
      · rw [if_pos h1, if_pos h2, if_pos (Prod.ext h1 h2)]; ring
      · have hne : s.2 ≠ t.2 := fun hh => h2 (congrArg Prod.snd hh)
        rw [if_pos h1, if_neg h2, if_neg hne]; ring
    · have hne : s.2 ≠ t.2 := fun hh => h1 (congrArg Prod.fst hh)
      rw [if_neg h1, if_neg hne]; ring
  simp only [stairPairM, Matrix.kroneckerMap_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply]
  have pA : s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0)
        * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
      = if s.2 = t.2 then s.1 * t.1 else 0 := by
    have hass : s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0)
        * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
      = s.1 * ((if s.2.1 = t.2.1 then (1 : ℚ) else 0)
        * (if s.2.2 = t.2.2 then (1 : ℚ) else 0)) * t.1 := by ring
    rw [hass, hδ]
    exact mul_ite_one _ _ _
  have pB : s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0) * (x₂ s.2.2 * y₂ t.2.2) * t.1
      = if s.2.1 = t.2.1 then s.1 * x₂ s.2.2 * (t.1 * y₂ t.2.2) else 0 := by
    split_ifs <;> ring
  have pC : s.1 * (x₁ s.2.1 * y₁ t.2.1) * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
      = if s.2.2 = t.2.2 then s.1 * x₁ s.2.1 * (t.1 * y₁ t.2.1) else 0 := by
    split_ifs <;> ring
  have pD : s.1 * (x₁ s.2.1 * y₁ t.2.1) * (x₂ s.2.2 * y₂ t.2.2) * t.1
      = (s.1 * x₁ s.2.1 * x₂ s.2.2) * (t.1 * y₁ t.2.1 * y₂ t.2.2) := by ring
  have e1 : s.1 * (((if s.2.1 = t.2.1 then (1 : ℚ) else 0) - x₁ s.2.1 * y₁ t.2.1)
        * ((if s.2.2 = t.2.2 then (1 : ℚ) else 0) - x₂ s.2.2 * y₂ t.2.2)) * t.1
      = s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0)
          * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
        - s.1 * (if s.2.1 = t.2.1 then (1 : ℚ) else 0) * (x₂ s.2.2 * y₂ t.2.2) * t.1
        - s.1 * (x₁ s.2.1 * y₁ t.2.1)
          * (if s.2.2 = t.2.2 then (1 : ℚ) else 0) * t.1
        + s.1 * (x₁ s.2.1 * y₁ t.2.1) * (x₂ s.2.2 * y₂ t.2.2) * t.1 := by ring
  rw [e1, pA, pB, pC, pD]


/-! ## P3 part 2: the corner identity (corner entry = Σ over the 47 terms) -/

lemma List.sum_map_congr {α : Type*} (l : List α) {f g : α → ℚ}
    (h : ∀ s ∈ l, f s = g s) : (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [h s (by simp), ih (fun x hx => h x (by simp [hx]))]

/-- Fin/Nat condition bridge for the regrouping lemma's coordinate ite. -/
lemma stair_ite_fin_nat (g : (ℚ × Pr 23) → Fin 23) (f : (ℚ × Pr 23) → ℚ) (s : ℚ × Pr 23) (c : Fin 23) :
    (if (g s : ℕ) = (c : ℕ) then f s else 0) = (if g s = c then f s else 0) := by
  by_cases h : g s = c
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun hh => h (Fin.ext hh))]

lemma stair_sum_fin_nat (g : (ℚ × Pr 23) → Fin 23) (f : (ℚ × Pr 23) → ℚ)
    (l : List (ℚ × Pr 23)) (c : Fin 23) :
    (l.map fun s => if (g s : ℕ) = (c : ℕ) then f s else 0).sum
      = (l.map fun s => if g s = c then f s else 0).sum :=
  List.sum_map_congr l (fun s _ => stair_ite_fin_nat g f s c)

/-- **The corner identity**: for arbitrary labels the pair matrix's corner entry is the sum of
the 47 term entries (the identity `rank_le_support_cut` consumes as `hsum`). -/
theorem corStairQ_stairPairM_sumN (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (i j : ℕ) (hi : i < 45) (hj : j < 45) :
    corStairQ (stairPairM x₁ y₁ x₂ y₂) i j
      = ∑ t ∈ Finset.range 47, stairTermN x₁ y₁ x₂ y₂ t i j := by
  -- (1) fold the row coefficient into the inner sum
  have h1 : corStairQ (stairPairM x₁ y₁ x₂ y₂) i j
      = ((RtermsStair j).map fun t =>
          ((LtermsStair i).map fun s => s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2 * t.1).sum).sum := by
    simp only [corStairQ]
    refine congrArg List.sum (List.map_congr_left (fun t _ => ?_))
    exact (List.sum_map_mul_right (LtermsStair i)
      (fun s => s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2) t.1).symm
  -- (2) the per-t four-piece split
  have h2 : ∀ t : ℚ × Pr 23,
      ((LtermsStair i).map fun s => s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2 * t.1).sum
      = ((LtermsStair i).map fun s => if s.2 = t.2 then s.1 * t.1 else 0).sum
        - ((LtermsStair i).map fun s =>
            if s.2.1 = t.2.1 then s.1 * x₂ s.2.2 * (t.1 * y₂ t.2.2) else 0).sum
        - ((LtermsStair i).map fun s =>
            if s.2.2 = t.2.2 then s.1 * x₁ s.2.1 * (t.1 * y₁ t.2.1) else 0).sum
        + ((LtermsStair i).map fun s =>
            (s.1 * x₁ s.2.1 * x₂ s.2.2) * (t.1 * y₁ t.2.1 * y₂ t.2.2)).sum := by
    intro t
    rw [show (List.map (fun s : ℚ × Pr 23 => s.1 * stairPairM x₁ y₁ x₂ y₂ s.2 t.2 * t.1)
          (LtermsStair i))
        = List.map (fun s : ℚ × Pr 23 =>
            (if s.2 = t.2 then s.1 * t.1 else 0)
            - (if s.2.1 = t.2.1 then s.1 * x₂ s.2.2 * (t.1 * y₂ t.2.2) else 0)
            - (if s.2.2 = t.2.2 then s.1 * x₁ s.2.1 * (t.1 * y₁ t.2.1) else 0)
            + ((s.1 * x₁ s.2.1 * x₂ s.2.2) * (t.1 * y₁ t.2.1 * y₂ t.2.2))) (LtermsStair i) from
      List.map_congr_left (fun s _ => summand_normal x₁ y₁ x₂ y₂ s t)]
    simp only [List.sum_map_add, List.sum_map_sub]
  -- (3) the diagonal piece vanishes
  have hA : ((RtermsStair j).map fun t =>
      ((LtermsStair i).map fun s => if s.2 = t.2 then s.1 * t.1 else 0).sum).sum = 0 := by
    refine List.sum_map_eq_zero _ _ (fun t ht => List.sum_map_eq_zero _ _ (fun s hs => ?_))
    rw [if_neg (stairLR_disjoint i j hi hj s hs t ht)]
  -- (4) the k-groups (shared FIRST coordinate)
  have hB : ((RtermsStair j).map fun t =>
      ((LtermsStair i).map fun s =>
        if s.2.1 = t.2.1 then s.1 * x₂ s.2.2 * (t.1 * y₂ t.2.2) else 0).sum).sum
      = ∑ k : Fin 23, stairUk x₂ k i * stairVk y₂ k j := by
    rw [List.sum_sum_ite_eq_group (lR := RtermsStair j) (lL := LtermsStair i)
      (f := fun s => s.1 * x₂ s.2.2) (g := fun t => t.1 * y₂ t.2.2)
      (k₁ := fun s => s.2.1) (k₂ := fun t => t.2.1)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [stairUk, stairVk]
    congr 1
    · exact (stair_sum_fin_nat (fun s => s.2.1) (fun s => s.1 * x₂ s.2.2) (LtermsStair i) c).symm
    · exact (stair_sum_fin_nat (fun t => t.2.1) (fun t => t.1 * y₂ t.2.2) (RtermsStair j) c).symm
  -- (5) the l-groups (shared SECOND coordinate)
  have hC : ((RtermsStair j).map fun t =>
      ((LtermsStair i).map fun s =>
        if s.2.2 = t.2.2 then s.1 * x₁ s.2.1 * (t.1 * y₁ t.2.1) else 0).sum).sum
      = ∑ l : Fin 23, stairUl x₁ l i * stairVl y₁ l j := by
    rw [List.sum_sum_ite_eq_group (lR := RtermsStair j) (lL := LtermsStair i)
      (f := fun s => s.1 * x₁ s.2.1) (g := fun t => t.1 * y₁ t.2.1)
      (k₁ := fun s => s.2.2) (k₂ := fun t => t.2.2)]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp only [stairUl, stairVl]
    congr 1
    · exact (stair_sum_fin_nat (fun s => s.2.2) (fun s => s.1 * x₁ s.2.1) (LtermsStair i) c).symm
    · exact (stair_sum_fin_nat (fun t => t.2.2) (fun t => t.1 * y₁ t.2.1) (RtermsStair j) c).symm
  -- (6) the whole term
  have hD : ((RtermsStair j).map fun t =>
      ((LtermsStair i).map fun s =>
        (s.1 * x₁ s.2.1 * x₂ s.2.2) * (t.1 * y₁ t.2.1 * y₂ t.2.2)).sum).sum
      = stairPw x₁ x₂ i * stairQw y₁ y₂ j := by
    rw [List.sum_sum_mul]
    simp only [stairPw, stairQw]
  -- (7) the Fin → range conversions and the range-47 split
  have hB' : (∑ k : Fin 23, stairUk x₂ k i * stairVk y₂ k j)
      = ∑ n ∈ Finset.range 23, stairUk x₂ n i * stairVk y₂ n j :=
    Fin.sum_univ_eq_sum_range (fun n => stairUk x₂ n i * stairVk y₂ n j) 23
  have hC' : (∑ l : Fin 23, stairUl x₁ l i * stairVl y₁ l j)
      = ∑ n ∈ Finset.range 23, stairUl x₁ n i * stairVl y₁ n j :=
    Fin.sum_univ_eq_sum_range (fun n => stairUl x₁ n i * stairVl y₁ n j) 23
  have hR : (∑ t ∈ Finset.range 47, stairTermN x₁ y₁ x₂ y₂ t i j)
      = -(∑ n ∈ Finset.range 23, stairUl x₁ n i * stairVl y₁ n j)
        - (∑ n ∈ Finset.range 23, stairUk x₂ n i * stairVk y₂ n j)
        + stairPw x₁ x₂ i * stairQw y₁ y₂ j := by
    rw [← Finset.sum_range_add_sum_Ico (fun t => stairTermN x₁ y₁ x₂ y₂ t i j)
        (show 23 ≤ 47 by omega),
      show Finset.Ico 23 47 = insert 46 (Finset.Ico 23 46) by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp only [Finset.mem_Ico]; omega),
      Finset.sum_Ico_eq_sum_range]
    have e1 : (∑ t ∈ Finset.range 23, stairTermN x₁ y₁ x₂ y₂ t i j)
        = -(∑ t ∈ Finset.range 23, stairUl x₁ t i * stairVl y₁ t j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      simp only [stairTermN, if_pos (Finset.mem_range.mp ht)]
      ring
    have e2 : (∑ t ∈ Finset.range 23, stairTermN x₁ y₁ x₂ y₂ (23 + t) i j)
        = -(∑ t ∈ Finset.range 23, stairUk x₂ t i * stairVk y₂ t j) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have ht23 : t < 23 := Finset.mem_range.mp ht
      simp only [stairTermN, if_neg (show ¬ (23 + t < 23) by omega),
        if_pos (show 23 + t < 46 by omega), Nat.add_sub_cancel_left]
      ring
    have e3 : stairTermN x₁ y₁ x₂ y₂ 46 i j = stairPw x₁ x₂ i * stairQw y₁ y₂ j := by
      simp only [stairTermN, if_neg (show ¬ (46 < 23) by omega),
        if_neg (show ¬ (46 < 46) by omega)]
    rw [e1, e2, e3]
    ring
  rw [h1, List.map_congr_left (fun t _ => h2 t)]
  simp only [List.sum_map_add, List.sum_map_sub]
  rw [hA, hB, hC, hD, hB', hC', hR]
  ring

/-! ## P4: the block bound and the 689-block instantiation -/

/-- Coherence accessor: the pinned row support is exactly the family coordinate set. -/
lemma stairNESr_iff (t i : ℕ) (ht : t < 47) (hi : i < 45) :
    (i ∈ stairNESr.getD t [] ↔ ((t < 23 ∧ t ∈ stairLsndN i) ∨
      (23 ≤ t ∧ t < 46 ∧ t - 23 ∈ stairLfstN i) ∨ 46 ≤ t)) :=
  of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp stairNESr_coh t (List.mem_range.mpr ht)) i (List.mem_range.mpr hi))

lemma stairNESc_iff (t j : ℕ) (ht : t < 47) (hj : j < 45) :
    (j ∈ stairNESc.getD t [] ↔ ((t < 23 ∧ t ∈ stairRsndN j) ∨
      (23 ≤ t ∧ t < 46 ∧ t - 23 ∈ stairRfstN j) ∨ 46 ≤ t)) :=
  of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp stairNESc_coh t (List.mem_range.mpr ht)) j (List.mem_range.mpr hj))

/-- Row factor of term `t` vanishes off its structural row support. -/
lemma stairTermRow_eq_zero (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t : Fin 47) (i : ℕ) (hi : i < 45)
    (h : i ∉ stairNESr.getD t.val []) : stairTermRow x₁ y₁ x₂ y₂ t.val ⟨i, hi⟩ = 0 := by
  have hmem : ¬((t.val < 23 ∧ t.val ∈ stairLsndN i) ∨
      (23 ≤ t.val ∧ t.val < 46 ∧ t.val - 23 ∈ stairLfstN i) ∨ 46 ≤ t.val) :=
    fun hc => h ((stairNESr_iff t.val i t.isLt hi).mpr hc)
  rcases Nat.lt_or_ge t.val 23 with h23 | h23
  · simp only [stairTermRow, if_pos h23]
    rw [stairUl_eq_zero x₁ t.val i (fun hm => hmem (Or.inl ⟨h23, hm⟩)), neg_zero]
  · rcases Nat.lt_or_ge t.val 46 with h46 | h46
    · simp only [stairTermRow]
      rw [if_neg (show ¬ t.val < 23 by omega), if_pos h46,
        stairUk_eq_zero x₂ (t.val - 23) i
          (fun hm => hmem (Or.inr (Or.inl ⟨h23, h46, hm⟩))), neg_zero]
    · exact absurd (Or.inr (Or.inr h46)) hmem

/-- Col factor of term `t` vanishes off its structural col support. -/
lemma stairTermCol_eq_zero (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (t : Fin 47) (j : ℕ) (hj : j < 45)
    (h : j ∉ stairNESc.getD t.val []) : stairTermCol x₁ y₁ x₂ y₂ t.val ⟨j, hj⟩ = 0 := by
  have hmem : ¬((t.val < 23 ∧ t.val ∈ stairRsndN j) ∨
      (23 ≤ t.val ∧ t.val < 46 ∧ t.val - 23 ∈ stairRfstN j) ∨ 46 ≤ t.val) :=
    fun hc => h ((stairNESc_iff t.val j t.isLt hj).mpr hc)
  rcases Nat.lt_or_ge t.val 23 with h23 | h23
  · simp only [stairTermCol, if_pos h23]
    rw [stairVl_eq_zero y₁ t.val j (fun hm => hmem (Or.inl ⟨h23, hm⟩))]
  · rcases Nat.lt_or_ge t.val 46 with h46 | h46
    · simp only [stairTermCol]
      rw [if_neg (show ¬ t.val < 23 by omega), if_pos h46,
        stairVk_eq_zero y₂ (t.val - 23) j
          (fun hm => hmem (Or.inr (Or.inl ⟨h23, h46, hm⟩)))]
    · exact absurd (Or.inr (Or.inr h46)) hmem

/-- Cardinality of a `Fin n`-filter against a raw Nat list. -/
lemma card_filter_mem_fin {n : ℕ} {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < n) :
    ((Finset.univ : Finset (Fin n)).filter (fun r => r.val ∈ l)).card = l.length := by
  classical
  have himg : ((Finset.univ : Finset (Fin n)).filter (fun r => r.val ∈ l)).image Fin.val
      = l.toFinset := by
    ext x
    constructor
    · intro hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
      exact List.mem_toFinset.mpr (Finset.mem_filter.mp hr).2
    · intro hx
      have hx' : x ∈ l := List.mem_toFinset.mp hx
      exact Finset.mem_image.mpr
        ⟨⟨x, hlt x hx'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩, rfl⟩
  have h1 : ((Finset.univ : Finset (Fin n)).filter (fun r => r.val ∈ l)).card
      = (((Finset.univ : Finset (Fin n)).filter (fun r => r.val ∈ l)).image Fin.val).card :=
    (Finset.card_image_of_injective _ Fin.val_injective).symm
  rw [h1, himg, List.toFinset_card_of_nodup hnd]

/-- Bridge: the bulk `decide` card pin, per block. -/
theorem stairNEcardOK_spec (b : StairNEBlock) (hb : b ∈ stairNEBlocksX) :
    (b.R0.length + b.C0.length + b.T0.length = b.cut) ∧ b.i < 45 ∧ b.j < 45 ∧
    (∀ r ∈ b.R0, r < 45) ∧ (∀ c ∈ b.C0, c < 45) ∧ (∀ t ∈ b.T0, t < 47) ∧
    b.R0.Nodup ∧ b.C0.Nodup ∧ b.T0.Nodup := by
  have h := List.all_eq_true.mp stairNE_cuts_card b hb
  simp only [stairNEcardOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Bridge: the bulk `decide` cover pin (cut_bound's certificate loop), per block. -/
theorem stairNEcoverOK_spec (b : StairNEBlock) (hb : b ∈ stairNEBlocksX) :
    ∀ t ∈ List.range 47, t ∉ b.T0 →
      (∀ r ∈ stairNESr.getD t [], r ≤ b.i → r ∈ b.R0) ∨
      (∀ c ∈ stairNESc.getD t [], b.j ≤ c → c ∈ b.C0) := by
  intro t ht hT
  have h := List.all_eq_true.mp (List.all_eq_true.mp stairNE_cuts_cover b hb) t ht
  simp only [stairNEcoverOK, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (hT0 | hr) | hc
  · exact absurd hT0 hT
  · left
    intro r hr' hle
    have hb' := List.all_eq_true.mp hr r hr'
    simpa [hle] using hb'
  · right
    intro c hc' hjc
    have hb' := List.all_eq_true.mp hc c hc'
    simpa [hjc] using hb'

/-! ## P4: the block cut sets, the block bound, and the 689-block instantiation -/

noncomputable def stairBlockR0 (b : StairNEBlock) : Finset (Fin 45) :=
  Finset.univ.filter fun r => r.val ∈ b.R0

noncomputable def stairBlockC0 (b : StairNEBlock) : Finset (Fin 45) :=
  Finset.univ.filter fun c => c.val ∈ b.C0

noncomputable def stairBlockT0 (b : StairNEBlock) : Finset (Fin 47) :=
  Finset.univ.filter fun t => t.val ∈ b.T0

noncomputable def stairBlockTerms (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (X Y : ℕ) :
    Fin 47 → Matrix {r : Fin 45 // r.val < X} {c : Fin 45 // Y ≤ c.val} ℚ :=
  fun t => (stairTermM x₁ y₁ x₂ y₂ t).submatrix Subtype.val Subtype.val

/-- Entrywise form of the corner identity (what `hsum` consumes). -/
theorem stairCornerQOf_pair_entry (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (r c : Fin 45) :
    stairCornerQOf (stairPairM x₁ y₁ x₂ y₂) r c = ∑ t : Fin 47, stairTermM x₁ y₁ x₂ y₂ t r c := by
  show corStairQ (stairPairM x₁ y₁ x₂ y₂) r.val c.val = _
  rw [corStairQ_stairPairM_sumN x₁ y₁ x₂ y₂ r.val c.val r.isLt c.isLt]
  rw [← Fin.sum_univ_eq_sum_range (fun n => stairTermN x₁ y₁ x₂ y₂ n r.val c.val) 47]
  exact Finset.sum_congr rfl (fun t _ => (stairTermM_apply x₁ y₁ x₂ y₂ t r c).symm)

/-- `hsum`: the restricted block is the sum of the restricted terms. -/
theorem stairBlock_hsum (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (X Y : ℕ) :
    (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)).submatrix
        (fun r : {r : Fin 45 // r.val < X} => r.1) (fun c : {c : Fin 45 // Y ≤ c.val} => c.1)
      = ∑ t : Fin 47, stairBlockTerms x₁ y₁ x₂ y₂ X Y t := by
  ext r c
  simp only [Matrix.submatrix_apply, Matrix.sum_apply, stairBlockTerms]
  exact stairCornerQOf_pair_entry x₁ y₁ x₂ y₂ r.1 c.1

/-- **The generic block bound**: every NE block of the pair-matrix corner obeys its cut. -/
theorem stairNE_block_le (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) (b : StairNEBlock)
    (hi : b.i < 45) (hj : b.j < 45)
    (hcard : b.R0.length + b.C0.length + b.T0.length = b.cut)
    (hndR : b.R0.Nodup) (hndC : b.C0.Nodup) (hndT : b.T0.Nodup)
    (hltR : ∀ r ∈ b.R0, r < 45) (hltC : ∀ c ∈ b.C0, c < 45) (hltT : ∀ t ∈ b.T0, t < 47)
    (hcover : ∀ t ∈ List.range 47, t ∉ b.T0 →
      (∀ r ∈ stairNESr.getD t [], r ≤ b.i → r ∈ b.R0) ∨
      (∀ c ∈ stairNESc.getD t [], b.j ≤ c → c ∈ b.C0)) :
    rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (b.i + 1) b.j ≤ b.cut := by
  have hcard' : (stairBlockR0 b).card + (stairBlockC0 b).card + (stairBlockT0 b).card ≤ b.cut := by
    rw [stairBlockR0, stairBlockC0, stairBlockT0, card_filter_mem_fin hndR hltR,
      card_filter_mem_fin hndC hltC, card_filter_mem_fin hndT hltT, hcard]
  refine (rank_le_support_cut (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (b.i + 1) b.j
    (stairBlockR0 b) (stairBlockC0 b) (stairBlockT0 b)
    (stairBlockTerms x₁ y₁ x₂ y₂ (b.i + 1) b.j) ?_ ?_ ?_).trans hcard'
  · exact stairBlock_hsum x₁ y₁ x₂ y₂ (b.i + 1) b.j
  · intro t ht
    have htT : t.val ∉ b.T0 := fun hmem =>
      ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
    rcases hcover t.val (List.mem_range.mpr t.isLt) htT with hr | hc
    · left
      intro r hrR
      have hnotsr : r.1.val ∉ stairNESr.getD t.val [] := fun hmem =>
        hrR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr r.1.val hmem (by omega)⟩)
      have hrow := stairTermRow_eq_zero x₁ y₁ x₂ y₂ t r.1.val r.1.isLt hnotsr
      funext c
      simp only [stairBlockTerms, Matrix.submatrix_apply, stairTermM, Matrix.vecMulVec_apply]
      rw [hrow]; simp
    · right
      intro c hcC r
      have hnotsc : c.1.val ∉ stairNESc.getD t.val [] := fun hmem =>
        hcC (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc c.1.val hmem (by omega)⟩)
      have hcol := stairTermCol_eq_zero x₁ y₁ x₂ y₂ t c.1.val c.1.isLt hnotsc
      simp only [stairBlockTerms, Matrix.submatrix_apply, stairTermM, Matrix.vecMulVec_apply]
      rw [hcol]; simp
  · intro t _
    simp only [stairBlockTerms, stairTermM, submatrix_vecMulVec]
    exact Matrix.rank_vecMulVec_le _ _

/-- **N2b — `stairNE_rk_le`**: every nontrivial NE block of the symbolic staircase corner
obeys its extracted min-cut bound, for ARBITRARY labels. -/
theorem stairNE_rk_le (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    ∀ t ∈ stairNEBlocks, rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (t.1 + 1) t.2.1 ≤ t.2.2.2 := by
  intro t ht
  have hmem : t ∈ stairNEBlocksX.map (fun b => (b.i, b.j, b.rho, b.cut)) := by
    rw [stairNEBlocksX_map]; exact ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hmem
  obtain ⟨hcard, hi, hj, hltR, hltC, hltT, hndR, hndC, hndT⟩ := stairNEcardOK_spec b hb
  exact stairNE_block_le x₁ y₁ x₂ y₂ b hi hj hcard hndR hndC hndT hltR hltC hltT
    (stairNEcoverOK_spec b hb)


set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-! ### N2c — the rightmost-pivot lower bound at the extracted witness (check_stair item 3)

`stairPC` is the extracted rightmost-pivot pattern (staircase_data.json `pc`), a permutation
of `0..44`; the corner runs are exactly its graph (`stairCornerRuns45_toFinset`, kernel
`decide`). For row `i` the four NE blocks around `(i, pc i)` have

  A = rk q i (pc i) = k,     B = rk q (i+1) (pc i) = k+1,
  C = rk q i (pc i+1) = k,   D = rk q (i+1) (pc i+1) = k,   k = #{r < i | pc r ≥ pc i},

which is `IsPiv q i (pc i)` by `isPiv_of_bounds`. Uppers are trivial (`min(#rows,#cols)`) or
N2b's cut table (`rkQ_le_of_block`); lowers are explicit nonzero minors certified by a
modular inverse mod `stairCertP` (the N3 `certChk` mechanism) — `n2c_rank_lower`.
-/

/-- The extracted rightmost-pivot pattern: row `i`'s rightmost pivot is column `pc i`. -/
def stairPC : List ℕ := [44, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 22, 21, 20, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 0]

/-- The extracted corner runs are exactly the graph of `stairPC` (as a set: `runPairs`
emits them in run order, not row order). -/
theorem stairCornerRuns45_toFinset :
    (runPairs stairCornerRuns45).toFinset
      = ((List.range 45).map (fun i => (i, stairPC.getD i 0))).toFinset := by
  decide

theorem stairCornerRuns45_mem {x : ℕ × ℕ} :
    x ∈ runPairs stairCornerRuns45 ↔
      x ∈ (List.range 45).map (fun i => (i, stairPC.getD i 0)) := by
  rw [← List.mem_toFinset, stairCornerRuns45_toFinset, List.mem_toFinset]

/-! #### generic rank lemmas -/

/-- NE-block rank is monotone in the row cut. -/
lemma rk_rows_mono {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    {X X' Y : ℕ} (h : X ≤ X') : rk q X Y ≤ rk q X' Y := by
  rw [rk, rk]
  have he : (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)) =
      (q.submatrix (fun r : {r : Fin a // r.val < X'} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a // r.val < X} =>
          (⟨r.1, by have := r.2; omega⟩ : {r : Fin a // r.val < X'})) (fun c => c) := by
    ext i j
    rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _

/-- NE-block rank is monotone in the column cut (larger `Y` = smaller block). -/
lemma rk_cols_mono {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    {X Y Y' : ℕ} (h : Y' ≤ Y) : rk q X Y ≤ rk q X Y' := by
  rw [rk, rk]
  have he : (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)) =
      (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y' ≤ c.val} => c.1)).submatrix (fun r => r)
        (fun c : {c : Fin b // Y ≤ c.val} =>
          (⟨c.1, by have := c.2; omega⟩ : {c : Fin b // Y' ≤ c.val})) := by
    ext i j
    rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _

/-- Trivial height bound. -/
lemma rk_le_height {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) : rk q X Y ≤ X := by
  rw [rk]
  refine (Matrix.rank_le_card_height _).trans ?_
  have h := Fintype.card_le_of_embedding
    (α := {r : Fin a // r.val < X}) (β := Fin X)
    ⟨fun r => ⟨r.1.val, r.2⟩, fun u v huv => by
      simp only [Fin.mk.injEq] at huv
      exact Subtype.ext (Fin.ext huv)⟩
  simpa using h

/-- Trivial width bound. -/
lemma rk_le_width {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) (hY : Y ≤ b) : rk q X Y ≤ b - Y := by
  rw [rk]
  refine (Matrix.rank_le_card_width _).trans ?_
  have h := Fintype.card_le_of_embedding
    (α := {c : Fin b // Y ≤ c.val}) (β := Fin (b - Y))
    ⟨fun c => ⟨c.1.val - Y, by have := c.2; have := c.1.isLt; omega⟩, fun u v huv => by
      simp only [Fin.mk.injEq] at huv
      have h1 := u.2; have h2 := v.2
      exact Subtype.ext (Fin.ext (by omega))⟩
  simpa using h

/-- A nonzero `n × n` minor forces `n ≤` the NE-block rank. -/
lemma rk_ge_of_det {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) {n_ : ℕ} (R : Fin n_ → {r : Fin a // r.val < X})
    (Cc : Fin n_ → {c : Fin b // Y ≤ c.val})
    (hdet : (Matrix.of fun i j => q (R i).1 (Cc j).1).det ≠ 0) : n_ ≤ rk q X Y := by
  have h1 : (Matrix.of fun i j => q (R i).1 (Cc j).1).rank = n_ := by
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
  have h2 : ((q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
      (fun c : {c : Fin b // Y ≤ c.val} => c.1)).submatrix R Cc).rank =
      (Matrix.of fun i j => q (R i).1 (Cc j).1).rank := rfl
  rw [← h1, ← h2, rk]
  exact Matrix.rank_submatrix_le _ _ _

/-- `IsPiv` from four exact rank values. -/
lemma isPiv_of_exact {a b : ℕ} (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j = k) (hB : rk q (i+1) j = k+1)
    (hC : rk q i (j+1) = k) (hD : rk q (i+1) (j+1) = k) : IsPiv q i j := by
  unfold IsPiv
  rw [hA, hB, hC, hD]
  omega

/-- `IsPiv` from two-sided bounds. -/
lemma isPiv_of_bounds {a b : ℕ} (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j ≤ k) (hB : rk q (i+1) j ≤ k+1)
    (hC : rk q i (j+1) ≤ k) (hD : rk q (i+1) (j+1) ≤ k)
    (hBlo : k+1 ≤ rk q (i+1) j) (hClo : k ≤ rk q i (j+1)) : IsPiv q i j := by
  have hAe : rk q i j = k := le_antisymm hA (hClo.trans (rk_cols_mono q (by omega)))
  have hCe : rk q i (j+1) = k := le_antisymm hC hClo
  have hDe : rk q (i+1) (j+1) = k := le_antisymm hD (hClo.trans (rk_rows_mono q (by omega)))
  exact isPiv_of_exact q i j k hAe (le_antisymm hB hBlo) hCe hDe

/-- N2b's cut bound, restated for `stairCornerQ` at the table block `(X-1, Y)`. -/
lemma rkQ_le_of_block (X Y c r : ℕ) (hX : 1 ≤ X)
    (h : (X - 1, Y, r, c) ∈ stairNEBlocks) : rk stairCornerQ X Y ≤ c := by
  have hb := stairNE_rk_le stairQX1 stairQY1 stairQX2 stairQY2 (X - 1, Y, r, c) h
  simp only [stairCornerQ, stairMQ, stairPairM] at hb ⊢
  rwa [Nat.sub_add_cancel hX] at hb

/-- **The modular minor certificate as a rank lower bound.** `rl`/`cl` are the minor's
row/column indices, `rows` the minor mod `stairCertP` and `cols` the transpose of its
inverse mod `stairCertP` (the N3 `certChk` convention); `hent` pins `rows` against the
concrete corner entries. -/
lemma n2c_rank_lower {n_ X Y : ℕ} (hX : X ≤ 45) (rl cl : List ℕ)
    (hrl : ∀ i : Fin n_, rl.getD i.val 0 < X)
    (hcl : ∀ i : Fin n_, Y ≤ cl.getD i.val 0)
    (hclB : ∀ i : Fin n_, cl.getD i.val 0 < 45)
    (rows cols : List (List ℕ))
    (hchk : certChk rows cols n_ stairCertP = true)
    (hent : ((List.range n_).all fun i => (List.range n_).all fun j =>
      decide (corZStair stairMZ (rl.getD i 0) (cl.getD j 0) % (stairCertP : ℤ) =
        (((rows.getD i []).getD j 0 : ℕ) : ℤ))) = true) :
    n_ ≤ rk stairCornerQ X Y := by
  set Dz : Matrix (Fin n_) (Fin n_) ℤ :=
    Matrix.of fun i j => corZStair stairMZ (rl.getD i.val 0) (cl.getD j.val 0) with hDz
  have hentQ : (Matrix.of fun i j : Fin n_ =>
        stairCornerQ (⟨rl.getD i.val 0, by have := hrl i; omega⟩ : Fin 45)
          (⟨cl.getD j.val 0, hclB j⟩ : Fin 45)) =
      Dz.map (Int.cast : ℤ → ℚ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, hDz, stairCornerQ, stairCornerQOf,
      ← stairMZ_map, corStairQ_cast]
  have hdetQ : (Dz.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    have e1 : (Dz.map (Int.cast : ℤ → ℚ)).det = ((Dz.det : ℤ) : ℚ) := by
      have h := RingHom.map_det (Int.castRingHom ℚ) Dz
      rw [RingHom.mapMatrix_apply] at h
      exact h.symm
    rw [e1, Int.cast_ne_zero]
    intro h0
    have e2 := RingHom.map_det (Int.castRingHom (ZMod stairCertP)) Dz
    rw [RingHom.mapMatrix_apply, h0, map_zero] at e2
    have e3 : Dz.map (Int.castRingHom (ZMod stairCertP)) =
        Matrix.of fun i l : Fin n_ =>
          (((rows.getD i.val []).getD l.val 0 : ℕ) : ZMod stairCertP) := by
      ext i l
      rw [Matrix.map_apply, hDz, Matrix.of_apply, Matrix.of_apply, eq_intCast,
        ← ZMod.intCast_mod]
      have hc := hent
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
      rw [hc i.val i.isLt l.val l.isLt, Int.cast_natCast]
    rw [e3] at e2
    exact det_ne_zero_of_certChk rows cols hchk e2.symm
  refine rk_ge_of_det stairCornerQ X Y
    (fun i => ⟨⟨rl.getD i.val 0, by have := hrl i; omega⟩, hrl i⟩)
    (fun j => ⟨⟨cl.getD j.val 0, hclB j⟩, hcl j⟩) ?_
  have heq : (Matrix.of fun i j : Fin n_ => stairCornerQ
        ((⟨⟨rl.getD i.val 0, by have := hrl i; omega⟩, hrl i⟩ :
          {r : Fin 45 // r.val < X}).1)
        ((⟨⟨cl.getD j.val 0, hclB j⟩, hcl j⟩ : {c : Fin 45 // Y ≤ c.val}).1)) =
      (Matrix.of fun i j : Fin n_ => stairCornerQ
        (⟨rl.getD i.val 0, by have := hrl i; omega⟩ : Fin 45)
        (⟨cl.getD j.val 0, hclB j⟩ : Fin 45)) := rfl
  rw [heq, hentQ]
  exact hdetQ

/-- N2c minor certificate 0: rows [0], cols [44] (det mod P = 15495622). -/
def n2cR0 : List ℕ := [0]
def n2cC0 : List ℕ := [44]
def n2cS0 : List (List ℕ) := [[15495622]]
def n2cT0 : List (List ℕ) := [[29527921]]

/-- N2c minor certificate 1: rows 0..24, cols 20..44 (det mod P = 36405705). -/
def n2cR1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24]
def n2cC1 : List ℕ := [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cS1 : List (List ℕ) := [[63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422, 15495622],
   [63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422, 15495622],
   [15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245, 15495622],
   [26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 14661890, 44527543, 57322967, 31708898],
   [61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449]]
def n2cT1 : List (List ℕ) := [[32553298, 58835255, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 37104211, 28989464, 25762093, 517955, 1616864, 500468, 11504810, 44596665, 5770762, 28549291],
   [22163025, 17219118, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 19067038, 35349376, 66050977, 33199726, 15088108, 59528887, 41517456, 53590399, 38885400, 58109868],
   [50283606, 11194603, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 16728599, 16357722, 16380240, 27992600, 54906687, 21623932, 7529448, 55448990, 66711973, 10794353],
   [45013771, 30179833, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 5338853, 2382351, 60754229, 41771391, 45643026, 20216090, 50251042, 61320259, 3296678, 47414073],
   [43662689, 23446170, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 14557495, 45685953, 33184234, 30011733, 43535046, 12021997, 51238737, 59959978],
   [56622863, 10485996, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 820746, 35162805, 16924268, 48969331, 56237921],
   [1926665, 65182194, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 66288113, 31946054, 1430980, 61567979, 32852036],
   [56622863, 10485996, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 820746, 35162805, 16924268, 48969331, 56237921],
   [1926665, 65182194, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 66288113, 31946054, 1430980, 61567979, 32852036],
   [59468520, 7640339, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 51236637, 401314, 43576062, 66578807, 66515694, 56171416, 55524703, 34474255, 60692098],
   [33695004, 33413855, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 12848507, 2817511, 24179845, 22630360, 55725906],
   [24854524, 42254335, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 30781395, 59260851, 16724588, 8340846, 54260352, 64291348, 61284262, 20798091, 33364051],
   [33695004, 33413855, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 12848507, 2817511, 24179845, 22630360, 55725906],
   [34105845, 33003014, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 33296619, 6989205, 35357300, 35679418, 10617726, 44967568, 7639020, 29833692, 47089078],
   [42319609, 24789250, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32721354, 15413076, 2729723, 32448836, 13127019, 53776421, 36346930, 28665828, 60767574],
   [63662156, 3446703, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55213590, 15023587, 51962733, 22198407, 60485370, 44172957, 31708852, 1748696],
   [56118310, 10990549, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 66254623, 1097127, 27030834, 56981345, 55268655, 10990549],
   [2431218, 64677641, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 854236, 66011732, 40078025, 28482762, 55268655, 10990549],
   [56118310, 10990549, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1097127, 27030834, 56981345, 55268655, 10990549],
   [2431218, 64677641, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40078025, 28482762, 55268655, 10990549],
   [56118310, 10990549, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56981345, 55268655, 10990549],
   [2431218, 64677641, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56981345, 55268655, 10990549],
   [10682246, 56426613, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15863481, 8226646, 56426613],
   [24187468, 31422510, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 22503486, 45366761, 64564504, 49943178, 65896211, 66733508, 24925822, 52769991, 7216035, 13871664],
   [16350218, 28834264, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 49678027, 5510641, 63932532, 58335748, 51746746, 32300699, 66129723, 59204754, 368643, 5446262]]

/-- N2c minor certificate 2: rows 0..43, cols 1..44 (det mod P = 30053301). -/
def n2cR2 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]
def n2cC2 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cS2 : List (List ℕ) := [[11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [62603866, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15068424, 61671799, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [33709772, 43030449, 62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 25282329, 15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 43030449, 15068424, 43030449, 43030449, 61671799, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245, 15495622],
   [7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 14661890, 44527543, 57322967, 31708898],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [62603866, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 31887850, 61585314, 10013370, 6076963, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 43030449, 62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 56236711, 13351160, 36241625, 51784342, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15068424, 43030449, 15068424, 61671799, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 32256487, 36241625, 46006646, 42830140, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [25282329, 15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 6076963, 950555, 51761187, 21081840, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 63031064, 11301318, 15495622, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 30508489, 51761187, 40895904, 13308995, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 25282329, 15495622, 15495622, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 32122605, 40895904, 63518117, 33196128, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 43030449, 15068424, 61671799, 43030449, 43030449, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 28109120, 62321203, 27281786, 20008787, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 13308995, 4955012, 1167113, 47864976, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 11301318, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 33196128, 1167113, 10522293, 55434195, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 11301318, 15495622, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 3510172, 10522293, 15480703, 50540108, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 11301318, 15495622, 25282329, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 47864976, 15480703, 41832548, 67073729, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 15495622, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 55434195, 41832548, 37412653, 24324252, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 15068424, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 20343947, 35141361, 55898772, 32397634, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 67073729, 41924079, 7876856, 40754344, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 43030449, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 11975041, 62012112, 49464710, 39599045, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 57852655, 3544103, 14815804, 54139551, 57656413, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40754344, 14815804, 44367567, 37819892, 57401204, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 12922069, 44367567, 45542965, 6679643, 20769422, 15495622],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 54139551, 45542965, 61526021, 43126199, 15495622]]
def n2cT2 : List (List ℕ) := [[20028871, 7778141, 19169835, 16717352, 29487123, 59729428, 52295495, 48267120, 62685197, 61565219, 27354073, 51221762, 55992939, 849681, 49790332, 66962586, 17420784, 28974977, 26182785, 32005375, 63114082, 51323451, 34385585, 8952233, 163187, 54838355, 49085353, 19148813, 34544427, 39152927, 2402581, 5909902, 45015126, 43944686, 30817142, 10768668, 36430229, 50372580, 31709078, 63087858, 57519784, 57955454, 10313643, 26432774],
   [31075382, 32944314, 5917773, 23516933, 6367675, 24896021, 31111092, 24794376, 16392298, 55348097, 33342244, 36585383, 35604739, 42374541, 13598402, 45751672, 45051523, 32070989, 8821992, 19395144, 30307241, 27185208, 11809110, 57953002, 56649588, 61015006, 38887039, 43939703, 63158298, 20226381, 47472326, 60611570, 61568390, 19767854, 47322764, 53971809, 45811080, 13553466, 48907129, 60652833, 49186744, 17278152, 48972632, 1805534],
   [26467556, 42344652, 62215702, 7973514, 54416345, 45746884, 39364958, 13685228, 28626346, 54619868, 66311486, 44646608, 49523255, 27852025, 18547358, 60316992, 26303876, 12390558, 29822027, 3044469, 31086431, 17883302, 25336574, 13335244, 62057272, 24878117, 13966825, 20259770, 32688276, 58956904, 43013568, 62911346, 32279116, 17325339, 57155891, 34862095, 40175268, 50366652, 41153030, 14025406, 52305681, 59450539, 30006325, 32036957],
   [7685663, 48878901, 28278640, 18945643, 7264532, 11026295, 28350614, 50450570, 25256400, 39672804, 23107055, 4271315, 53804138, 62522719, 22922657, 27983843, 40866786, 6302152, 35937426, 14826354, 13204911, 11709674, 67028553, 20833549, 32944504, 25187399, 65309104, 65817078, 37307550, 50724125, 984163, 40112499, 32491758, 51965062, 45713975, 65458253, 10586836, 11964425, 32747795, 15226772, 52772747, 65017676, 46837198, 26364584],
   [23803873, 421662, 21286593, 7983432, 52047484, 16361519, 50585827, 45249195, 3048591, 19964778, 45119210, 60650964, 8390319, 17274204, 2793792, 40109334, 26512448, 41463894, 55726810, 64974917, 67082746, 11487000, 60595978, 11471242, 53235702, 45657868, 51699616, 29168336, 21075580, 36892246, 19346216, 33023962, 33895082, 1755672, 61411614, 30705215, 12868793, 30921452, 58515762, 25679222, 37326743, 56764042, 23133170, 60147331],
   [16757704, 53152662, 17818023, 32886638, 1808776, 46838643, 25675442, 60260701, 10153302, 7918132, 41704039, 28823312, 34377943, 59685046, 10163146, 10210120, 66254509, 15244476, 19783679, 43100300, 18855452, 15974625, 28372703, 58362390, 52795586, 58013350, 52792350, 38714356, 34579604, 18945794, 25616745, 40106573, 3861881, 52381197, 46497579, 439185, 49105638, 15124771, 63637697, 48326998, 64481853, 54172025, 62955638, 45710224],
   [36470585, 46847370, 59944146, 20545283, 18451275, 48557843, 1372754, 39502460, 66831890, 42904893, 8216198, 7698594, 59698725, 54042075, 30766750, 35949473, 42784333, 37216976, 2539380, 45940796, 16665338, 61259659, 55645740, 48173072, 31118733, 28251764, 21621113, 61597283, 55612235, 10122357, 64536697, 18057150, 39179431, 48269632, 4584068, 46218679, 52174844, 62567217, 49238191, 7661908, 12504147, 22038456, 45740284, 24919605],
   [66229031, 32328957, 2108378, 22587368, 49512714, 55122310, 31937261, 16477106, 39968410, 66158798, 49707621, 2201703, 60710790, 38054692, 35639028, 6821968, 2002517, 24081954, 7799478, 62100712, 20602008, 61918284, 47963045, 1761994, 12933383, 7648584, 13193834, 52032884, 35469001, 57621537, 55572326, 54061882, 56573883, 55429231, 52062868, 46214463, 53789144, 16849511, 27328869, 838986, 10737934, 21399903, 10388242, 7406841],
   [18833053, 26023665, 44234501, 32372930, 48660401, 43381153, 22361016, 8822212, 15569227, 24166192, 24089634, 22796733, 61312869, 14886432, 8368317, 5546526, 48586733, 9577334, 18050900, 58870474, 24482628, 40094459, 8127223, 58681535, 58365389, 44995857, 65322391, 36475600, 45637250, 38484734, 21983792, 4481835, 56011917, 35241829, 28688936, 57445340, 36108018, 5722869, 65740045, 17329755, 52318357, 11217765, 64954430, 1350215],
   [5289731, 1976978, 47345786, 44132451, 25225233, 17853706, 29834415, 20059592, 66360051, 60585800, 65159779, 3123775, 14683803, 62304250, 14078329, 16954682, 60600386, 51516154, 1522053, 42799812, 50045132, 40042411, 54454473, 66563348, 63908753, 41890109, 2683855, 46339541, 33659972, 62834803, 30142322, 23752713, 26652183, 58985912, 21792301, 8793727, 29097630, 13415101, 54405876, 7464490, 19252481, 22443960, 27060581, 54235130],
   [1195521, 5199960, 28524856, 44200577, 51025381, 36045374, 29686038, 22561599, 25517940, 66813366, 7312062, 17882510, 60571990, 36049402, 66041960, 31911613, 65397255, 62277915, 23263936, 50413300, 53686770, 18929259, 27717565, 2081139, 18503186, 61739950, 41914810, 42238660, 37474588, 53271478, 35621573, 59088341, 2153682, 4920257, 6277425, 41628680, 6435384, 23541873, 8709734, 28287982, 14363997, 52262307, 42332414, 26534965],
   [34154682, 26551505, 25048450, 3562056, 35998624, 38838782, 38144195, 22164329, 20280539, 34212104, 21251819, 43543515, 56108211, 1875757, 8556555, 17192914, 16650537, 42928112, 1416129, 9636905, 45424843, 54594301, 25087447, 9781115, 22979848, 50227952, 2540512, 45179495, 14347681, 27505538, 38168706, 30254931, 1373516, 41884713, 27568508, 60536878, 43113465, 15301677, 32653663, 30163714, 38128822, 3573829, 38794638, 45902377],
   [50666848, 51485114, 12815211, 56028224, 53390361, 28709595, 28051013, 66719559, 29340903, 27938487, 47798202, 63039177, 3947690, 32993267, 9637192, 33399228, 41943012, 5038517, 19196055, 24756698, 32981481, 64872918, 47307907, 12589602, 45749842, 11375184, 18507229, 48001720, 29311926, 41736518, 22241683, 29144004, 6870368, 20074882, 41048668, 46232960, 56711430, 31319507, 52466114, 23292927, 2749433, 7111784, 22437747, 26505385],
   [45942292, 4295850, 57335748, 28319492, 28772703, 40404467, 60936307, 32964502, 23583222, 51014923, 62148574, 40633343, 38236435, 21409420, 45908179, 10547600, 64877185, 51262401, 57678890, 26788577, 30067960, 8294611, 16731127, 48771613, 37669878, 33451819, 1126913, 54984131, 21415979, 45532363, 18591612, 6689069, 50648777, 32303816, 22010813, 9601510, 37370543, 29477020, 8414341, 39980240, 62345453, 3727215, 18236715, 53708759],
   [33029316, 30661409, 64214425, 747012, 55755341, 21373816, 26415988, 43768660, 40504660, 35319573, 31818884, 35420119, 63748509, 66933121, 36210349, 55300817, 34135191, 54481681, 116384, 43546745, 34938402, 43707718, 66898249, 23098065, 5887639, 28119277, 62208507, 53764780, 21149264, 30201558, 8861793, 52547071, 713521, 60797577, 23084226, 55785793, 11727939, 26246127, 7316568, 59970230, 30985401, 28245392, 43701166, 25413463],
   [28743065, 5837064, 13302737, 60818280, 61347294, 17077890, 48149622, 15900304, 22778660, 49908816, 31172797, 66076592, 17019974, 46978417, 27531728, 30531498, 17284385, 62449638, 10330370, 42757786, 31271133, 62932394, 15632963, 3433825, 39648907, 50326888, 65445448, 16260576, 32355180, 12988941, 15990127, 48603051, 40060356, 50158732, 33631628, 32611092, 51204324, 56725581, 24391175, 64937638, 64435051, 52648334, 22777714, 46191229],
   [15391784, 9837704, 48504780, 12574659, 58120321, 14038037, 24780963, 20817761, 51668417, 42700659, 22632313, 26224487, 56194653, 55626411, 18008515, 1074653, 5121284, 48787501, 60402998, 62615998, 36616117, 22542518, 19379732, 33606528, 33134295, 44863370, 38800926, 59527840, 12986602, 18666598, 62590762, 8841279, 61665533, 23576005, 59828861, 23267458, 55203241, 15306833, 34947726, 5176449, 378131, 12336173, 13356131, 35495817],
   [15391784, 9837704, 48504780, 12574659, 58120321, 14038037, 24780963, 20817761, 51668417, 42700659, 22632313, 26224487, 56194653, 55626411, 52161767, 3185245, 64422235, 63389074, 32277844, 12933859, 19189397, 22542518, 19379732, 33606528, 33134295, 44863370, 38800926, 59527840, 12986602, 18666598, 62590762, 8841279, 61665533, 23576005, 59828861, 23267458, 55203241, 3206259, 4791029, 3184887, 63865452, 64623427, 24617650, 49982839],
   [64863111, 56122858, 32795135, 24402306, 60485301, 6702258, 23145938, 64975721, 62832174, 50081745, 13445742, 17028855, 63316509, 32639795, 45613742, 15738669, 44070839, 49857387, 52086419, 33614959, 19255265, 1377318, 38970074, 44114991, 60380951, 61607463, 15393345, 65290900, 4823940, 7131638, 49210872, 32244346, 55508686, 53463292, 29464637, 52192711, 28390954, 25924984, 12250204, 28607931, 35768878, 51489325, 49408373, 30670902],
   [64863111, 56122858, 32795135, 24402306, 60485301, 6702258, 23145938, 64975721, 62832174, 50081745, 13445742, 17028855, 63316509, 32639795, 45613742, 15738669, 36082059, 54953961, 63619482, 59899799, 60079284, 1377318, 38970074, 44114991, 60380951, 61607463, 15393345, 65290900, 4823940, 7131638, 49210872, 32244346, 55508686, 53463292, 29464637, 52192711, 28390954, 25924984, 12250204, 9477481, 37494011, 27899019, 41397962, 19360120],
   [47225579, 35299153, 17085490, 36229953, 62850281, 66475338, 21510913, 42024822, 6887072, 57462831, 4259171, 7833223, 3329506, 9653179, 39065717, 64714529, 48255672, 45166594, 8331331, 37752671, 35864521, 47320977, 58560416, 54623454, 20518748, 11242697, 59094623, 3945101, 63770137, 62705537, 35830982, 55647413, 49351839, 16241720, 66209272, 14009105, 1578667, 48643709, 48970796, 48905012, 19965899, 27522117, 65985493, 58506025],
   [47225579, 35299153, 17085490, 36229953, 62850281, 66475338, 21510913, 42024822, 6887072, 57462831, 4259171, 7833223, 3329506, 9653179, 39065717, 64714529, 48255672, 45166594, 8331331, 51174438, 22442754, 47320977, 58560416, 54623454, 20518748, 11242697, 59094623, 3945101, 63770137, 62705537, 35830982, 55647413, 49351839, 16241720, 66209272, 14009105, 1578667, 48643709, 48970796, 48905012, 19965899, 27522117, 65985493, 58506025],
   [4823150, 18825455, 34180169, 9915567, 3843226, 54667557, 37812672, 6197950, 4003127, 15298111, 31722542, 43369648, 41596331, 10937111, 33848525, 10622180, 45530638, 62548209, 49228594, 40828372, 64936551, 22160583, 10265392, 43107301, 57282565, 49288899, 38938681, 52649601, 9644584, 46828752, 39093534, 51466300, 22560810, 28310335, 1892724, 7166800, 58640802, 31663677, 53246761, 99399, 51387287, 11739468, 16013152, 2133938],
   [22081842, 12103045, 40949249, 13109936, 29990037, 32739, 26660969, 64026989, 28467779, 43247974, 39703376, 55350243, 13678332, 66008851, 41632306, 20064385, 46396266, 892906, 26611261, 62940325, 5431701, 63074015, 39235212, 34721602, 3535387, 4983733, 46293588, 6737900, 51855757, 12315729, 38494791, 63451518, 45507094, 39788595, 54777264, 63949083, 19676972, 29591253, 37313065, 32586399, 62162868, 19914362, 49437465, 9291605],
   [18256678, 28968832, 11979334, 41560689, 21202298, 16073740, 15101484, 1854778, 4430840, 15492905, 5155248, 31445393, 56325139, 30052188, 3003413, 52634904, 66068577, 17316478, 17442556, 52708893, 66299864, 61542773, 53843142, 25765340, 57872149, 58481437, 51670746, 24776785, 23241239, 42685173, 20059016, 18162554, 2783556, 56002089, 24288231, 19334936, 51558496, 7674939, 62717090, 27352029, 9068737, 36667910, 35697120, 16684249],
   [41710116, 2990672, 8410231, 45409065, 56128937, 28739806, 12341533, 46822413, 15281407, 9959579, 15525042, 45061180, 59564253, 23611442, 4953365, 36131125, 11502439, 41272644, 46105690, 8908299, 48080841, 32912498, 55888213, 14984232, 48578638, 16773211, 44265400, 63725243, 14916134, 56118733, 8376273, 40937810, 19638519, 39023081, 17423676, 22592459, 23699696, 52347411, 30815572, 6787823, 443444, 32176780, 36236128, 26106361],
   [34342128, 3782963, 23870260, 29603743, 15229239, 33083561, 45622802, 32053936, 52084117, 57138364, 33339585, 26784671, 5688365, 2046289, 43557914, 52318972, 52763684, 34481275, 57392445, 12270496, 8811498, 830216, 18583738, 27629342, 66693719, 49259470, 35741475, 61861157, 21204088, 15888190, 62595022, 19620172, 66096477, 34615028, 10650734, 29571477, 25170003, 28593289, 65026882, 29482484, 16378840, 64060803, 29408802, 39827897],
   [26399972, 4546519, 21222796, 18089111, 30777649, 53293363, 13388662, 12503553, 62079487, 16154026, 49948518, 17557509, 4079250, 40013545, 49556614, 34251877, 41072863, 7108761, 5053449, 63986046, 27429119, 7635864, 54110756, 21854360, 29781793, 44588939, 54279878, 28576998, 29547133, 49041572, 61561885, 40946325, 54425256, 37893575, 22037204, 29989094, 27437267, 37634993, 64951159, 6558967, 5275284, 49469856, 60231203, 24906524],
   [60226321, 34736937, 8540558, 27512317, 33342219, 10581716, 27463181, 16261749, 30534521, 57205112, 53167007, 13643832, 11006890, 54065322, 67004680, 47892570, 15352145, 12276921, 21768079, 2672474, 29085552, 32004977, 22505018, 16958845, 16646671, 66843885, 14065929, 15219737, 67104099, 261065, 52040925, 25087910, 23423032, 61032826, 26813911, 38455045, 5011252, 19587027, 32263177, 38955510, 43771030, 64547747, 12412016, 55038177],
   [30467875, 49255350, 66376326, 25470232, 15702547, 57704341, 55047486, 43335542, 32936851, 51531965, 771762, 16369714, 4687159, 8616586, 48272975, 50012643, 43547820, 55578717, 22988478, 14308953, 64461346, 31346352, 30187713, 63369923, 34832021, 20338206, 22493208, 24784136, 20138474, 60657899, 607219, 170178, 25724087, 13527798, 66659577, 36112627, 1272030, 58951014, 18914808, 17081132, 307207, 26737587, 53582510, 19685395],
   [10754994, 55560642, 24250203, 15684670, 16554860, 15758406, 51201964, 10251711, 62249667, 61530619, 34077444, 30193157, 34285767, 47139565, 39633533, 29639924, 9413436, 46462108, 65908000, 65592977, 12526940, 53170177, 2914676, 6450382, 56508874, 50099792, 37473510, 40341420, 9970225, 12685843, 467300, 21221241, 65165467, 63263375, 5182720, 22611633, 12567965, 17247634, 36076565, 34562205, 37946128, 23320296, 57450795, 45700127],
   [52856270, 2227647, 11232834, 60563583, 26780390, 31555954, 7996341, 9321580, 36473158, 53572767, 31986498, 47912914, 18825925, 18139176, 53665386, 53223316, 6025300, 3438802, 43300565, 55895431, 4399282, 39383664, 24725243, 39646095, 56020668, 53027229, 17648377, 14265807, 24226837, 62826089, 5143941, 23005183, 53544118, 11912723, 30914845, 61614341, 62199794, 11611688, 1374984, 9163067, 23229786, 43683668, 46178792, 47023961],
   [28392526, 9275488, 39959848, 3857023, 14189880, 23094185, 57298709, 63621183, 46219981, 65139410, 48076650, 29440514, 15980102, 7543631, 32552521, 21907490, 1961746, 16688236, 27327197, 45711139, 11661810, 7226518, 50433193, 63050778, 29262218, 33355699, 60881091, 34578360, 18132887, 65007958, 53938378, 19962139, 41041310, 52044158, 41967405, 49042117, 17268651, 32129030, 54529630, 6181523, 4633013, 12494180, 47377904, 22977142],
   [62542224, 55032802, 43436254, 44495544, 29216637, 20300777, 48840552, 64018453, 64879149, 13313397, 40929640, 28473603, 63022233, 45533088, 13639540, 54224825, 4703725, 39258689, 36868196, 19718802, 19583610, 38670335, 53063311, 55350802, 24785556, 44867697, 33146530, 31637525, 41259794, 23665039, 51391245, 48795549, 41821476, 4244294, 66123572, 7630643, 16704751, 3949197, 15877339, 19886305, 31772192, 32235378, 25693868, 27249016],
   [46030058, 30099193, 55669493, 59138235, 11824900, 30429964, 58933734, 19463223, 55818785, 36905430, 961490, 2707273, 58936819, 32462061, 24648458, 44197996, 52396392, 24550969, 29571579, 45426991, 58307849, 28391718, 30842851, 52542315, 2015562, 16611606, 17179813, 28815300, 26295549, 9434059, 209409, 49906476, 36324624, 26054125, 61905239, 2366669, 55451398, 6384908, 24135840, 57057613, 8598065, 23497780, 5746995, 30699832],
   [13070897, 8747648, 59145899, 32667897, 26851657, 27636556, 50475577, 19860493, 53715392, 41563259, 24055933, 16619863, 4208688, 55044373, 43646033, 14500497, 44330847, 54683869, 64674872, 38247659, 47416644, 59835535, 33472969, 44842339, 64647759, 28123604, 56554111, 25874465, 49422456, 35199999, 64771135, 25392482, 65141768, 25426872, 28866917, 7762725, 36713851, 61115403, 41731773, 20998827, 49477675, 15644376, 11449882, 40078043],
   [63667590, 50922898, 4270279, 47310588, 9459920, 37765743, 60568759, 42414122, 44655028, 29524344, 30362575, 30326331, 389945, 53951160, 30460595, 24077728, 66491803, 58863658, 67007227, 32313746, 50674126, 49556918, 11252509, 42033852, 41877765, 66976372, 40587394, 23052240, 34458211, 20969019, 13589299, 26503409, 42481471, 52440289, 12760822, 54257424, 30147300, 33015733, 18956706, 12366264, 24371245, 38429877, 58336569, 28267647],
   [10225185, 5019522, 38060791, 42333779, 37895796, 44053994, 33866153, 15182353, 41091106, 49055766, 32240512, 16787675, 24372977, 64039, 63965400, 10642252, 64761096, 42274157, 2647142, 64401927, 66559992, 7016083, 9425676, 28637898, 63284005, 4217634, 61983122, 41352189, 26127641, 8611777, 848192, 10684809, 59444747, 1215238, 60361017, 33144106, 64088179, 30350674, 34708518, 10014996, 31424081, 57890451, 22519425, 8275680],
   [14196263, 4637744, 19979924, 35482941, 7094940, 45101522, 62203784, 65365021, 33491271, 22143258, 39549146, 39521963, 21365568, 65257870, 1087410, 45506877, 47319221, 58797159, 20801538, 39464449, 22776455, 3613259, 58771026, 31525389, 14631109, 50232279, 63994975, 17289180, 42620873, 32503979, 26969189, 3100342, 48638318, 22553002, 43125046, 19666900, 53780857, 56055601, 50743662, 64025644, 3784789, 51443192, 31489867, 21666459],
   [27424412, 3478308, 14984943, 9834991, 5321205, 271712, 46652838, 32246551, 41895668, 50161873, 63216289, 46418687, 16024176, 15388973, 35598588, 56035318, 30559717, 29324259, 1444925, 52105697, 61683840, 19487159, 10523840, 6866827, 61304976, 54451424, 64773446, 12966885, 15188440, 41155199, 3449677, 35879686, 2924309, 50469181, 65898214, 14750175, 23558428, 785487, 10343625, 63860742, 37815325, 35554970, 54644150, 35508575],
   [31833795, 25461449, 35689569, 23655294, 4729960, 52437301, 63838809, 21207061, 22327514, 14762172, 48735717, 48717595, 14243712, 21135627, 54012809, 30842861, 2936679, 47844345, 9267806, 14718394, 26775542, 24778459, 39180684, 21016926, 54493312, 33488186, 20293697, 11526120, 50783535, 44038939, 40349079, 46806134, 54795165, 59774574, 6380411, 57850506, 13484285, 45437450, 6332325, 59724612, 57491770, 31286706, 55090768, 15108212],
   [31833795, 25461449, 35689569, 23655294, 4729960, 52437301, 63838809, 21207061, 22327514, 14762172, 48735717, 48717595, 14243712, 21135627, 54012809, 30842861, 24347226, 29326004, 64843602, 42120646, 66482149, 24778459, 39180684, 21016926, 54493312, 33488186, 20293697, 11526120, 50783535, 44038939, 40349079, 46806134, 54795165, 59774574, 6380411, 57850506, 13484285, 45437450, 6332325, 11746203, 55766637, 54877012, 63101179, 26418994],
   [49471327, 46285154, 51399214, 11827647, 2364980, 59773080, 65473834, 44157960, 11163757, 7381086, 57922288, 57913227, 7121856, 44122243, 60560834, 48975860, 12173613, 52535138, 3503460, 17499477, 3247491, 45943659, 19590342, 10508463, 27246656, 16744093, 43701278, 5763060, 58946197, 55573899, 53728969, 23403067, 60952012, 29887287, 36744635, 28925253, 40296572, 22718725, 36720592, 39427531, 6185890, 62138317, 9121404, 16451961],
   [49471327, 46285154, 51399214, 11827647, 2364980, 59773080, 65473834, 44157960, 11163757, 7381086, 57922288, 57913227, 7121856, 44122243, 60560834, 48975860, 12173613, 52535138, 61340142, 33256582, 54599245, 45943659, 19590342, 10508463, 27246656, 16744093, 43701278, 5763060, 58946197, 55573899, 53728969, 23403067, 60952012, 29887287, 36744635, 28925253, 40296572, 22718725, 36720592, 39427531, 6185890, 59847554, 53979775, 9967033]]

/-- N2c minor certificate 3: rows 0..23, cols 21..44 (det mod P = 62268375). -/
def n2cR3 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
def n2cC3 : List ℕ := [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cS3 : List (List ℕ) := [[63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422, 15495622],
   [15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422, 15495622],
   [63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245, 15495622],
   [26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 14661890, 44527543, 57322967, 31708898],
   [61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449]]
def n2cT3 : List (List ℕ) := [[35942361, 48349424, 60829425, 13488737, 10213071, 60074093, 54694681, 53453483, 35736088, 51797809, 27343792, 16213391, 63332866, 39433014, 41471829, 3198898, 62526204, 40082028, 19759985, 28872004, 32653420, 25172529, 14739226, 2666494],
   [34265571, 22328168, 7447486, 6699505, 44231035, 48723919, 51399923, 29901807, 30616022, 16583881, 40105751, 1482645, 47863675, 62350097, 17544621, 66151920, 22369128, 40513342, 37250536, 37250139, 22477389, 49139158, 19361427, 5620258],
   [3610567, 43862289, 63379308, 43643768, 697486, 32300832, 54280642, 51047651, 10970569, 53677098, 57415403, 20116455, 21984333, 67002507, 28681051, 32474633, 8649688, 17255536, 23704735, 5818391, 15228070, 40808022, 8768394, 19649124],
   [33790467, 59342722, 6161425, 15314075, 45110996, 58864221, 8871219, 64730322, 33920084, 9462747, 10270019, 18226177, 63796814, 50799856, 25678072, 66789362, 29911237, 46178242, 38183886, 30208448, 55355979, 29382954, 44410567, 11155073],
   [59971850, 65554524, 45066424, 26990237, 62572157, 64520462, 66132981, 64738616, 20052774, 10788553, 2425991, 14323258, 46796687, 65189314, 13945868, 8800780, 35018086, 36233280, 54823244, 59326752, 44432586, 23238557, 48819701, 41970967],
   [64374272, 45499882, 48843371, 54079633, 53543964, 65768910, 23421625, 32921432, 44266897, 43591383, 59910958, 62215783, 38301610, 12107849, 34940776, 62706471, 58327410, 57239230, 61840557, 65912287, 34945714, 41710107, 632272, 56822157],
   [51026507, 45814242, 55726549, 51343565, 52982746, 38824815, 7846293, 52050244, 3375437, 18037373, 22688148, 22392391, 52267717, 41877457, 65494006, 66101385, 43107717, 18743114, 2959911, 7975998, 11395373, 43922915, 17199228, 48282157],
   [64374272, 45499882, 48843371, 54079633, 53543964, 65768910, 36727713, 40109460, 44266897, 43591383, 59910958, 62215783, 38301610, 12107849, 34940776, 62706471, 58327410, 57239230, 61840557, 65912287, 34945714, 41710107, 632272, 56822157],
   [51026507, 45814242, 55726549, 51343565, 52982746, 38824815, 7846293, 44862216, 42345896, 18037373, 22688148, 22392391, 52267717, 41877457, 65494006, 66101385, 43107717, 18743114, 2959911, 7975998, 11395373, 43922915, 17199228, 48282157],
   [66857642, 54579532, 7423496, 41932170, 36501759, 24983064, 6221905, 16011077, 35403854, 62720519, 59977759, 14607207, 9003865, 30228084, 44147566, 19819024, 20700855, 32223787, 14744129, 6930649, 2512181, 44341180, 53336038, 1096690],
   [40640066, 48594188, 51012897, 60457346, 6496661, 24997076, 9947712, 38640662, 2831286, 21319366, 9546493, 22609587, 1650592, 21053177, 25396957, 61238245, 23426336, 34250009, 30550546, 45328111, 57862004, 65937603, 41244559, 30217888],
   [7651854, 42719936, 53557023, 44965852, 32921190, 12487790, 34626294, 46331014, 44811048, 40309390, 5943754, 50578569, 21809876, 32932129, 7928966, 460752, 10899932, 41732335, 34249922, 28560174, 55587942, 19695419, 43695800, 7777567],
   [40640066, 48594188, 51012897, 60457346, 6496661, 24997076, 9947712, 38640662, 2831286, 21319366, 9546493, 34029605, 42883951, 21053177, 25396957, 61238245, 23426336, 34250009, 30550546, 45328111, 57862004, 65937603, 41244559, 30217888],
   [39189911, 17930249, 66336106, 22850893, 7832691, 28068035, 1562107, 39982824, 6065678, 64120643, 1717159, 12411729, 52461783, 29125014, 48619171, 14478721, 46525185, 31805564, 39344169, 3845327, 52424323, 23138823, 7672715, 11304142],
   [23207544, 53598530, 49091194, 14097243, 10551390, 5040117, 51306399, 6227794, 33041174, 11721088, 61958755, 6329747, 56129731, 6898151, 61315495, 11165546, 16614735, 14839942, 57279891, 49563250, 17096744, 59229980, 48213941, 5247843],
   [23152008, 15167776, 27924302, 32993575, 49062928, 20930045, 49154077, 33512159, 36947354, 1018704, 33343904, 22021782, 23522622, 63856380, 45475117, 21830212, 57405493, 32425060, 54960619, 59266503, 253266, 52264491, 23792035, 28977715],
   [47694106, 27175595, 39117410, 31222157, 64578277, 33460268, 13753970, 65195844, 30034637, 43210364, 12528949, 34344906, 54672864, 28586187, 54438771, 40354114, 15162754, 24140912, 3359552, 35634036, 62242785, 20264736, 10877711, 27899207],
   [597814, 64138529, 65452510, 7092182, 41948433, 4024598, 30820036, 19775832, 17607697, 18418392, 2961298, 50263268, 35896463, 25399119, 45996011, 21344883, 19163514, 11190678, 61440916, 38254249, 51207161, 65368286, 6953789, 10096248],
   [47694106, 27175595, 39117410, 31222157, 64578277, 33460268, 13753970, 65195844, 30034637, 43210364, 12528949, 34344906, 54672864, 28586187, 54438771, 40354114, 15162754, 64791666, 4213788, 35634036, 62242785, 20264736, 10877711, 27899207],
   [597814, 64138529, 65452510, 7092182, 41948433, 4024598, 30820036, 19775832, 17607697, 18418392, 2961298, 50263268, 35896463, 25399119, 45996011, 21344883, 19163514, 11190678, 60586680, 39351376, 51207161, 65368286, 6953789, 10096248],
   [47694106, 27175595, 39117410, 31222157, 64578277, 33460268, 13753970, 65195844, 30034637, 43210364, 12528949, 34344906, 54672864, 28586187, 54438771, 40354114, 15162754, 64791666, 4213788, 34536909, 35211951, 20264736, 10877711, 27899207],
   [597814, 64138529, 65452510, 7092182, 41948433, 4024598, 30820036, 19775832, 17607697, 18418392, 2961298, 50263268, 35896463, 25399119, 45996011, 21344883, 19163514, 11190678, 60586680, 39351376, 11129136, 26758010, 6953789, 10096248],
   [66874034, 34601415, 36002065, 26552313, 59066143, 61358744, 19153708, 6768776, 38891104, 10893091, 50559911, 34409998, 1843187, 49383384, 65013395, 43592315, 15367063, 7154814, 57070963, 63512706, 31740839, 4695635, 64022203, 46592253],
   [17254285, 20450526, 40602146, 50381305, 60132588, 15620792, 18474494, 15949926, 23685450, 8880489, 49885227, 27215007, 17775375, 34763983, 56955207, 42448583, 4923970, 27670988, 11515726, 32188090, 13329055, 35750814, 49261638, 13377703]]

/-- N2c minor certificate 4: rows 0..22, cols 22..44 (det mod P = 35073811). -/
def n2cR4 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
def n2cC4 : List ℕ := [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cS4 : List (List ℕ) := [[34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422, 15495622],
   [19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245, 15495622],
   [18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 14661890, 44527543, 57322967, 31708898]]
def n2cT4 : List (List ℕ) := [[30115714, 2074659, 36905689, 50221868, 17773683, 2712163, 63906857, 57890384, 54705672, 26490421, 64371872, 22584499, 21788974, 51441962, 28100037, 333027, 57813493, 23105114, 13226815, 55488220, 34304552, 52350539, 42217409],
   [15868260, 65034200, 31145917, 16886991, 53842649, 54817552, 12153286, 20945603, 37599495, 48527198, 30661882, 44017094, 36737146, 60061856, 57013535, 66009241, 7829966, 38655430, 41831420, 15086578, 40703505, 45080142, 9601350],
   [24371311, 0, 58037894, 55323840, 58208907, 46298689, 35981820, 7756265, 46885976, 58776300, 52346451, 57763046, 23723179, 39095168, 4149322, 59566954, 41101110, 33567124, 6690581, 62530516, 18287193, 62951570, 26935809],
   [13538243, 0, 46500956, 11785019, 27671536, 7450521, 32141234, 49370960, 45390627, 7281692, 55365774, 48033775, 49582821, 40281350, 10972570, 26903353, 42947178, 41924233, 3505374, 17046030, 19569490, 56727567, 53686681],
   [21966270, 0, 19186416, 0, 6043704, 64638297, 9578835, 9925358, 776331, 12264909, 1635275, 13874767, 9100152, 4342676, 51507284, 15827902, 57587788, 7733561, 65550592, 14580630, 23852034, 28602213, 29759],
   [25823320, 0, 14929856, 0, 44601958, 38611789, 8711566, 12019986, 2250476, 23702501, 56156251, 51079718, 27634935, 11688682, 9620262, 9369846, 30853885, 6330269, 44486744, 38045993, 25555983, 50682387, 66686081],
   [59350776, 0, 59870127, 0, 30498383, 45225169, 7259219, 3362338, 48203615, 9896510, 32352604, 13903926, 45616831, 39900927, 50042676, 41096073, 24982028, 35700927, 7664918, 48404287, 58785540, 16096359, 4524164],
   [25823320, 0, 14929856, 0, 44601958, 51917877, 15899594, 12019986, 2250476, 23702501, 56156251, 51079718, 27634935, 11688682, 9620262, 9369846, 30853885, 6330269, 44486744, 38045993, 25555983, 50682387, 66686081],
   [59350776, 0, 59870127, 0, 30498383, 45225169, 71191, 42332797, 48203615, 9896510, 32352604, 13903926, 45616831, 39900927, 50042676, 41096073, 24982028, 35700927, 7664918, 48404287, 58785540, 16096359, 4524164],
   [67036382, 0, 39737900, 0, 24627667, 56327136, 26818810, 32503506, 28171818, 34858036, 25565876, 42926342, 65334054, 32820543, 27548819, 33066481, 52275272, 50680556, 46243927, 32702370, 37369498, 26554967, 51318014],
   [47855350, 0, 33192019, 0, 15370816, 20229149, 17704341, 40291892, 18365956, 38468894, 40574948, 47606696, 35822687, 2941155, 36922848, 27304076, 20920534, 34212407, 21315137, 39587820, 63355904, 35161889, 65502338],
   [37318746, 0, 41607964, 0, 59729525, 9805038, 65375303, 42199291, 32088135, 62238976, 36513889, 17376948, 37429079, 48648454, 22740090, 23161843, 34915379, 7818789, 30836525, 46862460, 20985619, 31616857, 5707907],
   [47855350, 0, 33192019, 0, 15370816, 20229149, 17704341, 40291892, 18365956, 38468894, 51994966, 21731196, 35822687, 2941155, 36922848, 27304076, 20920534, 34212407, 21315137, 39587820, 63355904, 35161889, 65502338],
   [45458306, 0, 14685194, 0, 42428691, 45517700, 58735354, 16446645, 2739806, 44193465, 58827190, 60342768, 36548239, 19843867, 13403831, 11652252, 60366985, 24241951, 61770793, 39234959, 44611286, 43428190, 44739040],
   [35036348, 0, 58352725, 0, 58057649, 35289007, 64166035, 58400982, 37732921, 22427855, 62326292, 38867477, 66873764, 17452477, 43746158, 14101231, 34886794, 13437184, 64057885, 23294427, 45046378, 55462480, 60234617],
   [10658413, 0, 43451970, 0, 33965449, 29716724, 13162194, 28407678, 32923052, 23830205, 65687069, 52788765, 29661282, 36256389, 58792319, 36902899, 9701892, 1864949, 6880343, 59246692, 21342630, 16069873, 43058024],
   [9776135, 0, 29292495, 0, 43865658, 37013111, 2424173, 47496293, 47528704, 58366437, 9645090, 29829980, 43262817, 977099, 35177340, 59543525, 41734009, 35745148, 23680040, 42465630, 65437473, 15792801, 1103384],
   [8289102, 0, 45507488, 0, 31234683, 60129935, 13546612, 34994890, 2925387, 42341433, 11754906, 35153664, 29988949, 50612510, 24485598, 58031253, 40560009, 6286048, 28471622, 43984650, 18904050, 50985945, 2998002],
   [9776135, 0, 29292495, 0, 43865658, 37013111, 2424173, 47496293, 47528704, 58366437, 9645090, 29829980, 43262817, 977099, 35177340, 59543525, 15275904, 36599384, 23680040, 42465630, 65437473, 15792801, 1103384],
   [8289102, 0, 45507488, 0, 31234683, 60129935, 13546612, 34994890, 2925387, 42341433, 11754906, 35153664, 29988949, 50612510, 24485598, 58031253, 40560009, 5431812, 29568749, 43984650, 18904050, 50985945, 2998002],
   [9776135, 0, 29292495, 0, 43865658, 37013111, 2424173, 47496293, 47528704, 58366437, 9645090, 29829980, 43262817, 977099, 35177340, 59543525, 15275904, 36599384, 22582913, 15434796, 65437473, 15792801, 1103384],
   [8289102, 0, 45507488, 0, 31234683, 60129935, 13546612, 34994890, 2925387, 42341433, 11754906, 35153664, 29988949, 50612510, 24485598, 58031253, 40560009, 5431812, 29568749, 3906625, 47402633, 50985945, 2998002],
   [44215492, 0, 58259607, 0, 59289892, 35379888, 63247009, 45358497, 48993325, 8198957, 10610724, 832444, 8199337, 56395318, 45301667, 25908043, 52184820, 12301939, 19931140, 64821629, 21776230, 1203159, 16170575]]

/-- N2c minor certificate 5: rows 0..44, cols 0..44 (det mod P = 31223173). -/
def n2cR5 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cC5 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cS5 : List (List ℕ) := [[11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [25282329, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 62603866, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [62603866, 15068424, 61671799, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15068424, 33709772, 43030449, 62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 25282329, 15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 15068424, 43030449, 15068424, 43030449, 43030449, 61671799, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245, 15495622],
   [7758056, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 14661890, 44527543, 57322967, 31708898],
   [62603866, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15068424, 62603866, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 31887850, 61585314, 10013370, 6076963, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 15068424, 43030449, 62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 56236711, 13351160, 36241625, 51784342, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [62603866, 15068424, 43030449, 15068424, 61671799, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 32256487, 36241625, 46006646, 42830140, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 25282329, 15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 6076963, 950555, 51761187, 21081840, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 63031064, 11301318, 15495622, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 30508489, 51761187, 40895904, 13308995, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 25282329, 15495622, 15495622, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 32122605, 40895904, 63518117, 33196128, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 15068424, 43030449, 15068424, 61671799, 43030449, 43030449, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 28109120, 62321203, 27281786, 20008787, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 13308995, 4955012, 1167113, 47864976, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 11301318, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 33196128, 1167113, 10522293, 55434195, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 11301318, 15495622, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 3510172, 10522293, 15480703, 50540108, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 11301318, 15495622, 25282329, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 47864976, 15480703, 41832548, 67073729, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 15495622, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 55434195, 41832548, 37412653, 24324252, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 15068424, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 20343947, 35141361, 55898772, 32397634, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 67073729, 41924079, 7876856, 40754344, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15068424, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 43030449, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 11975041, 62012112, 49464710, 39599045, 31157861, 32135978, 54165319, 5322943, 43030449],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 57852655, 3544103, 14815804, 54139551, 57656413, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40754344, 14815804, 44367567, 37819892, 57401204, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 12922069, 44367567, 45542965, 6679643, 20769422, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 54139551, 45542965, 61526021, 43126199, 15495622],
   [11301318, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 37819892, 61526021, 4153468, 63031064]]
def n2cT5 : List (List ℕ) := [[51608781, 23346977, 4023306, 25202327, 66339611, 37389127, 35019269, 40299053, 58180613, 61687952, 23080635, 49872702, 55797872, 56851497, 7078468, 30790992, 18979801, 12555881, 51323552, 16919863, 42120847, 28554489, 23953301, 15050436, 540624, 60622672, 29229588, 637573, 27475263, 64615596, 54680977, 15133187, 15381936, 66056682, 50396009, 31697203, 52716194, 15560685, 37299917, 28070695, 4447037, 32513403, 33717005, 43642659, 43756441],
   [4944256, 33925009, 26259457, 57776585, 33555329, 29062342, 47129693, 21707213, 28308948, 28202498, 54828365, 52208737, 43409360, 22533911, 48872980, 11199179, 3929258, 59931857, 14768642, 57100699, 43166268, 30157808, 16947410, 57150624, 3986237, 3731054, 35614249, 10235623, 4530425, 19772283, 65461925, 13456110, 35510638, 27820112, 33594425, 12857799, 37129065, 35779287, 43537218, 50003918, 49818885, 10846222, 3349963, 24937786, 18783687],
   [39027455, 64278050, 64755417, 54408762, 28583415, 9422638, 51923222, 34586243, 49706472, 14350412, 22727105, 17066501, 10758350, 29456871, 19448013, 66618216, 32177405, 24772048, 25972751, 22055196, 41992178, 34659054, 24233354, 22254244, 7870894, 55232686, 32220591, 40923234, 27255959, 10227535, 56112791, 37250520, 5545547, 4163060, 3445502, 19143562, 43319483, 1317711, 44598957, 23353836, 44045095, 56651096, 4433582, 28226004, 15680227],
   [58176462, 39116810, 19724980, 23587717, 53219642, 41745441, 42539947, 5910981, 24040958, 40099093, 19573519, 63698732, 31096238, 48963045, 12042078, 14403083, 9368544, 13472037, 23561795, 2668677, 33193708, 60015192, 25421115, 33542071, 41833796, 1077411, 51088183, 50832369, 46065604, 59879119, 43854306, 60805786, 8998075, 15063555, 20790669, 57063887, 8689560, 61104265, 1605082, 213207, 46337339, 51014600, 24129460, 26901340, 31595034],
   [39221490, 60078059, 17599086, 46732133, 39781968, 33608604, 60386451, 51158293, 42920117, 63301919, 13816014, 35637322, 50325620, 38904180, 4691935, 37018654, 13523417, 42093826, 64541932, 63602639, 44061672, 17543316, 53377130, 16886442, 56978974, 63080291, 58085076, 17246547, 7517531, 11676975, 20958235, 29345866, 64849315, 35480814, 12786570, 57451614, 54423510, 22918840, 10825311, 37014346, 2974049, 4641092, 11978237, 59961586, 3967583],
   [66877177, 28058611, 22941562, 59639855, 15200462, 23928205, 4903560, 45522230, 9791840, 17861236, 28967211, 31402828, 65503454, 33473606, 22938757, 47710684, 45775279, 17300699, 52727766, 23054251, 2934880, 54150901, 43836339, 32125475, 40840625, 7308998, 32923942, 11307136, 60661534, 48434109, 17182485, 41965854, 5770886, 49165538, 40500885, 26303561, 65837871, 15486968, 27813853, 38623507, 46702385, 52727989, 25420608, 40148226, 34488203],
   [48580369, 46920230, 5114126, 5817838, 37771586, 30503619, 26114394, 60651399, 25895277, 13222324, 22737444, 24261145, 32781308, 63612063, 30380162, 19839186, 41503241, 43877819, 40340029, 41665977, 54726374, 33628828, 65747297, 12557021, 35218963, 22723631, 9983495, 51898867, 35502701, 25719946, 58682408, 30962918, 58137576, 59468953, 5505756, 43960843, 56334746, 13690833, 42627429, 60652878, 51961480, 28699214, 17969239, 39777918, 18119121],
   [63162226, 17244382, 4590240, 45354994, 46838306, 63530421, 43891967, 43190547, 44984978, 3207486, 8129921, 23354635, 32992445, 23034643, 39162088, 61365092, 38649545, 22845501, 11547960, 17325922, 36235577, 27065422, 60783749, 22167240, 44826862, 35404053, 37199775, 3184560, 9644361, 54332310, 58554768, 47384409, 17372817, 30574274, 53186038, 9416766, 626344, 57764879, 14024040, 20028301, 6678650, 58760005, 25924056, 21992388, 41921047],
   [44865418, 36106001, 53871663, 58641836, 24427488, 52611023, 51642444, 5937300, 7082903, 51708521, 59138505, 24082806, 41990047, 28454397, 29078204, 52728138, 7362712, 52368154, 29791962, 63433369, 14847478, 12614083, 15585848, 2598786, 39205200, 50818686, 14259328, 59967226, 13154176, 20753765, 22632466, 30981846, 42208883, 4998173, 2115072, 45613627, 23683461, 35218412, 37377387, 27759495, 1984745, 61180500, 40424118, 26294763, 40285958],
   [14011275, 50901010, 59825673, 45924369, 39954860, 11961696, 30502328, 10071131, 3090174, 46209761, 59585356, 51603707, 16225316, 20229723, 58956540, 19526881, 25601820, 26236971, 18057074, 24309546, 13871651, 35335069, 57954373, 11257628, 15616363, 63876501, 18806592, 34430710, 36232799, 44092375, 113184, 56541297, 35095422, 53631479, 31882608, 57414483, 40195189, 30655391, 47299196, 45228228, 26228235, 35015183, 19291012, 40817998, 6743337],
   [41150467, 25291772, 35520341, 44356975, 11083390, 46874281, 7902546, 4668820, 32690164, 17188376, 22707723, 58362318, 31186424, 58050567, 20986000, 31471448, 29990217, 4757752, 32475259, 7793418, 20690589, 12986190, 32533258, 59749410, 43191437, 11804882, 18535161, 926726, 21690394, 17599907, 40115750, 20082601, 27353152, 14054390, 48539478, 750032, 31097714, 43140183, 39681838, 55551665, 20407249, 15893216, 47635371, 38084305, 44098076],
   [14966749, 12314545, 61416242, 46947631, 17559429, 10212186, 41669112, 47938887, 33775932, 60792726, 65648321, 9494901, 10383597, 26730961, 12896209, 3999817, 47354469, 62999064, 37777200, 38055325, 30105548, 41718630, 49480668, 49791175, 47177674, 46154864, 29351289, 9236733, 34476997, 10896736, 58421351, 4091074, 43025165, 10781884, 37753713, 30243047, 58527548, 60415265, 226678, 38130421, 40276698, 51812834, 55015088, 2070940, 50685833],
   [37435516, 14477543, 17169019, 30072114, 64848151, 41137539, 31271507, 61549152, 21607139, 43651340, 38972606, 15687824, 3344832, 31763316, 55783550, 30354065, 27740250, 51100303, 59436295, 9981409, 9334272, 30557725, 49480668, 49791175, 47177674, 39899937, 22810994, 8995085, 30226612, 14446049, 31277330, 49274544, 62164296, 14576669, 6222363, 13069191, 58932907, 63901775, 31944919, 49912808, 22876471, 64054587, 35760418, 52601196, 22695864],
   [41993278, 1125237, 32298690, 58051507, 19938713, 3356583, 32001340, 28282770, 33796895, 3838504, 65615263, 58069269, 44900784, 55733499, 41287808, 33624520, 13588365, 991243, 9886254, 22741332, 52865273, 5664274, 16266629, 29874705, 55150148, 5355795, 58774771, 12978819, 49037126, 39361588, 53964413, 8185048, 14501711, 37782033, 53210620, 23954869, 42294912, 61765482, 6534856, 25807126, 36385971, 67108769, 50487622, 16502610, 41266877],
   [33720565, 3663314, 65926556, 15787253, 51504053, 35400797, 54640468, 51320625, 10524114, 10346239, 34384595, 50765590, 36945233, 54792325, 60468230, 45105748, 45904257, 45980417, 58862175, 64266469, 42424604, 3682611, 66428078, 39832940, 51163911, 886133, 27086827, 17063444, 38762830, 11292191, 22438910, 11357628, 16105126, 4225415, 56582177, 39761524, 24607794, 56512689, 11356986, 22476884, 67018051, 17848772, 23060737, 41167314, 231310],
   [58690283, 59004934, 2110657, 53531574, 60994373, 46819846, 4811913, 50268604, 37379307, 43353124, 13399776, 58035354, 11769490, 16571010, 49281841, 46544897, 45677529, 5522065, 2314636, 33029824, 33981668, 66119158, 62531616, 5628814, 41362611, 16240861, 4299405, 34271818, 17135968, 23362443, 19814746, 36306140, 53870196, 30417671, 23831489, 43356582, 610299, 6351514, 55490989, 22766687, 29767163, 65663238, 8489021, 56616431, 15570176],
   [30005614, 59957944, 47575234, 1502392, 38159955, 29664055, 10900570, 41092098, 66549948, 44149997, 29796584, 25527244, 21860201, 10466659, 19906346, 15082440, 55049370, 19654445, 3150711, 63700096, 8685283, 43637150, 16266629, 29874705, 55150148, 28981188, 31362660, 25131803, 47299048, 8138333, 13600490, 40549571, 37154815, 60983020, 28997724, 54054075, 15320372, 3364678, 52011998, 712805, 19688547, 47017437, 40427088, 45233837, 56049891],
   [33407525, 66367696, 7302738, 42979235, 46588232, 30899000, 14902554, 6860772, 9876386, 65751086, 60093817, 10226393, 9933345, 31667997, 12894738, 52132904, 17150688, 6389206, 2936504, 5175414, 66610048, 55177233, 33214039, 19916470, 59136385, 13798283, 44946817, 51716803, 47421939, 54556970, 47995631, 18794117, 12470143, 53107365, 59712003, 16061138, 50928145, 59656500, 8133946, 44377540, 3667791, 16050290, 63475007, 27687890, 29655113],
   [26290663, 49143715, 29223912, 54326390, 24815857, 23927313, 34269531, 30863571, 55466923, 10844896, 25208573, 288898, 6775169, 47925564, 34773415, 30866193, 65975804, 61291935, 21312172, 61639389, 61093388, 64553122, 33214039, 19916470, 59136385, 57076243, 35638493, 33200162, 55835266, 4984475, 4762070, 2632655, 58204504, 50631766, 1413271, 1237767, 367679, 14146796, 47115596, 62837764, 50584306, 7966401, 45746951, 48588778, 29852344],
   [29692574, 55553467, 56060275, 28694374, 33244134, 25162258, 38271515, 63741104, 65902220, 32445985, 55505806, 52096906, 61957172, 2018043, 27761807, 33763405, 25966530, 47845824, 11592966, 42772924, 60767414, 126226, 50161449, 9958235, 63122622, 41893338, 49222650, 59785162, 55958157, 51403112, 39157211, 47986060, 33519832, 42756111, 32127550, 30353689, 35975452, 3329759, 15338118, 2441478, 17424662, 49454784, 60026169, 11770901, 44768621],
   [22575712, 38329486, 10872590, 40041529, 11471759, 18190571, 57638492, 20635044, 44383898, 44648654, 20620562, 42159411, 58798996, 18275610, 49640484, 12496694, 44105223, 1055844, 33712954, 24140173, 12422526, 52330343, 50161449, 9958235, 63122622, 18062439, 39914326, 41268521, 64371484, 1830617, 63032509, 31824598, 12145334, 40280512, 40937677, 15530318, 52523845, 24928914, 54319768, 50163119, 11236805, 51939357, 55055313, 32468597, 36314835],
   [25977623, 44739238, 37708953, 14409513, 19900036, 19425516, 61640476, 53512577, 54819195, 66249743, 50917795, 26858560, 46872140, 39476948, 42628876, 15393906, 4095949, 62707372, 18897174, 60849504, 66342338, 766520, 0, 0, 0, 2879534, 53498483, 744662, 64494375, 48249254, 30318791, 10069144, 54569521, 32404857, 4543097, 44646240, 21022759, 14111877, 22542290, 56875692, 64316470, 24593748, 25815978, 3661131, 62541894],
   [34646504, 67028891, 63616828, 64174345, 60610680, 54955376, 56363984, 56245336, 38819192, 13262496, 57044125, 55051983, 13365130, 1778869, 63265653, 48332993, 40213284, 22666994, 42497032, 57766418, 23106168, 43942715, 0, 0, 0, 31836977, 16249900, 34456877, 27111099, 63257824, 18165552, 61467262, 29646925, 41146792, 14818132, 59416140, 19750892, 64114103, 21311626, 33200422, 27389400, 49018087, 25356779, 13524140, 62867528],
   [25616060, 7933525, 50327888, 37493468, 24123292, 51541672, 58371128, 29213174, 48715560, 12641284, 12802945, 10775573, 13946681, 52564415, 56173095, 13461276, 2916643, 18506465, 64059015, 4695927, 49301720, 43281799, 45077226, 31575141, 52915854, 59490361, 31616328, 39127519, 2572931, 49836198, 36246526, 10544067, 54582459, 9802907, 42177942, 54055370, 66688838, 46747719, 61314265, 36549854, 48610793, 58640746, 12718232, 16694942, 30601025],
   [64535871, 60931194, 3132076, 700127, 36669200, 9850614, 10565420, 49232628, 54519495, 20317536, 1112031, 27226798, 34289679, 53419061, 42232501, 40773204, 36864226, 28443527, 60636924, 63463462, 32385014, 26912442, 4910422, 39486813, 7679752, 34582070, 54361107, 3428462, 991128, 30346239, 41703758, 55817813, 29693368, 14336734, 2132620, 13071756, 64953125, 48060276, 29869768, 15633875, 56829360, 21494787, 16750341, 62897336, 46576507],
   [11802915, 4138882, 24375130, 13413602, 2947977, 3367144, 34961101, 43299586, 39588617, 55124202, 62983732, 35059279, 42444133, 43025056, 49900247, 47928371, 41334601, 65168406, 53821181, 15020349, 58625918, 2267723, 50161449, 57167102, 37686321, 29538041, 34395978, 59063312, 63904495, 19047869, 13218666, 12532963, 56622819, 21734734, 33788195, 25384203, 39050138, 6470739, 46913516, 10335062, 55291661, 82565, 6415734, 34904468, 46534904],
   [64341836, 11444093, 50288407, 46447432, 13523619, 44431587, 56835506, 7293906, 55960116, 60550410, 17013491, 15648038, 6066043, 19310901, 18404859, 28064842, 34994624, 65134287, 1197017, 20661832, 51807571, 22536129, 42875505, 44854615, 25680531, 26734465, 40054406, 48908669, 66722494, 15246952, 27996673, 15482262, 9068693, 47947867, 22943683, 32490789, 59928759, 39873038, 65116564, 21645889, 44575818, 65835956, 33912082, 18000281, 42434314],
   [50425195, 37954228, 47643696, 5695242, 33781926, 42652071, 20261010, 49614122, 1743025, 17137252, 53590476, 45807922, 31686755, 54620871, 3254795, 45107641, 43196960, 6756873, 22444554, 29903839, 32325176, 63739619, 63719377, 1991647, 39468068, 34526408, 52192210, 48461058, 26054009, 11272195, 44873614, 28353120, 47347423, 38145901, 45257681, 37725810, 53955149, 6360907, 30460632, 35816831, 24934228, 62393520, 27601633, 56402159, 53874897],
   [40791162, 54113638, 14243505, 61415673, 35893211, 36872247, 58895043, 58701557, 54531179, 31929041, 58858428, 43669674, 21710635, 6469184, 14338899, 42438959, 45091499, 31398294, 67084882, 41415527, 23355081, 28722652, 18308972, 44593603, 35876133, 8250958, 47790821, 24023013, 37527892, 19375450, 56228526, 35315840, 48685073, 49100980, 34626339, 10530879, 58583545, 26514019, 65019702, 46467008, 17531673, 24870888, 33077536, 57570437, 44501898],
   [26209305, 16680627, 14767391, 21878517, 26826491, 17267212, 27695703, 93503, 39489917, 17482729, 23937850, 33672362, 18728489, 41738938, 11229713, 54162485, 20937763, 39844471, 58934866, 5127220, 2533414, 7489663, 23272520, 34983384, 26268234, 62679395, 20574541, 5628461, 63386232, 57871945, 30034462, 25605131, 33427973, 30582307, 13709487, 65290563, 44836454, 47423910, 20160513, 51833894, 34117203, 16688920, 53782865, 14065560, 34943285],
   [44506113, 64927867, 32594827, 8591675, 49237309, 28186610, 33366993, 23924983, 36653267, 41004186, 8044173, 40631886, 44149360, 66519871, 36668316, 26889286, 30576435, 22771650, 17069635, 12190717, 4866440, 40996075, 1361562, 54551838, 31889896, 47264762, 43514988, 15954654, 59876417, 24341631, 65956764, 8279241, 47171782, 27928963, 27219769, 11351772, 19509220, 63585186, 11086003, 32566774, 5674091, 26378910, 25683374, 1088799, 56536480],
   [22443192, 20621142, 8061820, 60676963, 13350727, 50807395, 19575350, 57112054, 47868100, 58234210, 8299574, 18369135, 3767401, 57416402, 25263187, 66948624, 665913, 1231837, 26691662, 58767147, 36338563, 50403405, 38298262, 50483429, 67043142, 25938255, 12224031, 31724506, 7583081, 65547552, 54613321, 8740715, 32936348, 10001944, 38375580, 13172718, 17179597, 18286256, 61263586, 12779082, 49896342, 24238549, 39010949, 57841270, 40942423],
   [48221064, 8633237, 50946149, 22876536, 62581407, 33923352, 9998032, 38615230, 11046006, 2334499, 23622061, 3574008, 49286117, 17877157, 26327556, 31629748, 26581583, 12632025, 37313047, 34462901, 37793176, 1854121, 51523011, 64510073, 27903659, 19169707, 39239155, 7886295, 51340199, 27495489, 48473480, 19178486, 48266058, 7999213, 6363433, 3479682, 22708791, 30691467, 41481952, 33306217, 36937991, 398719, 48690547, 23713209, 55186127],
   [7295923, 21610464, 25050248, 20285880, 56105368, 3476588, 43340325, 62454022, 9960238, 39260775, 30471906, 59234172, 27674179, 24666256, 38233159, 49811852, 26815967, 42603692, 35231756, 59003045, 28718344, 39890413, 34575601, 7359449, 23917422, 51928584, 28423027, 66685147, 38553596, 34198660, 30167879, 35170013, 32594045, 11271719, 6313790, 19433917, 39884540, 49530566, 44517083, 36019099, 32649056, 15383105, 12363550, 34504762, 5128797],
   [51936015, 19447466, 2188612, 37161397, 8816646, 39660094, 53737930, 48843757, 22129031, 56402161, 7357178, 39619482, 28442276, 30496825, 13392301, 35547159, 52609671, 60378736, 28084205, 30451411, 23208743, 10223336, 34575601, 7359449, 23917422, 58183511, 34963322, 66926795, 42803981, 30649347, 57311900, 57095402, 13454914, 7476934, 37845140, 45869600, 19911289, 31279809, 31252383, 52307664, 13240945, 11696695, 26418577, 14779601, 17172590],
   [11010874, 32424693, 43401570, 34570741, 2340607, 9213330, 19971364, 5573690, 21043263, 5457017, 3582006, 58412240, 21709839, 2624521, 9890759, 24530960, 57938080, 12434020, 33565361, 13444990, 32946916, 29446623, 17628191, 17317684, 19931185, 23833529, 24147194, 58616788, 30017378, 37352518, 39006299, 5978070, 11544356, 38786418, 17859249, 4629346, 16785709, 31945261, 50088983, 44159911, 26297301, 40421512, 29605837, 52958077, 39330456],
   [55650966, 30261695, 20539934, 51446258, 22160744, 45396836, 30368969, 59072284, 33212056, 22598403, 11945189, 17963483, 61950734, 8721761, 64136574, 53180770, 36226985, 4677353, 45305319, 61631187, 62904072, 31421648, 17628191, 17317684, 19931185, 30088456, 30687489, 58858436, 34267763, 33803205, 66150320, 27903459, 59514084, 17828188, 54594185, 19177267, 48571131, 35490165, 6288902, 29414908, 28194178, 34802799, 8075104, 32957617, 36113037],
   [25115580, 16770467, 29184781, 13670774, 44585869, 64110023, 42167950, 15748863, 28977250, 14909787, 21347562, 43843095, 12070841, 24353665, 17328222, 35109482, 47892388, 39046498, 45194131, 7251007, 11393110, 10607980, 50842230, 37234154, 11958711, 57321725, 39031332, 22669592, 20859762, 10459104, 13072747, 9916890, 36398641, 2899746, 25996353, 17624726, 37496680, 29096197, 373287, 21992465, 12010628, 11389873, 8286334, 34854964, 9116946],
   [59365917, 41075924, 38891256, 65731119, 35504842, 51133578, 7000008, 2191952, 44295081, 55903504, 16533200, 43201829, 9926907, 66469194, 37589599, 35629059, 61393716, 49925695, 28147245, 9169626, 55754490, 32356012, 680781, 27275919, 15944948, 1993401, 26411656, 50790077, 25731545, 36957063, 7879881, 65820375, 38464395, 28179442, 15069779, 4884716, 57858553, 21529317, 44843323, 43488242, 5280422, 21549267, 54921708, 38808216, 50884481],
   [8418575, 25999629, 59372814, 18190707, 3530209, 20646760, 2248518, 60871888, 25394838, 42504026, 6454190, 43877010, 33167537, 33950892, 50228120, 42554701, 14071329, 19830356, 51003088, 15520637, 33949694, 13588976, 4577243, 61480045, 25746248, 46436659, 26397839, 1376593, 52760920, 26458249, 47222414, 48904657, 64139015, 10264108, 55375484, 15381025, 16688085, 57814195, 16209387, 16644845, 30323721, 21316246, 9761714, 31406867, 54529012],
   [63080868, 51890153, 57242578, 12907121, 48848940, 56870320, 50739906, 12420479, 55378106, 22099746, 21121211, 1331316, 25011939, 29010289, 22722530, 33267073, 50467282, 2855218, 102856, 58488881, 16708150, 65187134, 50842230, 37234154, 11958711, 41007205, 22135823, 42721718, 17195327, 40110921, 16718301, 36628432, 17414706, 38530696, 42654232, 57701024, 5702387, 10747199, 49739725, 48472142, 60623972, 15480313, 1489652, 27997559, 65698866],
   [59678957, 45480401, 30406215, 38539137, 40420663, 55635375, 46737922, 46651805, 44942809, 498657, 57932837, 16632167, 36938795, 7808951, 29734138, 30369861, 23367697, 29723096, 63509154, 10246487, 3612357, 8818079, 33894820, 47192389, 7972474, 56190110, 8551666, 16136718, 17072436, 60801143, 49432019, 58383886, 42099378, 46406351, 11939953, 28585102, 37203473, 21564236, 14408344, 41759569, 26674757, 41100789, 54319293, 64815436, 50782589],
   [66795819, 62704382, 8485041, 27191982, 62193038, 62607062, 27370945, 22649006, 66461131, 55404847, 25709222, 26569662, 40096971, 58660243, 7855461, 51636572, 5229004, 9404217, 54810933, 46468663, 5188948, 3382259, 33894820, 47192389, 7972474, 12912150, 17859990, 34653359, 8659109, 43264779, 25556721, 7436489, 63473876, 48881950, 3129826, 43408473, 20655080, 67073940, 42535553, 61146787, 32862614, 38616216, 66174552, 14725496, 21306388],
   [63393908, 56294630, 48757537, 52823998, 53764761, 61372117, 23368961, 56880332, 56025834, 33803758, 62520848, 41870513, 52023827, 37458905, 14867069, 48739360, 45238278, 14861548, 2517854, 487155, 47556867, 25767210, 16947410, 57150624, 3986237, 28095055, 4275833, 8068359, 8536218, 63955001, 58270439, 29191943, 21049689, 56757605, 39524406, 14292551, 52156166, 10782118, 7204172, 54434214, 46891808, 65961825, 26014265, 21282474, 55703260],
   [3401911, 6409752, 26836363, 41476843, 8428277, 1234945, 4001984, 32877533, 10435297, 21601089, 30297233, 51808008, 55182003, 21201338, 60097251, 2897212, 27099585, 61651528, 52293079, 36709331, 40498045, 28966803, 16947410, 57150624, 3986237, 51925954, 13584157, 26585000, 122891, 46418637, 34395141, 45353405, 42424187, 59233204, 30714279, 29115922, 35607773, 56291822, 35331381, 6712573, 53079665, 39763250, 37869524, 38301393, 26227059]]

/-- N2c minor certificate 6: rows 0..42, cols 2..44 (det mod P = 24395732). -/
def n2cR6 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42]
def n2cC6 : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cS6 : List (List ℕ) := [[15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [61671799, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 25282329, 15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 15068424, 43030449, 43030449, 61671799, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245, 15495622],
   [35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 14661890, 44527543, 57322967, 31708898],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 31887850, 61585314, 10013370, 6076963, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 56236711, 13351160, 36241625, 51784342, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 15068424, 61671799, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 32256487, 36241625, 46006646, 42830140, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 6076963, 950555, 51761187, 21081840, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [63031064, 11301318, 15495622, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 30508489, 51761187, 40895904, 13308995, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 25282329, 15495622, 15495622, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 32122605, 40895904, 63518117, 33196128, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 15068424, 61671799, 43030449, 43030449, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 28109120, 62321203, 27281786, 20008787, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 13308995, 4955012, 1167113, 47864976, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 11301318, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 33196128, 1167113, 10522293, 55434195, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 11301318, 15495622, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 3510172, 10522293, 15480703, 50540108, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 11301318, 15495622, 25282329, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 47864976, 15480703, 41832548, 67073729, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 15495622, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 55434195, 41832548, 37412653, 24324252, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 15068424, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 20343947, 35141361, 55898772, 32397634, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 67073729, 41924079, 7876856, 40754344, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 43030449, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 11975041, 62012112, 49464710, 39599045, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 57852655, 3544103, 14815804, 54139551, 57656413, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40754344, 14815804, 44367567, 37819892, 57401204, 20769422, 15495622],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 12922069, 44367567, 45542965, 6679643, 20769422, 15495622]]
def n2cT6 : List (List ℕ) := [[23977725, 50527904, 42599135, 38546049, 61977381, 17487705, 237711, 25442760, 66007719, 17899513, 20662518, 19576352, 31924171, 56661933, 52765443, 4655410, 30058060, 59303554, 41460540, 23412589, 53881862, 47009064, 57788598, 35544240, 5013889, 51142594, 60231898, 8642807, 54246525, 35311692, 11864, 50430255, 40827938, 52707418, 26570605, 15959921, 54963183, 45317979, 54269433, 5678509, 66838788, 25177609, 10935834],
   [10682589, 24340015, 53790399, 23437345, 57303106, 50971749, 8618507, 64648659, 11348084, 6936398, 23571493, 37137629, 39200736, 13641192, 36119640, 24454602, 46685481, 36658106, 44348362, 15486431, 12546661, 33120076, 55799281, 16516245, 12285978, 4087930, 43039613, 40137984, 46549494, 26004658, 22012314, 53576755, 12407617, 2783076, 1583815, 7112702, 8951936, 64528544, 45929476, 35680018, 26786963, 47185321, 58861424],
   [39599584, 6781696, 28001952, 51121196, 62533296, 41572823, 55664110, 51632230, 65316039, 23315310, 19465329, 62188686, 50911632, 13164506, 6423706, 50701621, 5798264, 25252512, 63531267, 54953762, 57503803, 61705225, 33964403, 36652820, 23510449, 872329, 48986714, 49915886, 13972999, 50029932, 6321787, 25213862, 6133952, 26397540, 54526384, 52975940, 4621870, 52577637, 43267753, 23192199, 46322242, 65095457, 19089129],
   [57419172, 32950074, 54879498, 13046252, 10413109, 62754779, 24271942, 53764320, 61147612, 40128076, 2125979, 37281850, 35708547, 38228123, 29564484, 31660726, 42746985, 46563131, 35652669, 23068503, 6856967, 35256798, 9787019, 59074840, 24073820, 2277749, 10748549, 9752992, 11218183, 23077900, 62259347, 61386576, 1142362, 16824575, 52623648, 14668590, 19966960, 19250959, 9021299, 18121052, 61870400, 66964133, 32093806],
   [0, 14877894, 1445205, 35876868, 23153630, 41419707, 43797332, 64865829, 4376956, 37137050, 49933899, 15069896, 56663986, 18092428, 33770376, 63362372, 20809911, 12303114, 33529387, 33579472, 0, 0, 0, 0, 20249900, 51482525, 10456226, 8158079, 4539407, 12856928, 14266301, 10271765, 34680386, 30895893, 9200542, 35360433, 13310517, 40784640, 24239072, 42690444, 52632233, 15519325, 63199633],
   [0, 0, 22126917, 21769901, 37471751, 13191292, 29609957, 30576052, 3832813, 34862422, 38116897, 30511222, 56752941, 41647668, 40229001, 6829685, 49167785, 9381149, 38563520, 28545339, 0, 0, 0, 0, 0, 16190935, 59553391, 17318874, 6103796, 16644867, 18614985, 34878298, 23518982, 46204876, 48291665, 33483247, 57398676, 23770964, 17909433, 24845171, 29858937, 39399895, 9876310],
   [0, 0, 0, 39264713, 64949770, 35525525, 38147922, 3873399, 37109664, 6759889, 2604806, 39113352, 17700302, 12973717, 45630528, 12635093, 24252053, 62257934, 15496080, 51612779, 0, 0, 0, 0, 0, 0, 30884743, 1812323, 889818, 2155344, 59122347, 13838522, 39912344, 61369523, 33359768, 64236745, 38736865, 55984962, 33423036, 35839478, 46160302, 26347955, 19022308],
   [0, 0, 0, 0, 53091197, 21088136, 8777261, 49227403, 54692393, 52052575, 20690920, 49722213, 58109203, 6562716, 54973848, 64621798, 5470125, 3165665, 24307350, 42801509, 0, 0, 0, 0, 0, 0, 0, 26370933, 56314499, 59980338, 9167227, 26638288, 63788588, 15025530, 65141690, 64979040, 36404691, 17850403, 65211608, 32024221, 4348120, 67070442, 28714753],
   [0, 0, 0, 0, 0, 58148812, 30418573, 8555838, 10989877, 31819896, 26898577, 33605640, 1531275, 64232168, 33360580, 6263880, 11186132, 16429312, 62278035, 4830824, 0, 0, 0, 0, 0, 0, 0, 0, 40787155, 40091188, 22143965, 36827855, 64106113, 48729756, 15661176, 7873347, 26282651, 35766224, 3663352, 2358939, 42600916, 58691185, 52594744],
   [0, 0, 0, 0, 0, 0, 53332030, 25968035, 20642506, 22785778, 27840441, 16695414, 8628594, 31919825, 38088465, 31878940, 16160705, 38340494, 63746863, 3361996, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58589734, 18613815, 322565, 37958597, 4185999, 4410016, 33220541, 7050359, 18042884, 42815637, 31138793, 34283673, 31155861, 227220],
   [0, 0, 0, 0, 0, 0, 0, 7340794, 46255965, 24228895, 31179986, 25742905, 45680861, 61344977, 10749807, 10900789, 11351575, 27411065, 20564279, 46544580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53347404, 56235326, 3897254, 56682469, 38028122, 5013000, 21382930, 9124180, 42302907, 25327548, 23797904, 49198253, 703602],
   [0, 0, 0, 0, 0, 0, 0, 0, 18312532, 41048581, 63325082, 51668503, 65142930, 61262861, 18765051, 10920902, 32730854, 33906481, 26679344, 40429515, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17163445, 51069865, 12088043, 25766677, 53053347, 6466249, 59297180, 15501426, 47791348, 26621418, 12644856, 53403276],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 6792747, 18423426, 29105608, 65611342, 11488234, 30370421, 42381792, 35794757, 29111901, 28759954, 38348905, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56273451, 54709077, 13707149, 14992474, 6441839, 16159968, 64989180, 7527094, 53017545, 42432670, 57815848],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12034598, 29565262, 2213688, 40017283, 25326452, 51449749, 4213104, 2487118, 64959614, 2149245, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49950847, 62493208, 48157455, 22588620, 51188179, 49744520, 64952930, 60013315, 42025621, 18304729],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14675712, 55428953, 44609416, 3296150, 22400358, 32702783, 15800947, 14293419, 52815440, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61443588, 63930129, 45758593, 1398689, 62238952, 29577172, 14303599, 9716314, 46756893],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41686469, 63745869, 58773478, 51936644, 11057226, 57888323, 38402089, 28706770, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44285172, 10135997, 21400060, 64273832, 20947958, 11177342, 26851254, 57921185],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32955607, 34311844, 48321697, 41582324, 14747419, 106090, 67002769, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12100574, 59418114, 35126499, 59892871, 5655685, 59609222, 46872214],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36422436, 40513789, 56183897, 53731124, 17532810, 49576049, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29261417, 33134937, 56271333, 57942939, 3761882, 61359236],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7988780, 57225931, 12199557, 4957328, 62151531, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19130450, 21988869, 52070142, 41681689, 32080266],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62322505, 23732620, 31242168, 35866691, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23714002, 28479836, 33671278, 20769484],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41322045, 42947317, 24161542, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35364239, 4279034, 49948356],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41322045, 56369084, 10739775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35364239, 4279034, 49948356],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62692702, 8484531, 58624328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51964668, 28784300, 63040485],
   [65902780, 29212931, 18382293, 54976537, 37403038, 3661436, 50153361, 48026789, 825855, 3352580, 18057541, 52426595, 26388516, 41389624, 10757562, 30062872, 44565314, 6097222, 14129300, 61367246, 60251892, 31852061, 57321840, 40450679, 13016798, 62306343, 55489365, 43849539, 43201180, 40625090, 67099961, 12508953, 2933476, 61132725, 63958120, 4807274, 9109257, 16343160, 43183999, 12518333, 35475055, 14581874, 30216250],
   [63118088, 38716704, 8648406, 26309520, 39998271, 26055184, 46056118, 34848733, 61191411, 63145380, 36829919, 44347326, 5011577, 64487625, 57012099, 36729445, 23511719, 16740140, 47346034, 34240174, 16972275, 47672436, 8072210, 34846070, 829497, 58536569, 33637763, 49240211, 42386335, 52323269, 50346996, 29624152, 40331753, 38976454, 28107692, 50026640, 30355527, 8445319, 15666670, 58034730, 26071685, 45919948, 38076763],
   [44237055, 23175427, 38918137, 50313575, 59896307, 13702284, 17914088, 26328877, 28330683, 20127367, 49284037, 26403369, 27957869, 19137244, 32181313, 8087140, 51565139, 25958275, 20186802, 35736020, 13226997, 20099795, 9320261, 33081645, 57380052, 3141686, 15593689, 40787309, 12883506, 23575724, 21836678, 5025962, 60657674, 20097828, 41510147, 65860597, 59793409, 52598444, 60946962, 20493915, 51476575, 5562079, 22312316],
   [0, 38809198, 65663654, 46503091, 43990649, 16958166, 57811719, 21651388, 31840002, 10771865, 42476572, 23541917, 54472231, 55385935, 11919121, 55031032, 16640950, 48412474, 29795224, 37313635, 0, 0, 0, 0, 46858959, 15626334, 19967919, 43343639, 56797855, 33798047, 58728796, 48827993, 46098265, 35235632, 21990190, 47556496, 5467530, 50330194, 14869985, 25516741, 14816680, 2658077, 44254573],
   [0, 0, 40447346, 449789, 66295507, 41399288, 4408954, 16447088, 4139507, 41998066, 11609127, 15917984, 18658272, 35109383, 27133213, 57096732, 59384913, 25147705, 46342179, 20766680, 0, 0, 0, 0, 0, 38188443, 5666601, 17564289, 3517923, 17898045, 64886015, 15543914, 24943481, 12150160, 62562254, 7747631, 2739383, 13805453, 63786022, 65720598, 28700598, 41464979, 37888433],
   [0, 0, 0, 14422379, 2159089, 40543381, 65651223, 8333324, 65265283, 59550716, 20100029, 21140901, 36631673, 52280021, 58738844, 52180959, 61757830, 808956, 5055254, 62053605, 0, 0, 0, 0, 0, 0, 36224116, 65296536, 25431886, 24862327, 39189951, 5568949, 23261107, 1292267, 8379598, 18182971, 39163804, 6933877, 59079557, 61392769, 55529328, 50335829, 42410772],
   [0, 0, 0, 0, 595895, 46020723, 31961464, 5627029, 65263312, 3354208, 66351765, 5224374, 1895512, 44831595, 22388092, 54716972, 43597673, 66381722, 24040379, 43068480, 0, 0, 0, 0, 0, 0, 0, 40737926, 10794360, 40856974, 33123212, 12464690, 26148293, 743008, 41359901, 15315754, 35142259, 9810745, 65702544, 19977990, 58892797, 15431794, 46961640],
   [0, 0, 0, 0, 0, 62647139, 36690286, 51212227, 9863017, 31274582, 27453722, 51541634, 6719300, 18360849, 22353199, 58415863, 14260437, 39180160, 34123480, 32985379, 0, 0, 0, 0, 0, 0, 0, 0, 26321704, 27017671, 58726349, 41154537, 55378943, 16405711, 21461439, 66036256, 59543136, 47467857, 27004924, 61753757, 7040572, 15136665, 43039755],
   [0, 0, 0, 0, 0, 0, 355062, 41140824, 52629877, 43810619, 28171084, 41347443, 29412838, 62950547, 52459583, 6755159, 299943, 21187316, 21027578, 46081281, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8519125, 48495044, 38981935, 10239130, 42590324, 36912092, 35846157, 44348595, 5310166, 24868130, 25845076, 45576882, 7718942, 41401990],
   [0, 0, 0, 0, 0, 0, 0, 46346298, 20852894, 36087217, 17505447, 40357825, 11245609, 4731812, 63596625, 63137786, 37021703, 61939499, 47498224, 19610635, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13761455, 10873533, 6938154, 22826172, 9708317, 43924655, 30034398, 35532655, 38051773, 34626532, 56062010, 59043549, 30283803],
   [0, 0, 0, 0, 0, 0, 0, 0, 31477911, 26060278, 10054445, 57010579, 62708211, 62633260, 6071158, 17112934, 18863074, 43137275, 41723286, 25385573, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49945414, 16038994, 45758989, 66575345, 31998489, 8531050, 37760152, 13324909, 63066736, 24291216, 3266275, 1223415],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 46894345, 48685433, 23327539, 13177423, 57388583, 645273, 58637186, 30310715, 58415164, 13361799, 53747060, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10835408, 12399782, 59066981, 55295115, 27009001, 41859457, 61246535, 44777474, 59804305, 4283556, 47973526],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56113932, 5318890, 49232880, 18982869, 15322690, 1804810, 19714533, 65175234, 26399866, 40708993, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45246969, 28523821, 25195302, 21307122, 33226319, 53864962, 19849250, 438909, 43002064, 24019475],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39011380, 11679906, 56652695, 29500865, 17797351, 50049683, 22973236, 33505136, 33603723, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5665271, 3178730, 9249692, 6292056, 55982717, 66736544, 366238, 43744046, 55508374],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 65687709, 3362990, 48127413, 1564088, 20390270, 935977, 47711172, 19397687, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22823687, 56972862, 40539951, 61869898, 4965688, 60357369, 32344498, 16206627],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20731485, 32797015, 10798382, 35409463, 38107689, 6803562, 60305297, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55008285, 7690745, 12851910, 52335978, 6118248, 3768260, 58874219],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12948492, 53500732, 11783487, 31201753, 10832817, 56276042, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61940011, 59034871, 57451502, 1561262, 17075730, 63414395],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45698312, 9882928, 20805240, 15314089, 51794770, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47978409, 45119990, 45809316, 14240077, 62283005],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58473446, 9272177, 42716341, 24392518, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43394857, 2290763, 22250488, 6484928],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9272177, 51351754, 15757105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2290763, 22250488, 6484928]]

/-- N2c minor certificate 7: rows 0..42, cols 19..44 (det mod P = 22618087). -/
def n2cR7 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 42]
def n2cC7 : List ℕ := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cS7 : List (List ℕ) := [[15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422, 15495622],
   [15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422, 15495622],
   [63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422, 15495622],
   [15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245, 15495622],
   [26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 14661890, 44527543, 57322967, 31708898],
   [43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [63031064, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 12922069, 44367567, 45542965, 6679643, 20769422, 15495622]]
def n2cT7 : List (List ℕ) := [[44020079, 7455430, 16824264, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 37104211, 28989464, 25762093, 517955, 1616864, 500468, 11504810, 50601373, 22634604, 9627080],
   [30231768, 15765880, 23616263, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 19067038, 35349376, 66050977, 33199726, 15088108, 59528887, 41517456, 54598289, 20427650, 34275245],
   [6372153, 24337145, 37141064, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 16728599, 16357722, 16380240, 27992600, 54906687, 21623932, 7529448, 35787683, 1686099, 30368661],
   [10195274, 18804636, 56388968, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 5338853, 2382351, 60754229, 41771391, 45643026, 20216090, 50251042, 47501917, 29351036, 63427934],
   [46739843, 62172042, 4936817, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 14557495, 45685953, 33184234, 30011733, 43535046, 40387231, 57806624, 61819641],
   [32949246, 696724, 66412135, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 820746, 35162805, 36238422, 38128059, 12105955],
   [41377596, 62522010, 4586849, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 66288113, 31946054, 29896416, 22072741, 65096813],
   [32949246, 696724, 66412135, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 820746, 35162805, 36238422, 38128059, 12105955],
   [41377596, 62522010, 4586849, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 66288113, 31946054, 29896416, 22072741, 65096813],
   [29447472, 28832360, 38276499, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 51236637, 401314, 43576062, 66578807, 66515694, 56171416, 14087745, 55683158, 61880786],
   [11181858, 46783109, 20325750, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 12848507, 2817511, 8973306, 10957991, 31455943],
   [63144984, 16435625, 50673234, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 30781395, 59260851, 16724588, 8340846, 54260352, 64291348, 57161532, 49242809, 45746825],
   [11181858, 46783109, 20325750, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 12848507, 2817511, 8973306, 10957991, 31455943],
   [51362833, 9065787, 58043072, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 33296619, 6989205, 35357300, 35679418, 10617726, 44967568, 13801785, 46373119, 20766303],
   [59352672, 11585231, 55523628, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32721354, 15413076, 2729723, 32448836, 13127019, 53776421, 54894303, 60780706, 32149280],
   [59333568, 37705412, 29403447, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55213590, 15023587, 51962733, 22198407, 60485370, 16333193, 6377978, 35480731],
   [11661431, 54368610, 12740249, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 66254623, 1097127, 27030834, 3627479, 38701358, 1078818],
   [62665411, 8850124, 58258735, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 854236, 66011732, 40078025, 62507359, 21499442, 9015091],
   [22378920, 15851664, 51257195, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1097127, 27030834, 52652140, 65502068, 28878275],
   [54144765, 15511772, 51597087, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40078025, 37741431, 34984508, 10874089],
   [41322045, 42947317, 24161542, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35364239, 4279034, 49948356],
   [41322045, 56369084, 10739775, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35364239, 4279034, 49948356],
   [62692702, 8484531, 58624328, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51964668, 28784300, 63040485],
   [34337043, 6078703, 49531275, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 22503486, 45366761, 64564504, 49943178, 65896211, 66733508, 24925822, 64430331, 66820772, 64752245],
   [24532536, 46533557, 65759784, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 49678027, 5510641, 63932532, 58335748, 51746746, 32300699, 66129723, 1942006, 31600083, 17839246],
   [9272177, 51351754, 15757105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2290763, 22250488, 6484928]]

/-- N2c minor certificate 8: rows 0..27, cols 4..29 (det mod P = 22483997). -/
def n2cR8 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 27]
def n2cC8 : List ℕ := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
def n2cS8 : List (List ℕ) := [[15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799],
   [43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799],
   [43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799],
   [63031064, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064],
   [15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064],
   [63031064, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048],
   [15495622, 63031064, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048],
   [43030449, 43030449, 61671799, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799],
   [15495622, 15495622, 15495622, 63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799],
   [15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799],
   [15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064],
   [35550333, 35550333, 35550333, 35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385],
   [43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799],
   [43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799],
   [61671799, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 32256487, 36241625, 46006646, 42830140, 309759, 55855799]]
def n2cT8 : List (List ℕ) := [[27120593, 37362326, 26341779, 12579564, 28163121, 18107341, 38325841, 12579564, 25123112, 18107341, 11844571, 12579564, 18842334, 18107341, 11844571, 7142204, 5437360, 18842334, 63750604, 49271369, 64118130, 12066699, 34924689, 28567914, 62523036, 15986009],
   [23339240, 62564685, 38893638, 58669842, 57332085, 6445645, 1439078, 58669842, 14566806, 6445645, 20635953, 58669842, 44479534, 6445645, 20635953, 63767233, 62011468, 44479534, 44464538, 58393704, 42266402, 64592104, 28164808, 29738590, 47045012, 18481205],
   [4806256, 7196296, 60143024, 23937189, 1549098, 3813229, 41600670, 23937189, 5968470, 3813229, 56828495, 23937189, 38030782, 3813229, 56828495, 489762, 23447427, 38030782, 19810413, 64176595, 54936154, 45790182, 19869621, 21219944, 44021260, 25477961],
   [8969079, 32012597, 38973638, 30876680, 17605825, 4524112, 17815606, 30876680, 51647757, 4524112, 13442189, 30876680, 21958603, 4524112, 13442189, 44750538, 53235001, 21958603, 29745294, 23471516, 64398732, 31709160, 55460958, 17107849, 56220672, 64557170],
   [52339459, 28334808, 25417141, 49421792, 10849718, 17687067, 56259141, 49421792, 23582756, 17687067, 49421792, 49421792, 17687067, 17687067, 49421792, 0, 49421792, 17687067, 0, 0, 0, 0, 51091024, 8444661, 0, 10194433],
   [22126917, 22126917, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 16190935, 59920831, 40372623],
   [0, 53687092, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 19791109],
   [0, 0, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 58761568],
   [0, 53687092, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 59920831, 58761568],
   [0, 40265319, 22594932, 9173153, 23560516, 57935706, 43548343, 9173153, 10138749, 57935706, 9173153, 9173153, 57935706, 57935706, 9173153, 0, 9173153, 57935706, 0, 0, 0, 0, 0, 0, 61717838, 65174976],
   [0, 0, 43548343, 43548343, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 19791109],
   [0, 66675904, 43115388, 43981298, 9621675, 23127561, 40168768, 43981298, 30836748, 23127561, 43981298, 43981298, 23127561, 23127561, 43981298, 0, 43981298, 23127561, 0, 0, 0, 0, 0, 0, 2766462, 19791109],
   [0, 53687092, 43548343, 3283018, 53783641, 63825841, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 59920831, 58761568],
   [0, 40265319, 22594932, 9173153, 36982283, 57935706, 30126576, 9173153, 10138749, 57935706, 9173153, 9173153, 57935706, 57935706, 9173153, 0, 9173153, 57935706, 0, 0, 0, 0, 0, 0, 61717838, 65174976],
   [0, 0, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 19791109],
   [0, 0, 49438472, 49438472, 23560516, 17670387, 43548343, 49438472, 10138749, 17670387, 49438472, 49438472, 17670387, 17670387, 49438472, 0, 49438472, 17670387, 0, 0, 0, 0, 0, 0, 0, 65174976],
   [0, 53687092, 43548343, 3283018, 53783641, 63825841, 13325218, 3283018, 13518332, 63825841, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 59920831, 58761568],
   [0, 53687092, 43548343, 3283018, 53783641, 63825841, 13325218, 3283018, 13518332, 63825841, 56970110, 3283018, 63825841, 63825841, 3283018, 0, 3283018, 63825841, 0, 0, 0, 0, 0, 0, 59920831, 58761568],
   [0, 0, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 23560516, 56970110, 43548343, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 19791109],
   [0, 0, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 23560516, 56970110, 43548343, 10138749, 23560516, 43548343, 0, 43548343, 23560516, 0, 0, 0, 0, 0, 0, 0, 19791109],
   [0, 53687092, 43548343, 3283018, 53783641, 63825841, 13325218, 3283018, 13518332, 63825841, 56970110, 3283018, 10138749, 63825841, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 59920831, 58761568],
   [0, 53687092, 43548343, 3283018, 53783641, 63825841, 13325218, 3283018, 13518332, 63825841, 56970110, 3283018, 10138749, 63825841, 56970110, 0, 3283018, 63825841, 0, 0, 0, 0, 0, 0, 59920831, 58761568],
   [0, 0, 45736347, 45736347, 6127063, 21372512, 60981796, 45736347, 33354453, 21372512, 58870234, 45736347, 8238625, 21372512, 58870234, 53974972, 58870234, 8238625, 0, 0, 0, 0, 0, 0, 0, 37164251],
   [63545629, 5532685, 30575310, 57674186, 62763733, 3196709, 55141693, 57674186, 48266525, 3196709, 41448216, 57674186, 19422679, 3196709, 41448216, 21486887, 36187299, 19422679, 19295906, 46932547, 52574691, 41281620, 57692557, 12128494, 20216582, 4787708],
   [10333175, 48260887, 6079502, 41766233, 57325241, 57638844, 17563362, 41766233, 15316349, 57638844, 37586171, 41766233, 61818906, 57638844, 37586171, 58400657, 50474435, 61818906, 17759178, 2774329, 16737460, 8274298, 53781368, 31586892, 24037069, 5343193],
   [40447346, 40447346, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38188443, 0, 18118294]]

/-- N2c minor certificate 9: rows 0..38, cols 15..43 (det mod P = 63382188). -/
def n2cR9 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 38]
def n2cC9 : List ℕ := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 40, 43]
def n2cS9 : List (List ℕ) := [[15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 31157861, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 31157861, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 31157861, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 31157861, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 31157861, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 6591181, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 31157861, 5322943],
   [63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 6591181, 20769422],
   [15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 6591181, 20769422],
   [63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 24807078, 20769422],
   [15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 24807078, 20769422],
   [15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 20769422],
   [15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 6591181, 26510245],
   [35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 28293413, 57322967],
   [43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 31157861, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 31157861, 5322943],
   [63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 67073729, 41924079, 7876856, 40754344, 6591181, 20769422]]
def n2cT9 : List (List ℕ) := [[47357388, 21074584, 36693175, 62975979, 8108843, 52993746, 38394807, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 37104211, 28989464, 25762093, 27912119, 55529270, 50054474],
   [2205185, 19191093, 51951453, 34965545, 33583069, 46689824, 59801178, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 19067038, 35349376, 66050977, 44983778, 47348950, 30200503],
   [30914775, 57694145, 33781318, 7001948, 30923403, 30154556, 31323653, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 16728599, 16357722, 16380240, 59993629, 47999263, 14156786],
   [66931448, 46027241, 10081807, 30986014, 60772595, 31655249, 43538355, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 5338853, 2382351, 60754229, 47963766, 30775706, 11419439],
   [20793338, 8284181, 30595051, 43104208, 59338455, 44284212, 22824647, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 14557495, 37103875, 39046226, 43891075],
   [49194156, 3442231, 21356934, 0, 55215592, 57645192, 9463667, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 19513322, 41920466, 2735956],
   [17914703, 63666628, 32330158, 53687092, 50384903, 51502657, 15606202, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 47595537, 24091266, 49961425],
   [49194156, 3442231, 21356934, 0, 55215592, 57645192, 9463667, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 19513322, 41920466, 2735956],
   [17914703, 63666628, 32330158, 53687092, 50384903, 51502657, 15606202, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 47595537, 24091266, 49961425],
   [9550423, 23607523, 14057100, 0, 64794872, 55365746, 11743113, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 51236637, 401314, 50474997, 36037357, 24355651],
   [12621791, 3731507, 44796808, 53687092, 52335024, 37085886, 30022973, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 36327464, 7848008, 17441726, 57330956, 1581711],
   [54487068, 63377352, 8890284, 0, 53265471, 4953104, 62155755, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 30781395, 59260851, 49667133, 8680776, 51115670],
   [12621791, 3731507, 44796808, 53687092, 52335024, 37085886, 30022973, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 36327464, 7848008, 17441726, 57330956, 1581711],
   [15534592, 1448528, 53022795, 0, 12905848, 1180216, 65928643, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 33296619, 6989205, 61462505, 27781336, 3288229],
   [3684529, 48236831, 31130535, 53687092, 6327037, 29651287, 37457572, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32721354, 15413076, 355450, 20382267, 44140802],
   [36063270, 37761277, 1698007, 0, 36846363, 28564489, 38544370, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55213590, 20379780, 39012464, 30609244],
   [32955607, 46377374, 0, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12100574, 7412406, 59903120],
   [0, 53687092, 53687092, 0, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66011732, 59903120],
   [0, 0, 53687092, 0, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59903120],
   [0, 0, 0, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59903120],
   [0, 0, 53687092, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66011732, 59903120],
   [0, 0, 53687092, 53687092, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66011732, 59903120],
   [0, 0, 0, 0, 1671681, 65437178, 1671681, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9649696],
   [31590818, 51302921, 22811763, 3099660, 3984693, 34074439, 21535539, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 22503486, 45366761, 64564504, 29397555, 59016336, 63122433],
   [51275857, 50309293, 10499738, 11466302, 16850819, 4945661, 40238821, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 49678027, 5510641, 63932532, 44634457, 44226659, 59509947],
   [20731485, 20731485, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55008285, 58599326, 0]]

/-- N2c minor certificate 10: rows 0..36, cols 13..38 (det mod P = 50143147). -/
def n2cR10 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 36]
def n2cC10 : List ℕ := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38]
def n2cS10 : List (List ℕ) := [[15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970],
   [63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907],
   [43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970],
   [63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540],
   [15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540],
   [15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907],
   [35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970],
   [63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 55434195, 41832548, 37412653, 24324252, 47168114, 40068907]]
def n2cT10 : List (List ℕ) := [[7852681, 36218446, 24967878, 6454020, 5719027, 24232885, 7142204, 17825674, 6454020, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 37104211, 49377841, 10729573, 20516985],
   [53856485, 49372111, 1406201, 34634316, 63709286, 30481171, 63767233, 4747827, 34634316, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 19067038, 18142441, 61181451, 41877736],
   [54680134, 3811367, 57459593, 4508378, 37399684, 23242040, 489762, 56969831, 4508378, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 16728599, 39812966, 10191689, 11985737],
   [33581994, 54687537, 2417189, 50418094, 32983603, 52091557, 44750538, 24775510, 50418094, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 5338853, 9792339, 2066442, 27505595],
   [32505780, 9579920, 20178348, 46930511, 46930511, 20178348, 0, 20178348, 46930511, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 42652384, 5575784, 35057456],
   [49000636, 36857204, 54965427, 12143432, 12143432, 54965427, 0, 54965427, 12143432, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 23253571, 6747819, 66082109],
   [18108223, 20039073, 55617942, 11490917, 11490917, 55617942, 0, 55617942, 11490917, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 43855288, 63931821, 27484855],
   [49000636, 36857204, 54965427, 12143432, 12143432, 54965427, 0, 54965427, 12143432, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 23253571, 6747819, 66082109],
   [18108223, 20039073, 55617942, 11490917, 11490917, 55617942, 0, 55617942, 11490917, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 43855288, 63931821, 27484855],
   [23016127, 25639166, 2623039, 64485820, 64485820, 2623039, 0, 2623039, 64485820, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 50421482, 64127523, 41066430],
   [38863270, 43699710, 58523532, 8585327, 8585327, 58523532, 0, 58523532, 8585327, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 13934013, 19165200, 11580742],
   [28245589, 13196567, 52059837, 15049022, 15049022, 52059837, 0, 52059837, 15049022, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 53174846, 51514440, 14877363],
   [55329459, 40912543, 39270176, 27838683, 27838683, 39270176, 0, 39270176, 27838683, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 27434751, 26819193, 65810988],
   [42098374, 64782075, 22683701, 44425158, 44425158, 22683701, 0, 22683701, 44425158, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 54414264, 8392708, 51745935],
   [14675712, 50322662, 22225183, 44883676, 44883676, 22225183, 0, 22225183, 44883676, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61443588, 32161090, 50287249],
   [0, 19658386, 19658386, 47450473, 47450473, 19658386, 0, 19658386, 47450473, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26504865, 0],
   [0, 62002568, 48580801, 18528058, 18528058, 48580801, 0, 48580801, 18528058, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820, 26458105],
   [0, 62002568, 62002568, 5106291, 5106291, 62002568, 0, 62002568, 5106291, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820, 26458105],
   [0, 62002568, 48580801, 5106291, 5106291, 62002568, 0, 62002568, 5106291, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820, 0],
   [0, 62002568, 48580801, 5106291, 18528058, 48580801, 0, 48580801, 18528058, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820, 0],
   [0, 62002568, 62002568, 18528058, 5106291, 48580801, 0, 48580801, 18528058, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820, 26458105],
   [0, 62002568, 62002568, 18528058, 5106291, 48580801, 0, 62002568, 5106291, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820, 26458105],
   [0, 29923460, 16789573, 37185399, 50319286, 29923460, 53974972, 29923460, 37185399, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41950523, 0],
   [10887704, 6390595, 14828521, 62268344, 46042374, 65711410, 21486887, 60450493, 62268344, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 22503486, 46852693, 8730035, 1389476],
   [27507109, 22917112, 11056367, 25419913, 21239851, 6876305, 58400657, 19764569, 25419913, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 49678027, 37159107, 51664394, 37811732],
   [39011380, 11679906, 39777385, 27331474, 27331474, 39777385, 0, 39777385, 27331474, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5665271, 3178730, 16821610]]

/-- N2c minor certificate 11: rows 0..28, cols 5..30 (det mod P = 62855922). -/
def n2cR11 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 28]
def n2cC11 : List ℕ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
def n2cS11 : List (List ℕ) := [[15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715],
   [43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715],
   [43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001],
   [63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001],
   [15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001],
   [63031064, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998],
   [43030449, 61671799, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575],
   [15495622, 15495622, 63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [15495622, 15495622, 15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001],
   [35550333, 35550333, 35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570],
   [43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715],
   [43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715],
   [63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 6076963, 950555, 51761187, 21081840, 58669064, 56929001]]
def n2cT11 : List (List ℕ) := [[14889914, 17175908, 29404232, 46581857, 1282673, 19907105, 29404232, 25059841, 1282673, 28669239, 29404232, 2017666, 1282673, 28669239, 7142204, 22262028, 2017666, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 38249535, 59823127, 12620132],
   [62275128, 20826612, 17641597, 22675885, 47473890, 36095278, 17641597, 46901513, 47473890, 46716567, 17641597, 18398920, 47473890, 46716567, 63767233, 20983223, 18398920, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 40084714, 56807451, 58570004],
   [50073408, 59974998, 9160046, 42981337, 18590372, 168431, 9160046, 48040947, 18590372, 42051352, 9160046, 52807925, 18590372, 42051352, 489762, 8670284, 52807925, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 29965486, 38510892, 27501453],
   [44506699, 42718536, 59538844, 63599822, 42970807, 38930468, 59538844, 35801158, 42970807, 42104353, 59538844, 60405298, 42970807, 42104353, 44750538, 14788306, 60405298, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 57433651, 38593680, 15906038],
   [36687097, 7082203, 53569467, 26740154, 13539392, 40368705, 53569467, 62791762, 13539392, 53569467, 53569467, 13539392, 13539392, 53569467, 0, 53569467, 13539392, 0, 0, 0, 0, 51091024, 21969975, 41645572, 36998093, 22085730],
   [12808842, 22534921, 58896711, 31771134, 8212148, 35337725, 58896711, 55688770, 8212148, 58896711, 58896711, 8212148, 8212148, 58896711, 0, 58896711, 8212148, 0, 0, 0, 0, 0, 53802771, 66822402, 24779029, 54728509],
   [39264713, 60228508, 64031715, 34683202, 3077144, 32425657, 64031715, 48842098, 3077144, 64031715, 64031715, 3077144, 3077144, 64031715, 0, 64031715, 3077144, 0, 0, 0, 0, 0, 0, 30884743, 11393526, 60086320],
   [0, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 58761568, 0],
   [0, 50638598, 51241613, 62225657, 15867246, 4883202, 51241613, 21156328, 15867246, 51241613, 51241613, 15867246, 15867246, 51241613, 0, 51241613, 15867246, 0, 0, 0, 0, 0, 0, 0, 46574711, 62323648],
   [0, 44689838, 21653995, 29892028, 45454864, 37216831, 21653995, 15867246, 45454864, 21653995, 21653995, 45454864, 45454864, 21653995, 0, 21653995, 45454864, 0, 0, 0, 0, 0, 0, 0, 5703189, 46742736],
   [0, 43548343, 43548343, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 19791109, 0],
   [0, 42945328, 18617821, 10425695, 48491038, 39364748, 18617821, 19915478, 48491038, 18617821, 18617821, 48491038, 48491038, 18617821, 0, 18617821, 48491038, 0, 0, 0, 0, 0, 0, 0, 4506434, 24401959],
   [0, 50638598, 64663380, 62225657, 2445479, 4883202, 51241613, 21156328, 15867246, 51241613, 51241613, 15867246, 15867246, 51241613, 0, 51241613, 15867246, 0, 0, 0, 0, 0, 0, 0, 46574711, 62323648],
   [0, 44689838, 21653995, 43313795, 45454864, 23795064, 21653995, 15867246, 45454864, 21653995, 21653995, 45454864, 45454864, 21653995, 0, 21653995, 45454864, 0, 0, 0, 0, 0, 0, 0, 5703189, 46742736],
   [0, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 19791109, 0],
   [0, 49438472, 49438472, 23560516, 17670387, 43548343, 49438472, 10138749, 17670387, 49438472, 49438472, 17670387, 17670387, 49438472, 0, 49438472, 17670387, 0, 0, 0, 0, 0, 0, 0, 65174976, 0],
   [0, 50638598, 64663380, 62225657, 2445479, 4883202, 64663380, 21156328, 2445479, 51241613, 51241613, 15867246, 15867246, 51241613, 0, 51241613, 15867246, 0, 0, 0, 0, 0, 0, 0, 46574711, 62323648],
   [0, 50638598, 64663380, 62225657, 2445479, 4883202, 64663380, 21156328, 2445479, 51241613, 64663380, 2445479, 2445479, 64663380, 0, 64663380, 2445479, 0, 0, 0, 0, 0, 0, 0, 46574711, 62323648],
   [0, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 23560516, 56970110, 43548343, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 0, 0, 19791109, 0],
   [0, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 23560516, 56970110, 43548343, 10138749, 23560516, 43548343, 0, 43548343, 23560516, 0, 0, 0, 0, 0, 0, 0, 19791109, 0],
   [0, 50638598, 64663380, 62225657, 2445479, 4883202, 64663380, 21156328, 2445479, 51241613, 64663380, 15867246, 2445479, 51241613, 0, 51241613, 15867246, 0, 0, 0, 0, 0, 0, 0, 46574711, 62323648],
   [0, 50638598, 64663380, 62225657, 2445479, 4883202, 64663380, 21156328, 2445479, 51241613, 64663380, 15867246, 2445479, 51241613, 0, 64663380, 2445479, 0, 0, 0, 0, 0, 0, 0, 46574711, 62323648],
   [0, 45736347, 45736347, 6127063, 21372512, 60981796, 45736347, 33354453, 21372512, 58870234, 45736347, 8238625, 21372512, 58870234, 53974972, 58870234, 8238625, 0, 0, 0, 0, 0, 0, 0, 37164251, 0],
   [22386994, 54226928, 45055685, 48949681, 15815210, 1846886, 45055685, 65091193, 15815210, 28829715, 45055685, 32041180, 15815210, 28829715, 21486887, 23568798, 32041180, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 21644493, 5464299, 57643760],
   [7035506, 49317860, 56611647, 25593348, 42793430, 49295255, 56611647, 40261703, 42793430, 52431585, 56611647, 46973492, 42793430, 52431585, 58400657, 65319849, 46973492, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59210390, 16977499, 51652484],
   [14422379, 50428694, 60047254, 19100439, 7061605, 48008420, 60047254, 31785093, 7061605, 60047254, 60047254, 7061605, 7061605, 60047254, 0, 60047254, 7061605, 0, 0, 0, 0, 0, 0, 36224116, 8397583, 7022539]]

/-- N2c minor certificate 12: rows 0..25, cols 2..27 (det mod P = 8651120). -/
def n2cR12 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
def n2cC12 : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
def n2cS12 : List (List ℕ) := [[15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282],
   [61671799, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282],
   [43030449, 62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282],
   [63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401],
   [15495622, 25282329, 15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401],
   [15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [43030449, 15068424, 43030449, 43030449, 61671799, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282],
   [15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391],
   [35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282],
   [63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 31887850, 61585314, 10013370, 6076963, 4626330, 63654391]]
def n2cT12 : List (List ℕ) := [[23977725, 46996422, 21899026, 66946556, 9087430, 31148759, 51568321, 66946556, 66827572, 31148759, 3086165, 66946556, 45449047, 31148759, 52646268, 66946556, 45449047, 18921898, 12226861, 52646268, 53881862, 47009064, 57788598, 35544240, 570375, 17818909],
   [10682589, 22440381, 947907, 54486926, 34191906, 47761746, 1263876, 54486926, 42858856, 47761746, 27659252, 54486926, 14395374, 47761746, 20744439, 54486926, 14395374, 8671392, 39090354, 20744439, 12546661, 33120076, 55799281, 16516245, 38517087, 23621460],
   [39599584, 17358580, 34288740, 40079523, 7124183, 1333400, 45718320, 40079523, 21205441, 1333400, 42970112, 40079523, 9185339, 1333400, 32227584, 40079523, 9185339, 49293673, 19148586, 32227584, 57503803, 61705225, 33964403, 36652820, 843877, 48861904],
   [57419172, 8212828, 50860127, 19796066, 39488574, 3443776, 45443883, 19796066, 26575822, 3443776, 56833706, 19796066, 14168992, 3443776, 9070850, 19796066, 14168992, 20902313, 49650322, 9070850, 6856967, 35256798, 9787019, 59074840, 61720757, 39255609],
   [0, 0, 41691718, 17687067, 25417141, 49421792, 10849718, 17687067, 56259141, 49421792, 23582756, 17687067, 49421792, 49421792, 17687067, 17687067, 49421792, 0, 49421792, 17687067, 0, 0, 0, 0, 51091024, 11544014],
   [0, 17318416, 23582756, 25289672, 43526103, 41819187, 9074055, 25289672, 58034804, 41819187, 11349943, 25289672, 41819187, 41819187, 25289672, 25289672, 41819187, 0, 41819187, 25289672, 0, 0, 0, 0, 19901937, 12974399],
   [0, 0, 23560516, 10138749, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373],
   [0, 0, 10138749, 10138749, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 50198461],
   [0, 17318416, 23582756, 11867905, 43526103, 41819187, 9074055, 25289672, 58034804, 41819187, 11349943, 25289672, 41819187, 41819187, 25289672, 25289672, 41819187, 0, 41819187, 25289672, 0, 0, 0, 0, 19901937, 26280487],
   [0, 12988812, 44530607, 18967254, 22578252, 48141605, 23582756, 18967254, 43526103, 48141605, 25289672, 18967254, 48141605, 48141605, 18967254, 18967254, 48141605, 0, 48141605, 18967254, 0, 0, 0, 0, 65258097, 26508014],
   [0, 0, 23560516, 23560516, 43548343, 43548343, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373],
   [0, 34566999, 8864788, 27663646, 58244071, 39445213, 34189337, 27663646, 15601106, 39445213, 59254481, 27663646, 39445213, 39445213, 27663646, 27663646, 39445213, 0, 39445213, 27663646, 0, 0, 0, 0, 19603427, 47965129],
   [0, 17318416, 23582756, 11867905, 43526103, 55240954, 9074055, 11867905, 58034804, 41819187, 11349943, 25289672, 41819187, 41819187, 25289672, 25289672, 41819187, 0, 41819187, 25289672, 0, 0, 0, 0, 19901937, 26280487],
   [0, 12988812, 44530607, 18967254, 22578252, 48141605, 37004523, 18967254, 30104336, 48141605, 25289672, 18967254, 48141605, 48141605, 18967254, 18967254, 48141605, 0, 48141605, 18967254, 0, 0, 0, 0, 65258097, 26508014],
   [0, 0, 23560516, 23560516, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373],
   [0, 0, 17670387, 17670387, 49438472, 49438472, 23560516, 17670387, 43548343, 49438472, 10138749, 17670387, 49438472, 49438472, 17670387, 17670387, 49438472, 0, 49438472, 17670387, 0, 0, 0, 0, 0, 10892065],
   [0, 17318416, 23582756, 11867905, 43526103, 55240954, 9074055, 11867905, 58034804, 55240954, 11349943, 11867905, 41819187, 41819187, 25289672, 25289672, 41819187, 0, 41819187, 25289672, 0, 0, 0, 0, 19901937, 26280487],
   [0, 17318416, 23582756, 11867905, 43526103, 55240954, 9074055, 11867905, 58034804, 55240954, 11349943, 11867905, 41819187, 55240954, 11867905, 11867905, 55240954, 0, 55240954, 11867905, 0, 0, 0, 0, 19901937, 26280487],
   [0, 0, 23560516, 23560516, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 23560516, 56970110, 43548343, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373],
   [0, 0, 23560516, 23560516, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 23560516, 56970110, 43548343, 10138749, 23560516, 43548343, 0, 43548343, 23560516, 0, 0, 0, 0, 0, 36892373],
   [0, 17318416, 23582756, 11867905, 43526103, 55240954, 9074055, 11867905, 58034804, 55240954, 11349943, 11867905, 41819187, 55240954, 25289672, 11867905, 41819187, 0, 41819187, 25289672, 0, 0, 0, 0, 19901937, 26280487],
   [0, 17318416, 23582756, 11867905, 43526103, 55240954, 9074055, 11867905, 58034804, 55240954, 11349943, 11867905, 41819187, 55240954, 25289672, 11867905, 41819187, 0, 55240954, 11867905, 0, 0, 0, 0, 19901937, 26280487],
   [0, 0, 21372512, 21372512, 45736347, 45736347, 6127063, 21372512, 60981796, 45736347, 33354453, 21372512, 58870234, 45736347, 8238625, 21372512, 58870234, 53974972, 58870234, 8238625, 0, 0, 0, 0, 0, 10772959],
   [65902780, 65415972, 17130160, 16898942, 26738857, 26970075, 45209833, 16898942, 16988180, 26970075, 14462591, 16898942, 16244859, 26970075, 27624158, 16898942, 16244859, 46206546, 47872388, 27624158, 60251892, 31852061, 57321840, 40450679, 49903863, 3413033],
   [63118088, 55919259, 18695566, 3241442, 24266265, 39720389, 47297041, 3241442, 67002538, 39720389, 4423021, 3241442, 56421780, 39720389, 53648910, 3241442, 56421780, 11783091, 27937298, 53648910, 16972275, 47672436, 8072210, 34846070, 3834974, 50342118],
   [44237055, 33788802, 45225492, 6113614, 58005770, 30008789, 60300656, 6113614, 22630028, 30008789, 27218536, 6113614, 15708501, 30008789, 20413902, 6113614, 15708501, 61608728, 35508920, 20413902, 13226997, 20099795, 9320261, 33081645, 7184136, 64966508]]

/-- N2c minor certificate 13: rows 0..32, cols 9..34 (det mod P = 41650464). -/
def n2cR13 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 32]
def n2cC13 : List ℕ := [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34]
def n2cS13 : List (List ℕ) := [[15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785],
   [43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785],
   [43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374],
   [43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785],
   [63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374],
   [15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374],
   [63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423],
   [43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273],
   [15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785],
   [15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374],
   [35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316],
   [43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785],
   [43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785],
   [63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 13308995, 4955012, 1167113, 47864976, 42009301, 21479374]]
def n2cT13 : List (List ℕ) := [[61824173, 25248170, 14423185, 295331, 16263720, 13688192, 14423185, 16998713, 16263720, 13688192, 7142204, 7280981, 16998713, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 51807017, 15215130, 36689298],
   [18014206, 2188628, 26189881, 35503801, 38925606, 55264851, 26189881, 9850636, 38925606, 55264851, 63767233, 29531507, 9850636, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 23668837, 3968534, 14495230],
   [61440243, 23445577, 39703893, 52055057, 55155384, 5486340, 39703893, 22264078, 55155384, 5486340, 489762, 39214131, 22264078, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 36924538, 21908362, 6868235],
   [16022508, 61622614, 8438014, 36826739, 26962778, 58112382, 8438014, 44397269, 26962778, 58112382, 44750538, 30796335, 44397269, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 53302016, 11695924, 25837756],
   [54843509, 65690773, 61512166, 29831877, 5596693, 61512166, 61512166, 5596693, 5596693, 61512166, 0, 61512166, 5596693, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 17380310, 32544001, 5355841],
   [61417663, 41754649, 33333538, 294522, 33775321, 33333538, 33333538, 33775321, 33775321, 33333538, 0, 33333538, 33775321, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 8736513, 62576384, 25274007],
   [5691196, 5149028, 39187052, 37229076, 27921807, 39187052, 39187052, 27921807, 27921807, 39187052, 0, 39187052, 27921807, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 58372346, 38989522, 5990927],
   [61417663, 41754649, 33333538, 294522, 33775321, 33333538, 33333538, 33775321, 33775321, 33333538, 0, 33333538, 33775321, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 8736513, 62576384, 25274007],
   [18116908, 66527690, 38016116, 38790324, 29092743, 38016116, 38016116, 29092743, 29092743, 38016116, 0, 38016116, 29092743, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 15984368, 53935777, 11035081],
   [27456501, 18604125, 32428058, 46241068, 34680801, 32428058, 32428058, 34680801, 34680801, 32428058, 0, 32428058, 34680801, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 63296481, 44172338, 2991422],
   [7340794, 56654965, 64486041, 48236330, 2622818, 64486041, 64486041, 2622818, 2622818, 64486041, 0, 64486041, 2622818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 53347404, 47012413, 26458209],
   [0, 23203396, 17402547, 43905463, 49706312, 17402547, 17402547, 49706312, 49706312, 17402547, 0, 17402547, 49706312, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47050966, 7246278],
   [0, 23700281, 55118043, 60726994, 11990816, 55118043, 55118043, 11990816, 11990816, 55118043, 0, 55118043, 11990816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28639440, 24018656],
   [0, 27541296, 20655972, 39567563, 46452887, 20655972, 20655972, 46452887, 46452887, 20655972, 0, 20655972, 46452887, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64660526, 38989138],
   [0, 23203396, 3980780, 43905463, 49706312, 17402547, 17402547, 49706312, 49706312, 17402547, 0, 17402547, 49706312, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5817607, 7246278],
   [0, 17402547, 2985585, 49706312, 64123274, 2985585, 2985585, 64123274, 64123274, 2985585, 0, 2985585, 64123274, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21140420, 38989138],
   [0, 23700281, 1430951, 60726994, 65677908, 55118043, 55118043, 11990816, 11990816, 55118043, 0, 55118043, 11990816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28639440, 24018656],
   [0, 23700281, 1430951, 60726994, 65677908, 55118043, 1430951, 65677908, 65677908, 1430951, 0, 1430951, 65677908, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28639440, 24018656],
   [0, 23203396, 3980780, 43905463, 63128079, 17402547, 3980780, 49706312, 49706312, 17402547, 0, 17402547, 49706312, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5817607, 7246278],
   [0, 23203396, 3980780, 43905463, 63128079, 17402547, 3980780, 49706312, 63128079, 3980780, 0, 3980780, 63128079, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5817607, 7246278],
   [0, 23700281, 1430951, 60726994, 65677908, 55118043, 1430951, 11990816, 65677908, 55118043, 0, 55118043, 11990816, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28639440, 24018656],
   [0, 23700281, 1430951, 60726994, 65677908, 55118043, 1430951, 11990816, 65677908, 55118043, 0, 1430951, 65677908, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28639440, 24018656],
   [0, 10469413, 45049817, 56639446, 22059042, 58183704, 45049817, 8925155, 22059042, 58183704, 53974972, 58183704, 8925155, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17839491, 5798444],
   [37517944, 14618302, 5959826, 50110146, 54911069, 56842715, 5959826, 4028180, 54911069, 56842715, 21486887, 51581798, 4028180, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45030811, 22143082, 6037456],
   [12022988, 45120408, 65631520, 5865586, 33773557, 61451458, 65631520, 37953619, 33773557, 61451458, 58400657, 7230863, 37953619, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 27685373, 24531768, 6179359],
   [46346298, 33657290, 20025365, 62777992, 47083494, 20025365, 20025365, 47083494, 47083494, 20025365, 0, 20025365, 47083494, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13761455, 25914053, 47896928]]

/-- N2c minor certificate 14: rows 0..29, cols 6..31 (det mod P = 9278812). -/
def n2cR14 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 29]
def n2cC14 : List ℕ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
def n2cS14 : List (List ℕ) := [[15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074],
   [43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074],
   [43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626],
   [63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626],
   [15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626],
   [61671799, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103],
   [15495622, 63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659],
   [15495622, 15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [15495622, 15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074],
   [15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626],
   [35550333, 35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261],
   [43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074],
   [43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074],
   [63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 30508489, 51761187, 40895904, 13308995, 56929001, 2661626]]
def n2cT14 : List (List ℕ) := [[57493942, 64229087, 50178544, 41140496, 16310418, 56655268, 11094746, 41140496, 55920275, 56655268, 41875489, 41140496, 55920275, 7142204, 49513064, 41875489, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 53173659, 22798807, 26050422],
   [19786828, 4130666, 39984505, 983912, 18786658, 64131575, 29654115, 983912, 26097686, 64131575, 39017801, 983912, 26097686, 63767233, 364342, 39017801, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 30506175, 29979302, 39542117],
   [3827885, 21636661, 21594207, 17554134, 21555561, 10196284, 1920057, 17554134, 43087590, 10196284, 51771687, 17554134, 43087590, 489762, 9706522, 51771687, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 64790808, 37652089, 2538674],
   [32395448, 46758778, 22222876, 25347345, 13198555, 10053447, 57042448, 25347345, 59727815, 10053447, 42781836, 25347345, 59727815, 44750538, 32411768, 42781836, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 57780384, 55734370, 37324049],
   [52940307, 14438678, 7379267, 36808643, 59729592, 30300216, 26708571, 36808643, 30300216, 30300216, 36808643, 36808643, 30300216, 0, 30300216, 36808643, 0, 0, 0, 0, 51091024, 21969975, 35043965, 33374232, 45654553, 18089241],
   [54439591, 31761475, 6338581, 10654837, 60770278, 56454022, 36576069, 10654837, 56454022, 56454022, 10654837, 10654837, 56454022, 0, 56454022, 10654837, 0, 0, 0, 0, 0, 53802771, 59920831, 7925853, 41045041, 19531213],
   [39164615, 51763835, 52354647, 30022213, 14754212, 37086646, 62399237, 30022213, 37086646, 37086646, 30022213, 30022213, 37086646, 0, 37086646, 30022213, 0, 0, 0, 0, 0, 0, 7188028, 10997144, 22458314, 18392637],
   [53091197, 20872095, 45844745, 49825446, 21264114, 17283413, 66433928, 49825446, 17283413, 17283413, 49825446, 49825446, 17283413, 0, 17283413, 49825446, 0, 0, 0, 0, 0, 0, 0, 26370933, 59520050, 43135965],
   [0, 13346605, 59198126, 51184652, 7910733, 15924207, 45876583, 51184652, 15924207, 15924207, 51184652, 51184652, 15924207, 0, 15924207, 51184652, 0, 0, 0, 0, 0, 0, 0, 0, 699626, 46044595],
   [0, 17965351, 60153595, 43927060, 6955264, 23181799, 13830174, 43927060, 23181799, 23181799, 43927060, 43927060, 23181799, 0, 23181799, 43927060, 0, 0, 0, 0, 0, 0, 0, 0, 15836616, 39296632],
   [0, 49309430, 28266960, 25577882, 38841899, 41530977, 11734223, 25577882, 41530977, 41530977, 25577882, 25577882, 41530977, 0, 41530977, 25577882, 0, 0, 0, 0, 0, 0, 0, 0, 29317055, 32863159],
   [0, 40009005, 51706438, 31892298, 65192864, 35216561, 42523064, 31892298, 35216561, 35216561, 31892298, 31892298, 35216561, 0, 35216561, 31892298, 0, 0, 0, 0, 0, 0, 0, 0, 30406172, 50609090],
   [0, 26768372, 59198126, 37762885, 7910733, 15924207, 45876583, 51184652, 15924207, 15924207, 51184652, 51184652, 15924207, 0, 15924207, 51184652, 0, 0, 0, 0, 0, 0, 0, 0, 699626, 46044595],
   [0, 17965351, 6466503, 43927060, 60642356, 23181799, 13830174, 43927060, 23181799, 23181799, 43927060, 43927060, 23181799, 0, 23181799, 43927060, 0, 0, 0, 0, 0, 0, 0, 0, 15836616, 39296632],
   [0, 49309430, 28266960, 38999649, 38841899, 28109210, 11734223, 25577882, 41530977, 41530977, 25577882, 25577882, 41530977, 0, 41530977, 25577882, 0, 0, 0, 0, 0, 0, 0, 0, 29317055, 32863159],
   [0, 3427643, 21200220, 12472522, 45908639, 54636337, 25577882, 12472522, 54636337, 54636337, 12472522, 12472522, 54636337, 0, 54636337, 12472522, 0, 0, 0, 0, 0, 0, 0, 0, 38765006, 41424584],
   [0, 26768372, 59198126, 37762885, 7910733, 29345974, 45876583, 37762885, 15924207, 15924207, 51184652, 51184652, 15924207, 0, 15924207, 51184652, 0, 0, 0, 0, 0, 0, 0, 0, 699626, 46044595],
   [0, 26768372, 59198126, 37762885, 7910733, 29345974, 45876583, 37762885, 15924207, 29345974, 37762885, 37762885, 29345974, 0, 29345974, 37762885, 0, 0, 0, 0, 0, 0, 0, 0, 699626, 46044595],
   [0, 49309430, 28266960, 38999649, 38841899, 28109210, 11734223, 38999649, 41530977, 28109210, 25577882, 25577882, 41530977, 0, 41530977, 25577882, 0, 0, 0, 0, 0, 0, 0, 0, 29317055, 32863159],
   [0, 49309430, 28266960, 38999649, 38841899, 28109210, 11734223, 38999649, 41530977, 28109210, 25577882, 38999649, 28109210, 0, 28109210, 38999649, 0, 0, 0, 0, 0, 0, 0, 0, 29317055, 32863159],
   [0, 26768372, 59198126, 37762885, 7910733, 29345974, 45876583, 37762885, 15924207, 29345974, 51184652, 37762885, 15924207, 0, 15924207, 51184652, 0, 0, 0, 0, 0, 0, 0, 0, 699626, 46044595],
   [0, 26768372, 59198126, 37762885, 7910733, 29345974, 45876583, 37762885, 15924207, 29345974, 51184652, 37762885, 15924207, 0, 29345974, 37762885, 0, 0, 0, 0, 0, 0, 0, 0, 699626, 46044595],
   [0, 29175268, 35196902, 30776838, 31911957, 36332021, 1154315, 30776838, 49465908, 36332021, 17642951, 30776838, 49465908, 53974972, 49465908, 17642951, 0, 0, 0, 0, 0, 0, 0, 0, 476021, 13635354],
   [57542832, 2159829, 29474951, 36253487, 21321616, 24617408, 25233370, 36253487, 8391438, 24617408, 52479457, 36253487, 8391438, 21486887, 3130521, 52479457, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 10451400, 33232539, 14016613],
   [20408772, 26538506, 17610653, 28228753, 57277950, 4067465, 65581373, 28228753, 66996262, 4067465, 32408815, 28228753, 66996262, 58400657, 12775667, 32408815, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 8309274, 18942426, 60598390],
   [595895, 8882286, 6154787, 13106914, 60954072, 54001945, 39845505, 13106914, 54001945, 54001945, 13106914, 13106914, 54001945, 0, 54001945, 13106914, 0, 0, 0, 0, 0, 0, 0, 40737926, 16490002, 28115519]]

/-- N2c minor certificate 15: rows 0..41, cols 18..43 (det mod P = 10802819). -/
def n2cR15 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 41]
def n2cC15 : List ℕ := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43]
def n2cS15 : List (List ℕ) := [[15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943],
   [43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943],
   [43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422],
   [43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422],
   [63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422],
   [15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422],
   [63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245],
   [35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 14661890, 44527543, 57322967],
   [43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943],
   [43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943],
   [63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40754344, 14815804, 44367567, 37819892, 57401204, 20769422]]
def n2cT15 : List (List ℕ) := [[31026356, 8108843, 16911243, 7368451, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 37104211, 28989464, 25762093, 517955, 1616864, 500468, 24641394, 40113475, 50054474],
   [15139877, 33583069, 61829701, 44661301, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 19067038, 35349376, 66050977, 33199726, 15088108, 59528887, 33753839, 34191779, 30200503],
   [38613545, 30923403, 1659242, 59818967, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 16728599, 16357722, 16380240, 27992600, 54906687, 21623932, 13197613, 63147061, 14156786],
   [20119923, 60772595, 51775172, 23418432, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 5338853, 2382351, 60754229, 41771391, 45643026, 20216090, 33186247, 58851786, 11419439],
   [4642543, 59338455, 48926755, 18182104, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 14557495, 45685953, 33184234, 30011733, 52151355, 62071939, 43891075],
   [6297443, 55215592, 63942635, 3166224, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 820746, 12584800, 0, 2735956],
   [60811416, 50384903, 45205214, 21903645, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 66288113, 54524059, 28498583, 49961425],
   [6297443, 55215592, 63942635, 3166224, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 820746, 12584800, 0, 2735956],
   [60811416, 50384903, 45205214, 21903645, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 66288113, 54524059, 28498583, 49961425],
   [2024098, 64794872, 57389844, 9719015, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 51236637, 401314, 43576062, 66578807, 66515694, 2247646, 0, 24355651],
   [35754080, 52335024, 5731107, 61377752, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 12848507, 3975506, 28498583, 1581711],
   [31354779, 53265471, 36307883, 30800976, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 30781395, 59260851, 16724588, 8340846, 54260352, 63133353, 0, 51115670],
   [35754080, 52335024, 5731107, 61377752, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 12848507, 3975506, 28498583, 1581711],
   [15173514, 12905848, 16353730, 50755129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 33296619, 6989205, 35357300, 35679418, 10617726, 63427317, 0, 3288229],
   [61619293, 6327037, 24161721, 42947138, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32721354, 15413076, 2729723, 32448836, 13127019, 46423903, 28498583, 44140802],
   [46175552, 36846363, 7631182, 59477677, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55213590, 15023587, 51962733, 22198407, 15636881, 0, 30609244],
   [52036544, 19245818, 32790726, 34318133, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 66254623, 1097127, 31369748, 28498583, 59903120],
   [42065163, 19245818, 36241112, 30867747, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 854236, 66011732, 58743269, 0, 59903120],
   [14255871, 19245818, 62118912, 4989947, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1097127, 42707583, 28498583, 59903120],
   [62322505, 19245818, 56498454, 10610405, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23714002, 0, 59903120],
   [0, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28498583, 59903120],
   [0, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28498583, 59903120],
   [0, 1671681, 65437178, 1671681, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9649696],
   [43839092, 3984693, 10804672, 44805306, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 22503486, 45366761, 64564504, 49943178, 65896211, 66733508, 15073384, 20246538, 63122433],
   [2876680, 16850819, 7822341, 37362141, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 49678027, 5510641, 63932532, 58335748, 51746746, 32300699, 60075709, 12063260, 59509947],
   [58473446, 0, 58473446, 8635413, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43394857, 0, 0]]

/-- N2c minor certificate 16: rows 0..26, cols 3..28 (det mod P = 50417316). -/
def n2cR16 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26]
def n2cC16 : List ℕ := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]
def n2cS16 : List (List ℕ) := [[11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534],
   [15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759],
   [15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759],
   [62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759],
   [11301318, 63031064, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534],
   [25282329, 15495622, 63031064, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210],
   [11301318, 63031064, 15495622, 63031064, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210],
   [11301318, 15495622, 63031064, 15495622, 63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [15068424, 43030449, 43030449, 61671799, 43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759],
   [11301318, 15495622, 15495622, 15495622, 63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [11301318, 15495622, 15495622, 15495622, 15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [11301318, 15495622, 15495622, 15495622, 15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534],
   [7758056, 35550333, 35550333, 35550333, 35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553],
   [15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759],
   [15068424, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759],
   [62603866, 43030449, 43030449, 43030449, 43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 56236711, 13351160, 36241625, 51784342, 40133282, 309759]]
def n2cT16 : List (List ℕ) := [[23592391, 25513055, 41574314, 50326313, 56221450, 18553362, 41574314, 47935600, 56221450, 11673170, 41574314, 55486457, 56221450, 42309307, 41574314, 55486457, 7142204, 49079246, 42309307, 63750604, 49271369, 64118130, 12066699, 53454417, 18471861, 24578884],
   [30163891, 11302839, 10962178, 62808539, 54153309, 47815170, 10962178, 10955993, 54153309, 20588850, 10962178, 16119420, 54153309, 48996067, 10962178, 16119420, 63767233, 57494935, 48996067, 44464538, 58393704, 42266402, 64592104, 78928, 43615299, 44291939],
   [50472813, 12546813, 33345480, 31366939, 61513797, 62286831, 33345480, 47971796, 61513797, 22975185, 33345480, 27296244, 61513797, 454174, 33345480, 27296244, 489762, 61024035, 454174, 19810413, 64176595, 54936154, 45790182, 25778248, 2109356, 2095287],
   [13135605, 23289704, 59429716, 49941495, 43079935, 47721255, 59429716, 54809035, 43079935, 57746370, 59429716, 25645444, 43079935, 9755348, 59429716, 25645444, 44750538, 65438256, 9755348, 29745294, 23471516, 64398732, 31709160, 22755844, 16233861, 19157346],
   [14877894, 5958075, 57935706, 49438472, 9173153, 23560516, 57935706, 43548343, 9173153, 10138749, 57935706, 9173153, 9173153, 57935706, 57935706, 9173153, 0, 9173153, 57935706, 0, 0, 0, 0, 20249900, 20871631, 19697875],
   [0, 10138749, 10138749, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373, 59920831],
   [0, 23560516, 10138749, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373, 0],
   [0, 10138749, 10138749, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 50198461, 0],
   [0, 10138749, 63825841, 43548343, 56970110, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 50198461, 59920831],
   [0, 17670387, 57935706, 22594932, 9173153, 23560516, 57935706, 43548343, 9173153, 10138749, 57935706, 9173153, 9173153, 57935706, 57935706, 9173153, 0, 9173153, 57935706, 0, 0, 0, 0, 0, 10892065, 61717838],
   [0, 23560516, 23560516, 43548343, 43548343, 53783641, 10138749, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373, 0],
   [0, 23560516, 23127561, 43115388, 43981298, 9621675, 23127561, 40168768, 43981298, 30836748, 23127561, 43981298, 43981298, 23127561, 23127561, 43981298, 0, 43981298, 23127561, 0, 0, 0, 0, 0, 36892373, 2766462],
   [0, 10138749, 63825841, 43548343, 3283018, 53783641, 63825841, 13325218, 56970110, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 50198461, 59920831],
   [0, 17670387, 57935706, 22594932, 9173153, 36982283, 57935706, 30126576, 9173153, 10138749, 57935706, 9173153, 9173153, 57935706, 57935706, 9173153, 0, 9173153, 57935706, 0, 0, 0, 0, 0, 10892065, 61717838],
   [0, 23560516, 23560516, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 10138749, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373, 0],
   [0, 17670387, 17670387, 49438472, 49438472, 23560516, 17670387, 43548343, 49438472, 10138749, 17670387, 49438472, 49438472, 17670387, 17670387, 49438472, 0, 49438472, 17670387, 0, 0, 0, 0, 0, 10892065, 0],
   [0, 10138749, 63825841, 43548343, 3283018, 53783641, 63825841, 13325218, 3283018, 13518332, 63825841, 56970110, 56970110, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 50198461, 59920831],
   [0, 10138749, 63825841, 43548343, 3283018, 53783641, 63825841, 13325218, 3283018, 13518332, 63825841, 56970110, 3283018, 63825841, 63825841, 3283018, 0, 3283018, 63825841, 0, 0, 0, 0, 0, 50198461, 59920831],
   [0, 23560516, 23560516, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 23560516, 56970110, 43548343, 10138749, 10138749, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 36892373, 0],
   [0, 23560516, 23560516, 43548343, 43548343, 53783641, 23560516, 13325218, 43548343, 13518332, 23560516, 56970110, 43548343, 10138749, 23560516, 43548343, 0, 43548343, 23560516, 0, 0, 0, 0, 0, 36892373, 0],
   [0, 10138749, 63825841, 43548343, 3283018, 53783641, 63825841, 13325218, 3283018, 13518332, 63825841, 56970110, 3283018, 10138749, 63825841, 56970110, 0, 56970110, 10138749, 0, 0, 0, 0, 0, 50198461, 59920831],
   [0, 10138749, 63825841, 43548343, 3283018, 53783641, 63825841, 13325218, 3283018, 13518332, 63825841, 56970110, 3283018, 10138749, 63825841, 56970110, 0, 3283018, 63825841, 0, 0, 0, 0, 0, 50198461, 59920831],
   [0, 21372512, 21372512, 45736347, 45736347, 6127063, 21372512, 60981796, 45736347, 33354453, 21372512, 58870234, 45736347, 8238625, 21372512, 58870234, 53974972, 58870234, 8238625, 0, 0, 0, 0, 0, 10772959, 0],
   [32637351, 31196853, 2373694, 46141339, 58497201, 19639408, 2373694, 31157159, 58497201, 24799552, 2373694, 42271231, 58497201, 18599664, 2373694, 42271231, 21486887, 37010314, 18599664, 19295906, 46932547, 52574691, 41281620, 43795261, 2923319, 48674696],
   [44630934, 8069394, 53716343, 22866657, 45688734, 12572748, 53716343, 62315855, 45688734, 54825587, 53716343, 41508672, 45688734, 57896405, 53716343, 41508672, 58400657, 54396936, 57896405, 17759178, 2774329, 16737460, 8274298, 18515571, 39402790, 3482869],
   [38809198, 11712312, 26843540, 42949640, 40265319, 32212292, 26843540, 34896567, 40265319, 13421767, 26843540, 40265319, 40265319, 26843540, 26843540, 40265319, 0, 40265319, 26843540, 0, 0, 0, 0, 46858959, 57129293, 65133214]]

/-- N2c minor certificate 17: rows 0..33, cols 10..35 (det mod P = 43513890). -/
def n2cR17 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 33]
def n2cC17 : List ℕ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
def n2cS17 : List (List ℕ) := [[11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704],
   [25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704],
   [11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704],
   [62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155],
   [11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678],
   [15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366],
   [11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704],
   [7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366],
   [15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366],
   [25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 33196128, 1167113, 10522293, 55434195, 21479374, 42998704]]
def n2cT17 : List (List ℕ) := [[51300847, 33374494, 46469330, 562575, 29389337, 30124330, 1297568, 562575, 29389337, 7142204, 22982126, 1297568, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 37578742, 36789345, 394300],
   [66707087, 6469248, 31174196, 52455617, 41734840, 12659870, 23380647, 52455617, 41734840, 63767233, 16001496, 23380647, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 13938358, 43726654, 59953946],
   [63054567, 33670403, 8565360, 39315326, 21326398, 55543951, 6424020, 39315326, 21326398, 489762, 55054189, 6424020, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 8980788, 32808299, 50434519],
   [31223786, 31327397, 28195655, 20489465, 64585695, 14911327, 37923956, 20489465, 64585695, 44750538, 37269648, 37923956, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 16351491, 43290380, 269105],
   [8099411, 35957237, 47393495, 52322336, 14786523, 14786523, 52322336, 52322336, 14786523, 0, 14786523, 52322336, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 25021055, 10576207, 31622765],
   [50549284, 61619301, 62393797, 30018133, 37090726, 37090726, 30018133, 30018133, 37090726, 0, 37090726, 30018133, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 53713741, 6135164, 58841513],
   [16559575, 56462622, 8967950, 40280392, 26828467, 26828467, 40280392, 40280392, 26828467, 0, 26828467, 40280392, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 13395118, 41723876, 36559894],
   [50549284, 61619301, 62393797, 30018133, 37090726, 37090726, 30018133, 30018133, 37090726, 0, 37090726, 30018133, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 53713741, 6135164, 58841513],
   [16559575, 56462622, 8967950, 40280392, 26828467, 26828467, 40280392, 40280392, 26828467, 0, 26828467, 40280392, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 13395118, 41723876, 36559894],
   [42236659, 37872109, 65018680, 48764010, 18344849, 18344849, 48764010, 48764010, 18344849, 0, 18344849, 48764010, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 9653817, 57660387, 65155098],
   [52866236, 14099174, 63784722, 14284112, 52824747, 52824747, 14284112, 14284112, 52824747, 0, 52824747, 14284112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 12973439, 61113417, 34442716],
   [18312532, 11602654, 19169605, 64708848, 2400011, 2400011, 64708848, 64708848, 2400011, 0, 2400011, 64708848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17163445, 40323825, 27499583],
   [0, 60924153, 37582500, 28186875, 38921984, 38921984, 28186875, 28186875, 38921984, 0, 38921984, 28186875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56655995, 22661216],
   [0, 9049253, 22355029, 67097916, 10943, 10943, 67097916, 67097916, 10943, 0, 10943, 67097916, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 30360665, 13612311],
   [0, 43736003, 33779247, 42111650, 24997209, 24997209, 42111650, 42111650, 24997209, 0, 24997209, 42111650, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58311904, 5631332],
   [0, 49579217, 42111650, 24872848, 42236011, 42236011, 24872848, 24872848, 42236011, 0, 42236011, 24872848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43733928, 4223499],
   [0, 7237061, 37582500, 14765108, 38921984, 38921984, 28186875, 28186875, 38921984, 0, 38921984, 28186875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56655995, 22661216],
   [0, 7237061, 37582500, 14765108, 38921984, 52343751, 14765108, 14765108, 52343751, 0, 52343751, 14765108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56655995, 22661216],
   [0, 43736003, 33779247, 55533417, 24997209, 11575442, 42111650, 42111650, 24997209, 0, 24997209, 42111650, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58311904, 5631332],
   [0, 43736003, 33779247, 55533417, 24997209, 11575442, 42111650, 55533417, 11575442, 0, 11575442, 55533417, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58311904, 5631332],
   [0, 7237061, 37582500, 14765108, 38921984, 52343751, 28186875, 14765108, 38921984, 0, 38921984, 28186875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56655995, 22661216],
   [0, 7237061, 37582500, 14765108, 38921984, 52343751, 28186875, 14765108, 38921984, 0, 52343751, 14765108, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56655995, 22661216],
   [0, 26544195, 61882580, 59545822, 20696924, 7563037, 46411935, 59545822, 20696924, 53974972, 20696924, 46411935, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3676378, 52989544],
   [11856009, 8523559, 65811291, 49909713, 61844071, 10961182, 66135683, 49909713, 61844071, 21486887, 56583154, 66135683, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 5370373, 56294065, 66813134],
   [30352618, 13672742, 27280144, 16280046, 11836110, 16016172, 20460108, 16280046, 11836110, 58400657, 24724374, 20460108, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 3695075, 30624636, 56975460],
   [31477911, 17017146, 29820169, 5587912, 61520947, 61520947, 5587912, 5587912, 61520947, 0, 61520947, 5587912, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49945414, 44904125, 48449339]]

/-- N2c minor certificate 18: rows 0..30, cols 7..32 (det mod P = 18235905). -/
def n2cR18 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 30]
def n2cC18 : List ℕ := [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
def n2cS18 : List (List ℕ) := [[15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644],
   [43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644],
   [43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733],
   [63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733],
   [43030449, 62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644],
   [63031064, 11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536],
   [15495622, 25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536],
   [15495622, 11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [43030449, 15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644],
   [15495622, 11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [43030449, 15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [15495622, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733],
   [35550333, 7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818],
   [43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644],
   [43030449, 15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644],
   [63031064, 11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 32122605, 40895904, 63518117, 33196128, 2661626, 14507733]]
def n2cT18 : List (List ℕ) := [[13445451, 46752834, 10507835, 27636488, 20179070, 37360057, 10507835, 19444077, 20179070, 11242828, 10507835, 19444077, 7142204, 13036866, 11242828, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 58549423, 24420666, 51212678],
   [19595298, 48599794, 26679534, 21643614, 38435953, 19175705, 26679534, 402064, 38435953, 64713423, 26679534, 402064, 63767233, 41777579, 64713423, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 64521505, 36443755, 21859046],
   [53093710, 58123772, 37294975, 61677848, 57564302, 50610798, 37294975, 23346749, 57564302, 4403669, 37294975, 23346749, 489762, 57074540, 4403669, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 57559592, 31649188, 25785474],
   [62832903, 42433493, 11716389, 55333858, 23684403, 38867840, 11716389, 6249912, 23684403, 29150880, 11716389, 6249912, 44750538, 46042724, 29150880, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 40061603, 44495705, 30358867],
   [58926089, 6427663, 42689476, 2262186, 24419383, 12180062, 42689476, 24419383, 24419383, 42689476, 42689476, 24419383, 0, 24419383, 42689476, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 43405022, 58214107, 64160050],
   [51223891, 2974199, 61729825, 1854719, 5379034, 37567194, 61729825, 5379034, 5379034, 61729825, 61729825, 5379034, 0, 5379034, 61729825, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 43332066, 3987470, 19433913],
   [33918154, 16129309, 19362828, 16568740, 47746031, 25817104, 19362828, 47746031, 47746031, 19362828, 19362828, 47746031, 0, 47746031, 19362828, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 25685920, 14766764, 28772527],
   [50286716, 8185933, 4701343, 4097392, 62407516, 28638077, 4701343, 62407516, 62407516, 4701343, 4701343, 62407516, 0, 62407516, 4701343, 0, 0, 0, 0, 0, 0, 0, 38970459, 63703974, 6117658, 64483956],
   [58148812, 21742159, 50548156, 44143064, 16560703, 22658302, 50548156, 16560703, 16560703, 50548156, 50548156, 16560703, 0, 16560703, 50548156, 0, 0, 0, 0, 0, 0, 0, 0, 40787155, 18821168, 58059944],
   [0, 9702758, 38288706, 28321320, 28820153, 51051608, 38288706, 28820153, 28820153, 38288706, 38288706, 28820153, 0, 28820153, 38288706, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57764531, 57982630],
   [0, 61214295, 21966827, 21409668, 45142032, 6919483, 21966827, 45142032, 45142032, 21966827, 21966827, 45142032, 0, 45142032, 21966827, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16660763, 44172002],
   [0, 39605118, 62687936, 36276159, 4420923, 61214295, 62687936, 4420923, 4420923, 62687936, 62687936, 4420923, 0, 4420923, 62687936, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5125150, 31167579],
   [0, 39605118, 49266169, 36276159, 4420923, 61214295, 62687936, 4420923, 4420923, 62687936, 62687936, 4420923, 0, 4420923, 62687936, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5125150, 42587597],
   [0, 23124525, 38288706, 14899553, 28820153, 51051608, 38288706, 28820153, 28820153, 38288706, 38288706, 28820153, 0, 28820153, 38288706, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57764531, 57982630],
   [0, 61214295, 35388594, 21409668, 31720265, 6919483, 21966827, 45142032, 45142032, 21966827, 21966827, 45142032, 0, 45142032, 21966827, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16660763, 44172002],
   [0, 62687936, 60095875, 16057251, 7012984, 21966827, 60095875, 7012984, 7012984, 60095875, 60095875, 7012984, 0, 7012984, 60095875, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29272787, 66683431],
   [0, 39605118, 49266169, 36276159, 17842690, 61214295, 49266169, 4420923, 4420923, 62687936, 62687936, 4420923, 0, 4420923, 62687936, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5125150, 42587597],
   [0, 39605118, 49266169, 36276159, 17842690, 61214295, 49266169, 4420923, 17842690, 49266169, 49266169, 17842690, 0, 17842690, 49266169, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5125150, 42587597],
   [0, 61214295, 35388594, 21409668, 31720265, 6919483, 35388594, 45142032, 31720265, 21966827, 21966827, 45142032, 0, 45142032, 21966827, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16660763, 44172002],
   [0, 61214295, 35388594, 21409668, 31720265, 6919483, 35388594, 45142032, 31720265, 21966827, 35388594, 31720265, 0, 31720265, 35388594, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16660763, 44172002],
   [0, 39605118, 49266169, 36276159, 17842690, 61214295, 49266169, 4420923, 17842690, 62687936, 49266169, 4420923, 0, 4420923, 62687936, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5125150, 42587597],
   [0, 39605118, 49266169, 36276159, 17842690, 61214295, 49266169, 4420923, 17842690, 62687936, 49266169, 4420923, 0, 17842690, 49266169, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5125150, 42587597],
   [0, 64207607, 14430151, 5339862, 52678708, 1728352, 14430151, 65812595, 52678708, 1296264, 14430151, 65812595, 53974972, 65812595, 1296264, 0, 0, 0, 0, 0, 0, 0, 0, 0, 62120037, 3565209],
   [40247556, 65598663, 42450768, 46381493, 18420127, 55866031, 42450768, 2194157, 18420127, 58676738, 42450768, 2194157, 21486887, 64042099, 58676738, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 6419577, 15238930, 62253780],
   [54489874, 31147642, 64884637, 4967008, 34520440, 47347026, 64884637, 30340378, 34520440, 1955840, 64884637, 30340378, 58400657, 43228642, 1955840, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 63362694, 34407300, 28505527],
   [62647139, 17862959, 12139780, 59241954, 54969079, 38555993, 12139780, 54969079, 54969079, 12139780, 12139780, 54969079, 0, 54969079, 12139780, 0, 0, 0, 0, 0, 0, 0, 0, 26321704, 53412841, 51636512]]

/-- N2c minor certificate 19: rows 0..37, cols 14..43 (det mod P = 11386426). -/
def n2cR19 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 37]
def n2cC19 : List ℕ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 43]
def n2cS19 : List (List ℕ) := [[15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 20769422],
   [61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 5322943],
   [15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 20769422],
   [63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 20769422],
   [15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 20769422],
   [15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 26510245],
   [35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 57322967],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 5322943],
   [61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 20343947, 35141361, 55898772, 32397634, 8685970, 5322943]]
def n2cT19 : List (List ℕ) := [[40330940, 58341177, 61597704, 39454587, 36198060, 45220463, 13120714, 11158980, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 37104211, 28989464, 55199463, 60490061, 54156177],
   [61513865, 18886195, 35744936, 46229292, 29370551, 31491633, 54503421, 51987581, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 19067038, 35349376, 3782912, 8135853, 40195332],
   [5489442, 64563936, 15259028, 30295341, 12491390, 22892851, 41671085, 19807124, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 16728599, 16357722, 6992589, 39562586, 30609141],
   [36891380, 24366245, 34632257, 11034547, 768535, 40325727, 51149377, 24044227, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 5338853, 2382351, 62647879, 55240555, 58391927],
   [36034228, 177793, 55079282, 66931066, 12029577, 35766230, 31520422, 35588437, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 49077952, 63029543, 54408835],
   [4723565, 59813297, 62385294, 7295562, 4723565, 420965, 59392332, 7716527, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 9771346, 0, 36677205],
   [62385294, 20717329, 18145332, 46391530, 48963527, 38070671, 49755517, 17353342, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 57337513, 26458105, 16020176],
   [4723565, 59813297, 62385294, 7295562, 4723565, 420965, 59392332, 7716527, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 9771346, 0, 36677205],
   [62385294, 20717329, 18145332, 46391530, 48963527, 38070671, 49755517, 17353342, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 57337513, 26458105, 16020176],
   [3743407, 40454093, 63365452, 26654766, 3743407, 41908851, 65654101, 1454758, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 51236637, 44606334, 0, 42317075],
   [602109, 47090960, 12819658, 20017899, 54289201, 38594169, 8496791, 58612068, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 36327464, 45646946, 26458105, 26408395],
   [66506750, 33439666, 602109, 33669193, 66506750, 67006326, 33542199, 33566660, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 30781395, 21461913, 0, 26288986],
   [602109, 47090960, 12819658, 20017899, 54289201, 38594169, 8496791, 58612068, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 36327464, 45646946, 26458105, 26408395],
   [60421217, 25711132, 6687642, 41397727, 60421217, 63323364, 29496627, 37612232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 33296619, 50959873, 0, 3882135],
   [28450711, 28450711, 52079915, 38658148, 15028944, 19245818, 9204893, 57903966, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32721354, 22496371, 26458105, 59903120],
   [41686469, 65845688, 25422390, 1263171, 41686469, 41737190, 24108498, 43000361, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44285172, 0, 31253810],
   [0, 0, 13421767, 0, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 59903120],
   [0, 13421767, 0, 53687092, 0, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 59903120],
   [0, 0, 0, 53687092, 0, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59903120],
   [0, 0, 0, 0, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59903120],
   [0, 13421767, 13421767, 53687092, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 59903120],
   [0, 13421767, 13421767, 53687092, 53687092, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 59903120],
   [0, 0, 0, 0, 0, 1671681, 65437178, 1671681, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9649696],
   [36860654, 40130191, 20910581, 20740704, 39960314, 43259837, 63979213, 58739624, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 22503486, 45366761, 8932047, 38518528, 43268941],
   [34442644, 54420971, 53496131, 44984106, 45908946, 65966101, 55563729, 56729612, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 49678027, 5510641, 16983352, 65540482, 32196548],
   [65687709, 1263171, 1421150, 65845688, 65687709, 6251603, 62120427, 4988432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22823687, 0, 13673530]]

/-- N2c minor certificate 20: rows 0..34, cols 11..36 (det mod P = 29226664). -/
def n2cR20 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 34]
def n2cC20 : List ℕ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
def n2cS20 : List (List ℕ) := [[15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991],
   [63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991],
   [43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129],
   [63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340],
   [43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684],
   [15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991],
   [35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129],
   [43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129],
   [63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 3510172, 10522293, 15480703, 50540108, 42998704, 51191991]]
def n2cT20 : List (List ℕ) := [[8009516, 54940924, 63298801, 33761970, 34496963, 64033794, 63298801, 33761970, 7142204, 27354759, 64033794, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 42070438, 27989110, 46926612],
   [39541321, 66247702, 27606941, 66583516, 37508546, 65640830, 27606941, 66583516, 63767233, 40850172, 65640830, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 6997911, 64038460, 19918357],
   [11414373, 54100992, 35971035, 24670689, 58888242, 3079729, 35971035, 24670689, 489762, 58398480, 3079729, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 26002410, 5812437, 43738813],
   [53447420, 65123267, 16692808, 1273493, 18707984, 34127299, 16692808, 1273493, 44750538, 41066305, 34127299, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 66264696, 28677112, 5535603],
   [64959998, 17905499, 14769606, 52339253, 52339253, 14769606, 14769606, 52339253, 0, 52339253, 14769606, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 33203445, 6167572, 38783380],
   [55459383, 48605591, 32417335, 34691524, 34691524, 32417335, 32417335, 34691524, 0, 34691524, 32417335, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 57993217, 53302994, 4395438],
   [11649476, 45705067, 258093, 66850766, 66850766, 258093, 258093, 66850766, 0, 66850766, 258093, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 9115642, 15004677, 25390546],
   [55459383, 48605591, 32417335, 34691524, 34691524, 32417335, 32417335, 34691524, 0, 34691524, 32417335, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 57993217, 53302994, 4395438],
   [11649476, 45705067, 258093, 66850766, 66850766, 258093, 258093, 66850766, 0, 66850766, 258093, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 9115642, 15004677, 25390546],
   [43855675, 21943749, 34841430, 32267429, 32267429, 34841430, 34841430, 32267429, 0, 32267429, 34841430, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 32328171, 37012132, 18449723],
   [12007703, 64625702, 16809647, 50299212, 50299212, 16809647, 16809647, 50299212, 0, 50299212, 16809647, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 8765512, 30475356, 18453008],
   [15882477, 726645, 46721183, 20387676, 20387676, 46721183, 46721183, 20387676, 0, 20387676, 46721183, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 39691558, 48863241, 49358092],
   [6792747, 2519957, 4427068, 62681791, 62681791, 4427068, 4427068, 62681791, 0, 62681791, 4427068, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 56273451, 44926509, 31167357],
   [0, 39725906, 8713047, 58395812, 58395812, 8713047, 8713047, 58395812, 0, 58395812, 8713047, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42758647, 65963657],
   [0, 28077376, 403307, 66705552, 66705552, 403307, 403307, 66705552, 0, 66705552, 403307, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55749360, 9581964],
   [0, 21058032, 43923235, 23185624, 23185624, 43923235, 43923235, 23185624, 0, 23185624, 43923235, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41812020, 7186473],
   [0, 66233282, 18850354, 34836738, 34836738, 32272121, 32272121, 34836738, 0, 34836738, 32272121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12558311, 20204020],
   [0, 66233282, 18850354, 34836738, 48258505, 18850354, 18850354, 48258505, 0, 48258505, 18850354, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12558311, 20204020],
   [0, 28077376, 13825074, 66705552, 53283785, 403307, 403307, 66705552, 0, 66705552, 403307, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55749360, 9581964],
   [0, 28077376, 13825074, 66705552, 53283785, 403307, 13825074, 53283785, 0, 53283785, 13825074, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55749360, 9581964],
   [0, 66233282, 18850354, 34836738, 48258505, 32272121, 18850354, 34836738, 0, 34836738, 32272121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12558311, 20204020],
   [0, 66233282, 18850354, 34836738, 48258505, 32272121, 18850354, 34836738, 0, 48258505, 18850354, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12558311, 20204020],
   [0, 6104089, 42685279, 37557467, 24423580, 29551392, 42685279, 37557467, 53974972, 37557467, 29551392, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58933403, 34713247],
   [61101722, 25903166, 36411973, 8232952, 24458922, 52637943, 36411973, 8232952, 21486887, 2972035, 52637943, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 2001601, 12562597, 31913900],
   [20696240, 64667286, 46173130, 49051885, 53231947, 50353192, 46173130, 49051885, 58400657, 61940149, 50353192, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 18713834, 40926363, 50376512],
   [46894345, 63713325, 27845053, 39263806, 39263806, 27845053, 27845053, 39263806, 0, 39263806, 27845053, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10835408, 34740661, 56145522]]

/-- N2c minor certificate 21: rows 0..31, cols 8..33 (det mod P = 10638598). -/
def n2cR21 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 31]
def n2cC21 : List ℕ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33]
def n2cS21 : List (List ℕ) := [[11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162],
   [15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162],
   [15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301],
   [62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162],
   [11301318, 63031064, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301],
   [25282329, 15495622, 25282329, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597],
   [11301318, 63031064, 11301318, 63031064, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597],
   [15068424, 43030449, 62603866, 43030449, 33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162],
   [11301318, 15495622, 11301318, 63031064, 11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [15068424, 43030449, 15068424, 43030449, 62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162],
   [11301318, 15495622, 11301318, 15495622, 11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [11301318, 15495622, 11301318, 15495622, 11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301],
   [7758056, 35550333, 7758056, 35550333, 7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520],
   [15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162],
   [15068424, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162],
   [62603866, 43030449, 15068424, 43030449, 15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 28109120, 62321203, 27281786, 20008787, 19343644, 11273162]]
def n2cT21 : List (List ℕ) := [[10634944, 2284605, 3107664, 29981274, 1920832, 705631, 29246281, 29981274, 1440624, 705631, 29246281, 7142204, 22839070, 1440624, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 47059607, 49244473, 24324704],
   [45079904, 22042952, 57238114, 30335809, 29975897, 34779678, 59410779, 30335809, 5704708, 34779678, 59410779, 63767233, 33677435, 5704708, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 67106504, 12464217, 63635940],
   [20231946, 40838742, 17637748, 18805038, 12811338, 8945380, 51696344, 18805038, 43162933, 8945380, 51696344, 489762, 18315276, 43162933, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 19864306, 9539056, 31552772],
   [51435949, 41747421, 18709553, 43378487, 34978681, 59131164, 25943996, 43378487, 9456796, 59131164, 25943996, 44750538, 65736808, 9456796, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 25185852, 28296996, 62281528],
   [42800720, 14936261, 25255103, 9750421, 31738678, 57358438, 9750421, 9750421, 57358438, 57358438, 9750421, 0, 9750421, 57358438, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 54061884, 17559203, 478560],
   [48778534, 19407604, 45907207, 34936766, 42896124, 32172093, 34936766, 34936766, 32172093, 32172093, 34936766, 0, 34936766, 32172093, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 48954943, 26710713, 42392846],
   [18330325, 14291661, 36147537, 6326794, 36303514, 60782065, 6326794, 6326794, 60782065, 60782065, 6326794, 0, 6326794, 60782065, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 18153916, 66687101, 7077036],
   [48747609, 31748266, 29192436, 46600736, 27344164, 20508123, 46600736, 46600736, 20508123, 20508123, 46600736, 0, 46600736, 20508123, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 43203722, 20828546, 56210173],
   [4071658, 11738013, 41027372, 20631780, 39599819, 46477079, 20631780, 20631780, 46477079, 46477079, 20631780, 0, 20631780, 46477079, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 43558680, 40988898, 30082397],
   [53332030, 22556096, 30770529, 15473835, 46477079, 51635024, 15473835, 15473835, 51635024, 51635024, 15473835, 0, 15473835, 51635024, 0, 0, 0, 0, 0, 0, 0, 0, 0, 58589734, 39306687, 5643304],
   [0, 10138749, 41027372, 20631780, 39599819, 46477079, 20631780, 20631780, 46477079, 46477079, 20631780, 0, 20631780, 46477079, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40988898, 37672691],
   [0, 23560516, 41027372, 20631780, 39599819, 46477079, 20631780, 20631780, 46477079, 46477079, 20631780, 0, 20631780, 46477079, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40988898, 11797191],
   [0, 10138749, 41027372, 20631780, 39599819, 46477079, 20631780, 20631780, 46477079, 46477079, 20631780, 0, 20631780, 46477079, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52408916, 11797191],
   [0, 17670387, 40909278, 6300682, 36338330, 60808177, 6300682, 6300682, 60808177, 60808177, 6300682, 0, 6300682, 60808177, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64296103, 21442980],
   [0, 23560516, 41027372, 7210013, 39599819, 46477079, 20631780, 20631780, 46477079, 46477079, 20631780, 0, 20631780, 46477079, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40988898, 37672691],
   [0, 17670387, 30770529, 55739154, 46477079, 11369705, 55739154, 55739154, 11369705, 11369705, 55739154, 0, 55739154, 11369705, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64296103, 45031733],
   [0, 10138749, 41027372, 34053547, 39599819, 33055312, 20631780, 20631780, 46477079, 46477079, 20631780, 0, 20631780, 46477079, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52408916, 11797191],
   [0, 10138749, 41027372, 34053547, 39599819, 33055312, 20631780, 34053547, 33055312, 33055312, 34053547, 0, 34053547, 33055312, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52408916, 11797191],
   [0, 23560516, 41027372, 7210013, 39599819, 59898846, 20631780, 7210013, 46477079, 46477079, 20631780, 0, 20631780, 46477079, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40988898, 37672691],
   [0, 23560516, 41027372, 7210013, 39599819, 59898846, 20631780, 7210013, 46477079, 59898846, 7210013, 0, 7210013, 59898846, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40988898, 37672691],
   [0, 10138749, 41027372, 34053547, 39599819, 33055312, 20631780, 34053547, 46477079, 33055312, 20631780, 0, 20631780, 46477079, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52408916, 11797191],
   [0, 10138749, 41027372, 34053547, 39599819, 33055312, 20631780, 34053547, 46477079, 33055312, 20631780, 0, 34053547, 33055312, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52408916, 11797191],
   [0, 21372512, 44238978, 45361151, 56224334, 21747708, 58495038, 45361151, 8613821, 21747708, 58495038, 53974972, 58495038, 8613821, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18423560, 36250604],
   [59132651, 15063761, 64778111, 11068474, 65668235, 49802421, 61951363, 11068474, 66028391, 49802421, 61951363, 21486887, 56690446, 66028391, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 15036939, 46952719, 48865331],
   [10078136, 66099032, 53637050, 28751810, 32668913, 3544408, 24571748, 28751810, 7724470, 3544408, 24571748, 58400657, 37460012, 7724470, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 20367285, 65637386, 43692242],
   [355062, 62223150, 23560516, 57935706, 56970110, 9173153, 57935706, 57935706, 9173153, 9173153, 57935706, 0, 57935706, 9173153, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8519125, 24989416, 15799676]]

/-- N2c minor certificate 22: rows 0..35, cols 12..37 (det mod P = 65470632). -/
def n2cR22 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 35]
def n2cC22 : List ℕ := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37]
def n2cS22 : List (List ℕ) := [[11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199],
   [15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199],
   [15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114],
   [33709772, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199],
   [11301318, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114],
   [62603866, 43030449, 61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547],
   [11301318, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397],
   [11301318, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [11301318, 15495622, 15495622, 15495622, 15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114],
   [7758056, 35550333, 35550333, 35550333, 35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536],
   [15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199],
   [15068424, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199],
   [25282329, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 47864976, 15480703, 41832548, 67073729, 51191991, 47168114]]
def n2cT22 : List (List ℕ) := [[63250915, 6364601, 48826693, 49561686, 48969071, 48234078, 48826693, 7142204, 42419482, 48969071, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 38789817, 32299229, 41167029],
   [23224702, 65455426, 39510112, 10435142, 25605375, 54680345, 39510112, 63767233, 13776768, 25605375, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 325718, 42632783, 27548430],
   [65203898, 32234478, 51043632, 18152326, 43815645, 9598092, 51043632, 489762, 17662564, 43815645, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 38097529, 47419736, 33768971],
   [1434960, 22089262, 65092348, 15417980, 37417303, 19982812, 65092348, 44750538, 37776301, 37417303, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 45145202, 9071927, 32353541],
   [48757156, 62932364, 13860804, 13860804, 53248055, 53248055, 13860804, 0, 13860804, 53248055, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 64601718, 41629153, 64852187],
   [50573729, 35408947, 65633403, 65633403, 1475456, 1475456, 65633403, 0, 65633403, 1475456, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 16736438, 284136, 19521737],
   [16535130, 18278145, 29921022, 29921022, 37187837, 37187837, 29921022, 0, 29921022, 37187837, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 50372421, 34103369, 28661532],
   [50573729, 35408947, 65633403, 65633403, 1475456, 1475456, 65633403, 0, 65633403, 1475456, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 16736438, 284136, 19521737],
   [16535130, 18278145, 29921022, 29921022, 37187837, 37187837, 29921022, 0, 29921022, 37187837, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 50372421, 34103369, 28661532],
   [26053777, 12949616, 35524519, 35524519, 31584340, 31584340, 35524519, 0, 35524519, 31584340, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 57164612, 21820364, 27265531],
   [14917678, 55149891, 2579041, 2579041, 64529818, 64529818, 2579041, 0, 2579041, 64529818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 50509585, 21095677, 24200219],
   [42291347, 46494400, 43344826, 43344826, 23764033, 23764033, 43344826, 0, 43344826, 23764033, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 44566905, 48055759, 37413285],
   [51210147, 44884932, 57632468, 57632468, 9476391, 9476391, 57632468, 0, 57632468, 9476391, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 30492039, 0, 65604763],
   [12034598, 19337895, 28512645, 28512645, 38596214, 38596214, 28512645, 0, 28512645, 38596214, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 49950847, 55232905, 11158274],
   [0, 53687092, 62002568, 62002568, 5106291, 5106291, 62002568, 0, 62002568, 5106291, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820],
   [0, 0, 19658386, 19658386, 47450473, 47450473, 19658386, 0, 19658386, 47450473, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26504865],
   [0, 53687092, 33551857, 33551857, 33557002, 33557002, 33551857, 0, 33551857, 33557002, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34387505, 12843449],
   [0, 53687092, 33551857, 46973624, 20135235, 20135235, 46973624, 0, 46973624, 20135235, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34387505, 12843449],
   [0, 0, 62002568, 48580801, 5106291, 5106291, 62002568, 0, 62002568, 5106291, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820],
   [0, 0, 62002568, 48580801, 5106291, 18528058, 48580801, 0, 48580801, 18528058, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35339820],
   [0, 53687092, 33551857, 46973624, 33557002, 20135235, 33551857, 0, 33551857, 33557002, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34387505, 12843449],
   [0, 53687092, 33551857, 46973624, 33557002, 20135235, 33551857, 0, 46973624, 20135235, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34387505, 12843449],
   [0, 0, 29923460, 16789573, 37185399, 50319286, 29923460, 53974972, 29923460, 37185399, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41950523],
   [2893458, 12003764, 47266054, 63492024, 13604841, 64487730, 47266054, 21486887, 42005137, 13604841, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 54793711, 59661652, 53010802],
   [7687122, 4071461, 7291779, 11471841, 25004439, 20824377, 7291779, 58400657, 20180043, 25004439, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 19337334, 62316538, 31849614],
   [56113932, 27903232, 47719461, 47719461, 19389398, 19389398, 47719461, 0, 47719461, 19389398, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45246969, 5482871, 42631753]]

/-- N2c minor certificate 23: rows 0..39, cols 16..43 (det mod P = 50143513). -/
def n2cR23 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 39]
def n2cC23 : List ℕ := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 43]
def n2cS23 : List (List ℕ) := [[15495622, 15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 20769422],
   [63031064, 15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 20769422],
   [15495622, 63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 20769422],
   [63031064, 15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 20769422],
   [15495622, 63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 20769422],
   [15495622, 15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 26510245],
   [35550333, 35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 57322967],
   [43030449, 43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 5322943],
   [61671799, 43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 11975041, 62012112, 49464710, 39599045, 31157861, 5322943]]
def n2cT23 : List (List ℕ) := [[53252300, 49119420, 50549734, 8108843, 40567501, 50821052, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 37104211, 28989464, 25762093, 517955, 47108047, 20833634, 50054474],
   [44615719, 12472405, 7335734, 33583069, 19060013, 20322130, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 19067038, 35349376, 66050977, 33199726, 4422761, 2543907, 30200503],
   [54055085, 61057033, 46835092, 30923403, 2878841, 58599368, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 16728599, 16357722, 16380240, 27992600, 6193880, 45122086, 14156786],
   [28378159, 59364173, 48812507, 60772595, 49481742, 25711862, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 5338853, 2382351, 60754229, 41771391, 58405839, 22415525, 11419439],
   [52829777, 28825126, 44874133, 59338455, 46054137, 21054722, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 14557495, 45685953, 10747846, 33599353, 43891075],
   [66823876, 66823876, 21641917, 55215592, 12178250, 54930609, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 66082157, 820746, 2735956],
   [284983, 53972075, 32045175, 50384903, 29860740, 37248119, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 1026702, 65190986, 49961425],
   [66823876, 66823876, 21641917, 55215592, 12178250, 54930609, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 66082157, 820746, 2735956],
   [284983, 53972075, 32045175, 50384903, 29860740, 37248119, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 1026702, 65190986, 49961425],
   [60081419, 60081419, 21084540, 64794872, 9341427, 57767432, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 51236637, 401314, 43576062, 2989424, 66515694, 24355651],
   [58867108, 45445341, 53038559, 52335024, 36437353, 30671506, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 36327464, 7848008, 50384271, 66445740, 11751380, 1581711],
   [8241751, 8241751, 648533, 53265471, 5601637, 61507222, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 30781395, 59260851, 16724588, 663119, 54260352, 51115670],
   [58867108, 45445341, 53038559, 52335024, 36437353, 30671506, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 36327464, 7848008, 50384271, 66445740, 11751380, 1581711],
   [20699719, 20699719, 32323076, 12905848, 33503292, 33605567, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 33296619, 6989205, 35357300, 10719714, 10617726, 3288229],
   [3722472, 57409564, 27408063, 6327037, 3372258, 63736601, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32721354, 15413076, 2729723, 58273344, 12029892, 44140802],
   [49856457, 49856457, 18950409, 36846363, 47514898, 19593961, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55213590, 15023587, 3175077, 22198407, 30609244],
   [27135628, 13713861, 39973231, 19245818, 34149180, 32959679, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 49837459, 0, 59903120],
   [36422436, 36422436, 17264656, 19245818, 11440605, 55668254, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29261417, 66011732, 59903120],
   [0, 53687092, 0, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59903120],
   [0, 0, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59903120],
   [0, 53687092, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66011732, 59903120],
   [0, 53687092, 53687092, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66011732, 59903120],
   [0, 0, 0, 1671681, 65437178, 1671681, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9649696],
   [27169634, 30269294, 62750988, 3984693, 26616908, 28993070, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 22503486, 45366761, 64564504, 49943178, 15000609, 17929204, 63122433],
   [46063168, 57529470, 31545429, 16850819, 25024788, 20159694, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 49678027, 5510641, 63932532, 58335748, 41969178, 20199617, 59509947],
   [12948492, 12948492, 54160367, 0, 54160367, 12948492, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61940011, 0, 0]]

/-- N2c minor certificate 24: rows 0..40, cols 17..43 (det mod P = 27553203). -/
def n2cR24 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 40]
def n2cC24 : List ℕ := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43]
def n2cS24 : List (List ℕ) := [[15495622, 15495622, 15495622, 63031064, 63031064, 34793008, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 34793008, 55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 54165319, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 54165319, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 54165319, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 54165319, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 54165319, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57401204, 20769422],
   [43030449, 43030449, 43030449, 43030449, 43030449, 48880801, 42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 54165319, 5322943],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57401204, 20769422],
   [15495622, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57401204, 20769422],
   [63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57401204, 20769422],
   [15495622, 63031064, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 57401204, 20769422],
   [63031064, 15495622, 63031064, 63031064, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 10804460, 20769422],
   [15495622, 63031064, 15495622, 15495622, 63031064, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 10804460, 26510245],
   [35550333, 35550333, 26163315, 26163315, 26163315, 18518343, 33194879, 29415250, 59176471, 38763925, 40814016, 51165553, 23891385, 38064570, 23072261, 51252818, 14216520, 44793316, 66431806, 25814596, 20197536, 36335696, 32394171, 28293413, 44527543, 57322967],
   [43030449, 43030449, 43030449, 61671799, 61671799, 64886753, 42057346, 32256487, 36241625, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 54165319, 5322943],
   [43030449, 43030449, 43030449, 43030449, 43030449, 52754345, 59942233, 32256487, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 54165319, 5322943],
   [63031064, 15495622, 15495622, 15495622, 15495622, 19883386, 65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 57852655, 3544103, 14815804, 54139551, 57401204, 20769422]]
def n2cT24 : List (List ℕ) := [[58741674, 32458870, 8108843, 26710942, 64677611, 63750604, 49271369, 64118130, 12066699, 34924689, 13246821, 25243689, 15832119, 35128922, 23672091, 6567215, 22527845, 33192288, 37104211, 28989464, 25762093, 517955, 1616864, 45966701, 59772989, 50054474],
   [49454250, 66440158, 33583069, 63675732, 42815270, 44464538, 58393704, 42266402, 64592104, 28164808, 39812970, 51388957, 5585088, 31060899, 34791709, 17962861, 62257431, 20280375, 19067038, 35349376, 66050977, 33199726, 15088108, 59548133, 55951803, 30200503],
   [28528980, 55308350, 30923403, 56933926, 4544283, 19810413, 64176595, 54936154, 45790182, 19869621, 3534243, 26086113, 1516198, 27563365, 31145766, 63827007, 37105034, 61205608, 16728599, 16357722, 16380240, 27992600, 54906687, 6214052, 57406974, 14156786],
   [60780325, 39876118, 60772595, 10751042, 64442562, 29745294, 23471516, 64398732, 31709160, 55460958, 46543253, 58525620, 54872568, 24185549, 16725835, 24098535, 45114592, 48168664, 5338853, 2382351, 60754229, 41771391, 45643026, 40242368, 41701890, 11419439],
   [60344196, 47835039, 59338455, 31775055, 35333804, 0, 0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 14557495, 45685953, 33184234, 53404362, 56359530, 43891075],
   [37941231, 59298165, 55215592, 11893267, 55215592, 0, 0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 29038196, 27324277, 2735956],
   [29167628, 7810694, 50384903, 30145723, 36963136, 0, 0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 38070663, 1174306, 49961425],
   [37941231, 59298165, 55215592, 11893267, 55215592, 0, 0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 29038196, 27324277, 2735956],
   [29167628, 7810694, 50384903, 30145723, 36963136, 0, 0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 38070663, 1174306, 49961425],
   [50994660, 65051760, 64794872, 2313987, 64794872, 0, 0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 51236637, 401314, 43576062, 66578807, 14206608, 4871916, 24355651],
   [57283516, 48393232, 52335024, 28195602, 38913257, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 274886, 58059814, 1581711],
   [9825343, 18715627, 53265471, 13843388, 53265471, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 30781395, 59260851, 16724588, 8340846, 66833973, 37547628, 51115670],
   [57283516, 48393232, 52335024, 28195602, 38913257, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 274886, 58059814, 1581711],
   [44696492, 30610428, 12905848, 54203011, 12905848, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 33296619, 6989205, 35357300, 35679418, 33733785, 36842664, 3288229],
   [17290112, 61842414, 6327037, 7094730, 60014129, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32721354, 15413076, 2729723, 32448836, 18243790, 15531512, 44140802],
   [29619927, 31317934, 36846363, 30262496, 36846363, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55213590, 15023587, 51962733, 35986914, 39745628, 30609244],
   [63434570, 9747478, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 66254623, 1017217, 67012117, 59903120],
   [23635780, 10214013, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 854236, 43907008, 52293003, 59903120],
   [7988780, 21410547, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19130450, 14825265, 59903120],
   [0, 53687092, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59903120],
   [0, 0, 19245818, 47863041, 19245818, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28498583, 59903120],
   [0, 0, 19245818, 61284808, 5824051, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28498583, 59903120],
   [0, 0, 1671681, 65437178, 1671681, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9649696],
   [56607033, 9210277, 3984693, 53786542, 1823436, 19295906, 46932547, 52574691, 41281620, 57692557, 6842099, 64953307, 38457555, 7207738, 32577576, 45406233, 66990190, 42214643, 22503486, 45366761, 64564504, 49943178, 65896211, 49411048, 39056332, 63122433],
   [63317302, 62350738, 16850819, 3979097, 41205385, 17759178, 2774329, 16737460, 8274298, 53781368, 8735656, 59906376, 45942704, 45678226, 13995966, 16441811, 34331271, 37890566, 49678027, 5510641, 63932532, 58335748, 51746746, 25958501, 51480988, 59509947],
   [45698312, 45698312, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47978409, 52283594, 0]]

/-- N2c minor certificate 25: rows 0..21, cols 23..44 (det mod P = 4841081). -/
def n2cR25 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
def n2cC25 : List ℕ := [23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44]
def n2cS25 : List (List ℕ) := [[65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [55442623, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [7012739, 48115129, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [42057346, 48115129, 13835394, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [42057346, 64601377, 13835394, 24513689, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [65097439, 31673818, 39658851, 26832714, 20229401, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 20229401, 44968210, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 44968210, 18158048, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 18158048, 48330998, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 18007575, 18016103, 19343644, 11273162, 51008785, 12592366, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2015659, 43879536, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 43879536, 28905597, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 28905597, 3784423, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 2742273, 22502155, 1147129, 40521199, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 61487678, 15056340, 47168114, 40068907, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [42057346, 64601377, 52878468, 6168440, 40133282, 309759, 55855799, 53535715, 48288074, 19343644, 11273162, 51008785, 12592366, 66726684, 53888547, 8685970, 47546318, 31157861, 32135978, 54165319, 5322943, 43030449],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 18561397, 4229540, 2105309, 6591181, 57656413, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 4229540, 25632564, 6591181, 57656413, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 25632564, 24807078, 57656413, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 24807078, 25706444, 57401204, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 25706444, 10804460, 20769422, 15495622],
   [65097439, 31673818, 39658851, 4626330, 63654391, 17009534, 58669064, 56929001, 2661626, 14507733, 42009301, 21479374, 42998704, 51191991, 47168114, 40068907, 2105309, 6591181, 57656413, 10804460, 26510245, 15495622]]
def n2cT25 : List (List ℕ) := [[2074659, 49773306, 50221868, 46729204, 52049804, 26898392, 38361964, 6569999, 3199107, 36227403, 53714821, 7314243, 37409683, 26907540, 3622241, 61794096, 57180861, 2638056, 51924348, 50736937, 42605997, 58471315],
   [65034200, 53765278, 16886991, 64106388, 66180702, 15854800, 36556225, 42545655, 2234593, 31413450, 29726088, 30362292, 54948374, 63145741, 26821874, 7987564, 49121094, 66266647, 42958627, 41839491, 40330060, 41523293],
   [0, 56563780, 55323840, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 14557495, 45685953, 33184234, 30011733, 43535046, 61013418, 34261667, 1918644],
   [0, 0, 11785019, 16017835, 45138884, 32064894, 18307627, 3282311, 61409761, 6116181, 6819080, 34484604, 58289062, 19310468, 52551364, 21422906, 33924625, 37097126, 23573813, 6095441, 32847192, 7597420],
   [0, 0, 0, 51091024, 21969975, 35043965, 48801232, 63826548, 5699098, 60992678, 60289779, 32624255, 8819797, 47798391, 14557495, 45685953, 33184234, 30011733, 43535046, 61013418, 34261667, 36513808],
   [0, 0, 0, 0, 53802771, 59920831, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 820746, 35162805, 37256131, 62931035, 45751925],
   [0, 0, 0, 0, 0, 7188028, 28138400, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 66288113, 31946054, 29852728, 4177824, 34778701],
   [0, 0, 0, 0, 0, 0, 38970459, 14215982, 26726250, 25480551, 56551347, 15183427, 10316352, 32148463, 57405434, 5456564, 27218431, 820746, 35162805, 37256131, 62931035, 45751925],
   [0, 0, 0, 0, 0, 0, 0, 52892877, 40382609, 41628308, 10557512, 51925432, 56792507, 34960396, 9703425, 61652295, 39890428, 66288113, 31946054, 29852728, 4177824, 34778701],
   [0, 0, 0, 0, 0, 0, 0, 0, 57334486, 14282199, 28124472, 11681945, 61590929, 51236637, 401314, 43576062, 66578807, 66515694, 56171416, 17463983, 42555372, 53051759],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 55688841, 25875500, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 12848507, 2817511, 3904942, 39555252, 22312051],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 41233359, 52012229, 14410801, 30781395, 59260851, 16724588, 8340846, 54260352, 64291348, 63203917, 27553607, 58218575],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15096630, 52698058, 36327464, 7848008, 50384271, 58768013, 12848507, 2817511, 3904942, 39555252, 22312051],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5346550, 33296619, 6989205, 35357300, 35679418, 10617726, 44967568, 3654035, 61297893, 14086064],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32721354, 15413076, 2729723, 32448836, 13127019, 53776421, 42649336, 62873304, 35978324],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55213590, 15023587, 51962733, 22198407, 60485370, 10250389, 8074259, 65410852],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26458105, 66254623, 1097127, 27030834, 28498583, 20165624, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 854236, 66011732, 40078025, 38610276, 46943235, 13421767],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1097127, 27030834, 28498583, 20165624, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40078025, 38610276, 46943235, 13421767],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28498583, 20165624, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 46943235, 13421767]]

/-- N2c minor certificate 26: rows [0, 4], cols [26, 27] (det mod P = 32585344). -/
def n2cR26 : List ℕ := [0, 4]
def n2cC26 : List ℕ := [26, 27]
def n2cS26 : List (List ℕ) := [[4626330, 63654391],
   [24513689, 40133282]]
def n2cT26 : List (List ℕ) := [[43726733, 14211652],
   [51091024, 21969975]]

/-- N2c minor certificate 27: rows [0, 16], cols [38, 39] (det mod P = 35806779). -/
def n2cR27 : List ℕ := [0, 16]
def n2cC27 : List ℕ := [38, 39]
def n2cS27 : List (List ℕ) := [[40068907, 2105309],
   [4229540, 2105309]]
def n2cT27 : List (List ℕ) := [[40650754, 58641656],
   [26458105, 66254623]]

/-- N2c minor certificate 28: rows [0, 20], cols [42, 43] (det mod P = 48232105). -/
def n2cR28 : List ℕ := [0, 20]
def n2cC28 : List ℕ := [42, 43]
def n2cS28 : List (List ℕ) := [[57401204, 20769422],
   [10804460, 20769422]]
def n2cT28 : List (List ℕ) := [[38610276, 3835327],
   [28498583, 20165624]]

/-- N2c minor certificate 29: rows [0, 9], cols [31, 32] (det mod P = 52378980). -/
def n2cR29 : List ℕ := [0, 9]
def n2cC29 : List ℕ := [31, 32]
def n2cS29 : List (List ℕ) := [[2661626, 14507733],
   [18016103, 19343644]]
def n2cT29 : List (List ℕ) := [[35402117, 33515156],
   [57334486, 14282199]]

/-- N2c minor certificate 30: rows [0, 3], cols [25, 26] (det mod P = 33294419). -/
def n2cR30 : List ℕ := [0, 3]
def n2cC30 : List ℕ := [25, 26]
def n2cS30 : List (List ℕ) := [[39658851, 4626330],
   [13835394, 6168440]]
def n2cT30 : List (List ℕ) := [[6656261, 17386224],
   [11785019, 27563311]]

/-- N2c minor certificate 31: rows [0, 19], cols [41, 42] (det mod P = 19028811). -/
def n2cR31 : List ℕ := [0, 19]
def n2cC31 : List ℕ := [41, 42]
def n2cS31 : List (List ℕ) := [[57656413, 57401204],
   [25706444, 57401204]]
def n2cT31 : List (List ℕ) := [[27030834, 57917607],
   [40078025, 38610276]]

/-- N2c minor certificate 32: rows [0, 1], cols [23, 24] (det mod P = 14891056). -/
def n2cR32 : List ℕ := [0, 1]
def n2cC32 : List ℕ := [23, 24]
def n2cS32 : List (List ℕ) := [[65097439, 31673818],
   [55442623, 31673818]]
def n2cT32 : List (List ℕ) := [[2074659, 65926728],
   [65034200, 48799886]]

/-- N2c minor certificate 33: rows [0, 15], cols [37, 38] (det mod P = 40072897). -/
def n2cR33 : List ℕ := [0, 15]
def n2cC33 : List ℕ := [37, 38]
def n2cS33 : List (List ℕ) := [[47168114, 40068907],
   [53888547, 8685970]]
def n2cT33 : List (List ℕ) := [[60599598, 17488976],
   [55213590, 15023587]]

/-- N2c minor certificate 34: rows [0, 7], cols [29, 30] (det mod P = 30487046). -/
def n2cR34 : List ℕ := [0, 7]
def n2cC34 : List ℕ := [29, 30]
def n2cS34 : List (List ℕ) := [[58669064, 56929001],
   [18158048, 56929001]]
def n2cT34 : List (List ℕ) := [[28138400, 11499707],
   [38970459, 14215982]]

/-- N2c minor certificate 35: rows [0, 14], cols [36, 37] (det mod P = 42054527). -/
def n2cR35 : List ℕ := [0, 14]
def n2cC35 : List ℕ := [36, 37]
def n2cS35 : List (List ℕ) := [[51191991, 47168114],
   [15056340, 47168114]]
def n2cT35 : List (List ℕ) := [[34387505, 37345867],
   [32721354, 62984015]]

/-- N2c minor certificate 36: rows [0, 11], cols [33, 34] (det mod P = 39626307). -/
def n2cR36 : List ℕ := [0, 11]
def n2cC36 : List ℕ := [33, 34]
def n2cS36 : List (List ℕ) := [[42009301, 21479374],
   [28905597, 21479374]]
def n2cT36 : List (List ℕ) := [[25875500, 20451595],
   [41233359, 52012229]]

/-- N2c minor certificate 37: rows [0, 18], cols [40, 41] (det mod P = 26428235). -/
def n2cR37 : List ℕ := [0, 18]
def n2cC37 : List ℕ := [40, 41]
def n2cS37 : List (List ℕ) := [[6591181, 57656413],
   [24807078, 57656413]]
def n2cT37 : List (List ℕ) := [[66011732, 31125968],
   [1097127, 27030834]]

/-- N2c minor certificate 38: rows [0, 10], cols [32, 33] (det mod P = 2691858). -/
def n2cR38 : List ℕ := [0, 10]
def n2cC38 : List ℕ := [32, 33]
def n2cS38 : List (List ℕ) := [[14507733, 42009301],
   [43879536, 42009301]]
def n2cT38 : List (List ℕ) := [[11420018, 51248677],
   [55688841, 25875500]]

/-- N2c minor certificate 39: rows [0, 5], cols [27, 28] (det mod P = 19889017). -/
def n2cR39 : List ℕ := [0, 5]
def n2cC39 : List ℕ := [27, 28]
def n2cS39 : List (List ℕ) := [[63654391, 17009534],
   [20229401, 17009534]]
def n2cT39 : List (List ℕ) := [[13306088, 1425247],
   [53802771, 59920831]]

/-- N2c minor certificate 40: rows [0, 17], cols [39, 40] (det mod P = 3775826). -/
def n2cR40 : List ℕ := [0, 17]
def n2cC40 : List ℕ := [39, 40]
def n2cS40 : List (List ℕ) := [[2105309, 6591181],
   [25632564, 6591181]]
def n2cT40 : List (List ℕ) := [[66254623, 46628652],
   [854236, 66011732]]

/-- N2c minor certificate 41: rows [0, 12], cols [34, 35] (det mod P = 50985781). -/
def n2cR41 : List ℕ := [0, 12]
def n2cC41 : List ℕ := [34, 35]
def n2cS41 : List (List ℕ) := [[21479374, 42998704],
   [3784423, 42998704]]
def n2cT41 : List (List ℕ) := [[52012229, 27190969],
   [15096630, 11510592]]

/-- N2c minor certificate 42: rows [0, 21], cols [43, 44] (det mod P = 1265442). -/
def n2cR42 : List ℕ := [0, 21]
def n2cC42 : List ℕ := [43, 44]
def n2cS42 : List (List ℕ) := [[20769422, 15495622],
   [26510245, 15495622]]
def n2cT42 : List (List ℕ) := [[20165624, 16106154],
   [46943235, 13421767]]

/-- N2c minor certificate 43: rows [0, 8], cols [30, 31] (det mod P = 10543006). -/
def n2cR43 : List ℕ := [0, 8]
def n2cC43 : List ℕ := [30, 31]
def n2cS43 : List (List ℕ) := [[56929001, 2661626],
   [48330998, 2661626]]
def n2cT43 : List (List ℕ) := [[14215982, 44777422],
   [52892877, 64016811]]

/-- N2c minor certificate 44: rows [0, 2], cols [24, 25] (det mod P = 11652490). -/
def n2cR44 : List ℕ := [0, 2]
def n2cC44 : List ℕ := [24, 25]
def n2cS44 : List (List ℕ) := [[31673818, 39658851],
   [48115129, 52878468]]
def n2cT44 : List (List ℕ) := [[36429725, 52961823],
   [56563780, 42421926]]

/-- N2c minor certificate 45: rows [0, 6], cols [28, 29] (det mod P = 8249980). -/
def n2cR45 : List ℕ := [0, 6]
def n2cC45 : List ℕ := [28, 29]
def n2cS45 : List (List ℕ) := [[17009534, 58669064],
   [44968210, 58669064]]
def n2cT45 : List (List ℕ) := [[59920831, 38123857],
   [7188028, 28138400]]

/-- N2c minor certificate 46: rows [0, 13], cols [35, 36] (det mod P = 7009534). -/
def n2cR46 : List ℕ := [0, 13]
def n2cC46 : List ℕ := [35, 36]
def n2cS46 : List (List ℕ) := [[42998704, 51191991],
   [22502155, 1147129]]
def n2cT46 : List (List ℕ) := [[37610506, 58979920],
   [5346550, 33296619]]


theorem n2cChk0 : certChk n2cS0 n2cT0 1 stairCertP = true := by decide +kernel
theorem n2cEnt0 : ((List.range 1).all fun i => (List.range 1).all fun j =>
    decide (corZStair stairMZ (n2cR0.getD i 0) (n2cC0.getD j 0) % (stairCertP : ℤ) =
      (((n2cS0.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk1 : certChk n2cS1 n2cT1 25 stairCertP = true := by decide +kernel
theorem n2cEnt1 : ((List.range 25).all fun i => (List.range 25).all fun j =>
    decide (corZStair stairMZ (n2cR1.getD i 0) (n2cC1.getD j 0) % (stairCertP : ℤ) =
      (((n2cS1.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk2 : certChk n2cS2 n2cT2 44 stairCertP = true := by decide +kernel
theorem n2cEnt2 : ((List.range 44).all fun i => (List.range 44).all fun j =>
    decide (corZStair stairMZ (n2cR2.getD i 0) (n2cC2.getD j 0) % (stairCertP : ℤ) =
      (((n2cS2.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk3 : certChk n2cS3 n2cT3 24 stairCertP = true := by decide +kernel
theorem n2cEnt3 : ((List.range 24).all fun i => (List.range 24).all fun j =>
    decide (corZStair stairMZ (n2cR3.getD i 0) (n2cC3.getD j 0) % (stairCertP : ℤ) =
      (((n2cS3.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk4 : certChk n2cS4 n2cT4 23 stairCertP = true := by decide +kernel
theorem n2cEnt4 : ((List.range 23).all fun i => (List.range 23).all fun j =>
    decide (corZStair stairMZ (n2cR4.getD i 0) (n2cC4.getD j 0) % (stairCertP : ℤ) =
      (((n2cS4.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk5 : certChk n2cS5 n2cT5 45 stairCertP = true := by decide +kernel
theorem n2cEnt5 : ((List.range 45).all fun i => (List.range 45).all fun j =>
    decide (corZStair stairMZ (n2cR5.getD i 0) (n2cC5.getD j 0) % (stairCertP : ℤ) =
      (((n2cS5.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk6 : certChk n2cS6 n2cT6 43 stairCertP = true := by decide +kernel
theorem n2cEnt6 : ((List.range 43).all fun i => (List.range 43).all fun j =>
    decide (corZStair stairMZ (n2cR6.getD i 0) (n2cC6.getD j 0) % (stairCertP : ℤ) =
      (((n2cS6.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk7 : certChk n2cS7 n2cT7 26 stairCertP = true := by decide +kernel
theorem n2cEnt7 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR7.getD i 0) (n2cC7.getD j 0) % (stairCertP : ℤ) =
      (((n2cS7.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk8 : certChk n2cS8 n2cT8 26 stairCertP = true := by decide +kernel
theorem n2cEnt8 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR8.getD i 0) (n2cC8.getD j 0) % (stairCertP : ℤ) =
      (((n2cS8.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk9 : certChk n2cS9 n2cT9 26 stairCertP = true := by decide +kernel
theorem n2cEnt9 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR9.getD i 0) (n2cC9.getD j 0) % (stairCertP : ℤ) =
      (((n2cS9.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk10 : certChk n2cS10 n2cT10 26 stairCertP = true := by decide +kernel
theorem n2cEnt10 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR10.getD i 0) (n2cC10.getD j 0) % (stairCertP : ℤ) =
      (((n2cS10.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk11 : certChk n2cS11 n2cT11 26 stairCertP = true := by decide +kernel
theorem n2cEnt11 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR11.getD i 0) (n2cC11.getD j 0) % (stairCertP : ℤ) =
      (((n2cS11.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk12 : certChk n2cS12 n2cT12 26 stairCertP = true := by decide +kernel
theorem n2cEnt12 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR12.getD i 0) (n2cC12.getD j 0) % (stairCertP : ℤ) =
      (((n2cS12.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk13 : certChk n2cS13 n2cT13 26 stairCertP = true := by decide +kernel
theorem n2cEnt13 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR13.getD i 0) (n2cC13.getD j 0) % (stairCertP : ℤ) =
      (((n2cS13.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk14 : certChk n2cS14 n2cT14 26 stairCertP = true := by decide +kernel
theorem n2cEnt14 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR14.getD i 0) (n2cC14.getD j 0) % (stairCertP : ℤ) =
      (((n2cS14.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk15 : certChk n2cS15 n2cT15 26 stairCertP = true := by decide +kernel
theorem n2cEnt15 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR15.getD i 0) (n2cC15.getD j 0) % (stairCertP : ℤ) =
      (((n2cS15.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk16 : certChk n2cS16 n2cT16 26 stairCertP = true := by decide +kernel
theorem n2cEnt16 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR16.getD i 0) (n2cC16.getD j 0) % (stairCertP : ℤ) =
      (((n2cS16.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk17 : certChk n2cS17 n2cT17 26 stairCertP = true := by decide +kernel
theorem n2cEnt17 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR17.getD i 0) (n2cC17.getD j 0) % (stairCertP : ℤ) =
      (((n2cS17.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk18 : certChk n2cS18 n2cT18 26 stairCertP = true := by decide +kernel
theorem n2cEnt18 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR18.getD i 0) (n2cC18.getD j 0) % (stairCertP : ℤ) =
      (((n2cS18.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk19 : certChk n2cS19 n2cT19 26 stairCertP = true := by decide +kernel
theorem n2cEnt19 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR19.getD i 0) (n2cC19.getD j 0) % (stairCertP : ℤ) =
      (((n2cS19.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk20 : certChk n2cS20 n2cT20 26 stairCertP = true := by decide +kernel
theorem n2cEnt20 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR20.getD i 0) (n2cC20.getD j 0) % (stairCertP : ℤ) =
      (((n2cS20.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk21 : certChk n2cS21 n2cT21 26 stairCertP = true := by decide +kernel
theorem n2cEnt21 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR21.getD i 0) (n2cC21.getD j 0) % (stairCertP : ℤ) =
      (((n2cS21.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk22 : certChk n2cS22 n2cT22 26 stairCertP = true := by decide +kernel
theorem n2cEnt22 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR22.getD i 0) (n2cC22.getD j 0) % (stairCertP : ℤ) =
      (((n2cS22.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk23 : certChk n2cS23 n2cT23 26 stairCertP = true := by decide +kernel
theorem n2cEnt23 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR23.getD i 0) (n2cC23.getD j 0) % (stairCertP : ℤ) =
      (((n2cS23.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk24 : certChk n2cS24 n2cT24 26 stairCertP = true := by decide +kernel
theorem n2cEnt24 : ((List.range 26).all fun i => (List.range 26).all fun j =>
    decide (corZStair stairMZ (n2cR24.getD i 0) (n2cC24.getD j 0) % (stairCertP : ℤ) =
      (((n2cS24.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk25 : certChk n2cS25 n2cT25 22 stairCertP = true := by decide +kernel
theorem n2cEnt25 : ((List.range 22).all fun i => (List.range 22).all fun j =>
    decide (corZStair stairMZ (n2cR25.getD i 0) (n2cC25.getD j 0) % (stairCertP : ℤ) =
      (((n2cS25.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk26 : certChk n2cS26 n2cT26 2 stairCertP = true := by decide +kernel
theorem n2cEnt26 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR26.getD i 0) (n2cC26.getD j 0) % (stairCertP : ℤ) =
      (((n2cS26.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk27 : certChk n2cS27 n2cT27 2 stairCertP = true := by decide +kernel
theorem n2cEnt27 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR27.getD i 0) (n2cC27.getD j 0) % (stairCertP : ℤ) =
      (((n2cS27.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk28 : certChk n2cS28 n2cT28 2 stairCertP = true := by decide +kernel
theorem n2cEnt28 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR28.getD i 0) (n2cC28.getD j 0) % (stairCertP : ℤ) =
      (((n2cS28.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk29 : certChk n2cS29 n2cT29 2 stairCertP = true := by decide +kernel
theorem n2cEnt29 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR29.getD i 0) (n2cC29.getD j 0) % (stairCertP : ℤ) =
      (((n2cS29.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk30 : certChk n2cS30 n2cT30 2 stairCertP = true := by decide +kernel
theorem n2cEnt30 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR30.getD i 0) (n2cC30.getD j 0) % (stairCertP : ℤ) =
      (((n2cS30.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk31 : certChk n2cS31 n2cT31 2 stairCertP = true := by decide +kernel
theorem n2cEnt31 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR31.getD i 0) (n2cC31.getD j 0) % (stairCertP : ℤ) =
      (((n2cS31.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk32 : certChk n2cS32 n2cT32 2 stairCertP = true := by decide +kernel
theorem n2cEnt32 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR32.getD i 0) (n2cC32.getD j 0) % (stairCertP : ℤ) =
      (((n2cS32.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk33 : certChk n2cS33 n2cT33 2 stairCertP = true := by decide +kernel
theorem n2cEnt33 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR33.getD i 0) (n2cC33.getD j 0) % (stairCertP : ℤ) =
      (((n2cS33.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk34 : certChk n2cS34 n2cT34 2 stairCertP = true := by decide +kernel
theorem n2cEnt34 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR34.getD i 0) (n2cC34.getD j 0) % (stairCertP : ℤ) =
      (((n2cS34.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk35 : certChk n2cS35 n2cT35 2 stairCertP = true := by decide +kernel
theorem n2cEnt35 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR35.getD i 0) (n2cC35.getD j 0) % (stairCertP : ℤ) =
      (((n2cS35.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk36 : certChk n2cS36 n2cT36 2 stairCertP = true := by decide +kernel
theorem n2cEnt36 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR36.getD i 0) (n2cC36.getD j 0) % (stairCertP : ℤ) =
      (((n2cS36.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk37 : certChk n2cS37 n2cT37 2 stairCertP = true := by decide +kernel
theorem n2cEnt37 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR37.getD i 0) (n2cC37.getD j 0) % (stairCertP : ℤ) =
      (((n2cS37.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk38 : certChk n2cS38 n2cT38 2 stairCertP = true := by decide +kernel
theorem n2cEnt38 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR38.getD i 0) (n2cC38.getD j 0) % (stairCertP : ℤ) =
      (((n2cS38.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk39 : certChk n2cS39 n2cT39 2 stairCertP = true := by decide +kernel
theorem n2cEnt39 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR39.getD i 0) (n2cC39.getD j 0) % (stairCertP : ℤ) =
      (((n2cS39.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk40 : certChk n2cS40 n2cT40 2 stairCertP = true := by decide +kernel
theorem n2cEnt40 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR40.getD i 0) (n2cC40.getD j 0) % (stairCertP : ℤ) =
      (((n2cS40.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk41 : certChk n2cS41 n2cT41 2 stairCertP = true := by decide +kernel
theorem n2cEnt41 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR41.getD i 0) (n2cC41.getD j 0) % (stairCertP : ℤ) =
      (((n2cS41.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk42 : certChk n2cS42 n2cT42 2 stairCertP = true := by decide +kernel
theorem n2cEnt42 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR42.getD i 0) (n2cC42.getD j 0) % (stairCertP : ℤ) =
      (((n2cS42.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk43 : certChk n2cS43 n2cT43 2 stairCertP = true := by decide +kernel
theorem n2cEnt43 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR43.getD i 0) (n2cC43.getD j 0) % (stairCertP : ℤ) =
      (((n2cS43.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk44 : certChk n2cS44 n2cT44 2 stairCertP = true := by decide +kernel
theorem n2cEnt44 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR44.getD i 0) (n2cC44.getD j 0) % (stairCertP : ℤ) =
      (((n2cS44.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk45 : certChk n2cS45 n2cT45 2 stairCertP = true := by decide +kernel
theorem n2cEnt45 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR45.getD i 0) (n2cC45.getD j 0) % (stairCertP : ℤ) =
      (((n2cS45.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk46 : certChk n2cS46 n2cT46 2 stairCertP = true := by decide +kernel
theorem n2cEnt46 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR46.getD i 0) (n2cC46.getD j 0) % (stairCertP : ℤ) =
      (((n2cS46.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cPiv0 : IsPiv stairCornerQ 0 (stairPC.getD 0 0) := by
  have hpc : stairPC.getD 0 0 = 44 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 0 44 0 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 0 44
  · exact rk_le_height stairCornerQ 1 44
  · exact rk_le_height stairCornerQ 0 45
  · refine rk_le_width stairCornerQ 1 45 (by decide)
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0
  · exact Nat.zero_le _

theorem n2cPiv1 : IsPiv stairCornerQ 1 (stairPC.getD 1 0) := by
  have hpc : stairPC.getD 1 0 = 23 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 1 23 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 1 23
  · exact rk_le_height stairCornerQ 2 23
  · exact rk_le_height stairCornerQ 1 24
  · exact rkQ_le_of_block 2 24 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR32 n2cC32 (by decide) (by decide) (by decide) n2cS32 n2cT32 n2cChk32 n2cEnt32
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv2 : IsPiv stairCornerQ 2 (stairPC.getD 2 0) := by
  have hpc : stairPC.getD 2 0 = 24 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 2 24 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 2 24 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 3 24 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 2 25 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 3 25 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR44 n2cC44 (by decide) (by decide) (by decide) n2cS44 n2cT44 n2cChk44 n2cEnt44
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv3 : IsPiv stairCornerQ 3 (stairPC.getD 3 0) := by
  have hpc : stairPC.getD 3 0 = 25 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 3 25 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 3 25 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 4 25 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 3 26 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 4 26 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR30 n2cC30 (by decide) (by decide) (by decide) n2cS30 n2cT30 n2cChk30 n2cEnt30
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv4 : IsPiv stairCornerQ 4 (stairPC.getD 4 0) := by
  have hpc : stairPC.getD 4 0 = 26 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 4 26 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 4 26 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 5 26 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 4 27 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 5 27 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR26 n2cC26 (by decide) (by decide) (by decide) n2cS26 n2cT26 n2cChk26 n2cEnt26
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv5 : IsPiv stairCornerQ 5 (stairPC.getD 5 0) := by
  have hpc : stairPC.getD 5 0 = 27 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 5 27 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 5 27 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 6 27 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 5 28 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 6 28 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR39 n2cC39 (by decide) (by decide) (by decide) n2cS39 n2cT39 n2cChk39 n2cEnt39
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv6 : IsPiv stairCornerQ 6 (stairPC.getD 6 0) := by
  have hpc : stairPC.getD 6 0 = 28 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 6 28 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 6 28 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 7 28 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 6 29 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 7 29 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR45 n2cC45 (by decide) (by decide) (by decide) n2cS45 n2cT45 n2cChk45 n2cEnt45
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv7 : IsPiv stairCornerQ 7 (stairPC.getD 7 0) := by
  have hpc : stairPC.getD 7 0 = 29 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 7 29 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 7 29 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 8 29 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 7 30 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 8 30 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR34 n2cC34 (by decide) (by decide) (by decide) n2cS34 n2cT34 n2cChk34 n2cEnt34
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv8 : IsPiv stairCornerQ 8 (stairPC.getD 8 0) := by
  have hpc : stairPC.getD 8 0 = 30 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 8 30 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 8 30 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 9 30 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 8 31 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 9 31 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR43 n2cC43 (by decide) (by decide) (by decide) n2cS43 n2cT43 n2cChk43 n2cEnt43
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv9 : IsPiv stairCornerQ 9 (stairPC.getD 9 0) := by
  have hpc : stairPC.getD 9 0 = 31 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 9 31 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 9 31 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 10 31 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 9 32 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 10 32 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR29 n2cC29 (by decide) (by decide) (by decide) n2cS29 n2cT29 n2cChk29 n2cEnt29
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv10 : IsPiv stairCornerQ 10 (stairPC.getD 10 0) := by
  have hpc : stairPC.getD 10 0 = 32 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 10 32 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 10 32 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 11 32 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 10 33 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 11 33 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR38 n2cC38 (by decide) (by decide) (by decide) n2cS38 n2cT38 n2cChk38 n2cEnt38
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv11 : IsPiv stairCornerQ 11 (stairPC.getD 11 0) := by
  have hpc : stairPC.getD 11 0 = 33 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 11 33 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 11 33 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 12 33 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 11 34 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 12 34 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR36 n2cC36 (by decide) (by decide) (by decide) n2cS36 n2cT36 n2cChk36 n2cEnt36
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv12 : IsPiv stairCornerQ 12 (stairPC.getD 12 0) := by
  have hpc : stairPC.getD 12 0 = 34 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 12 34 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 12 34 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 13 34 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 12 35 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 13 35 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR41 n2cC41 (by decide) (by decide) (by decide) n2cS41 n2cT41 n2cChk41 n2cEnt41
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv13 : IsPiv stairCornerQ 13 (stairPC.getD 13 0) := by
  have hpc : stairPC.getD 13 0 = 35 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 13 35 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 13 35 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 14 35 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 13 36 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 14 36 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR46 n2cC46 (by decide) (by decide) (by decide) n2cS46 n2cT46 n2cChk46 n2cEnt46
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv14 : IsPiv stairCornerQ 14 (stairPC.getD 14 0) := by
  have hpc : stairPC.getD 14 0 = 36 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 14 36 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 14 36 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 15 36 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 14 37 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 15 37 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR35 n2cC35 (by decide) (by decide) (by decide) n2cS35 n2cT35 n2cChk35 n2cEnt35
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv15 : IsPiv stairCornerQ 15 (stairPC.getD 15 0) := by
  have hpc : stairPC.getD 15 0 = 37 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 15 37 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 15 37 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 16 37 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 15 38 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 16 38 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR33 n2cC33 (by decide) (by decide) (by decide) n2cS33 n2cT33 n2cChk33 n2cEnt33
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv16 : IsPiv stairCornerQ 16 (stairPC.getD 16 0) := by
  have hpc : stairPC.getD 16 0 = 38 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 16 38 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 16 38 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 17 38 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 16 39 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 17 39 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR27 n2cC27 (by decide) (by decide) (by decide) n2cS27 n2cT27 n2cChk27 n2cEnt27
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv17 : IsPiv stairCornerQ 17 (stairPC.getD 17 0) := by
  have hpc : stairPC.getD 17 0 = 39 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 17 39 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 17 39 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 18 39 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 17 40 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 18 40 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR40 n2cC40 (by decide) (by decide) (by decide) n2cS40 n2cT40 n2cChk40 n2cEnt40
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv18 : IsPiv stairCornerQ 18 (stairPC.getD 18 0) := by
  have hpc : stairPC.getD 18 0 = 40 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 18 40 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 18 40 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 19 40 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 18 41 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 19 41 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR37 n2cC37 (by decide) (by decide) (by decide) n2cS37 n2cT37 n2cChk37 n2cEnt37
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv19 : IsPiv stairCornerQ 19 (stairPC.getD 19 0) := by
  have hpc : stairPC.getD 19 0 = 41 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 19 41 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 19 41 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 20 41 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 19 42 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 20 42 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR31 n2cC31 (by decide) (by decide) (by decide) n2cS31 n2cT31 n2cChk31 n2cEnt31
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv20 : IsPiv stairCornerQ 20 (stairPC.getD 20 0) := by
  have hpc : stairPC.getD 20 0 = 42 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 20 42 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 20 42 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 21 42 2 2 (by decide) (by decide)
  · exact rkQ_le_of_block 20 43 1 1 (by decide) (by decide)
  · exact rkQ_le_of_block 21 43 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR28 n2cC28 (by decide) (by decide) (by decide) n2cS28 n2cT28 n2cChk28 n2cEnt28
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv21 : IsPiv stairCornerQ 21 (stairPC.getD 21 0) := by
  have hpc : stairPC.getD 21 0 = 43 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 21 43 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 21 43 1 1 (by decide) (by decide)
  · refine rk_le_width stairCornerQ 22 43 (by decide)
  · refine rk_le_width stairCornerQ 21 44 (by decide)
  · refine rk_le_width stairCornerQ 22 44 (by decide)
  · refine n2c_rank_lower (by decide) n2cR42 n2cC42 (by decide) (by decide) (by decide) n2cS42 n2cT42 n2cChk42 n2cEnt42
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

theorem n2cPiv22 : IsPiv stairCornerQ 22 (stairPC.getD 22 0) := by
  have hpc : stairPC.getD 22 0 = 22 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 22 22 22 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 22 22
  · exact rk_le_height stairCornerQ 23 22
  · exact rk_le_height stairCornerQ 22 23
  · refine rk_le_width stairCornerQ 23 23 (by decide)
  · refine n2c_rank_lower (by decide) n2cR4 n2cC4 (by decide) (by decide) (by decide) n2cS4 n2cT4 n2cChk4 n2cEnt4
  · refine n2c_rank_lower (by decide) n2cR25 n2cC25 (by decide) (by decide) (by decide) n2cS25 n2cT25 n2cChk25 n2cEnt25

theorem n2cPiv23 : IsPiv stairCornerQ 23 (stairPC.getD 23 0) := by
  have hpc : stairPC.getD 23 0 = 21 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 23 21 23 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 23 21
  · exact rk_le_height stairCornerQ 24 21
  · exact rk_le_height stairCornerQ 23 22
  · refine rk_le_width stairCornerQ 24 22 (by decide)
  · refine n2c_rank_lower (by decide) n2cR3 n2cC3 (by decide) (by decide) (by decide) n2cS3 n2cT3 n2cChk3 n2cEnt3
  · refine n2c_rank_lower (by decide) n2cR4 n2cC4 (by decide) (by decide) (by decide) n2cS4 n2cT4 n2cChk4 n2cEnt4

theorem n2cPiv24 : IsPiv stairCornerQ 24 (stairPC.getD 24 0) := by
  have hpc : stairPC.getD 24 0 = 20 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 24 20 24 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 24 20
  · exact rk_le_height stairCornerQ 25 20
  · exact rk_le_height stairCornerQ 24 21
  · refine rk_le_width stairCornerQ 25 21 (by decide)
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1
  · refine n2c_rank_lower (by decide) n2cR3 n2cC3 (by decide) (by decide) (by decide) n2cS3 n2cT3 n2cChk3 n2cEnt3

theorem n2cPiv25 : IsPiv stairCornerQ 25 (stairPC.getD 25 0) := by
  have hpc : stairPC.getD 25 0 = 2 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 25 2 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 25 2
  · exact rk_le_height stairCornerQ 26 2
  · exact rk_le_height stairCornerQ 25 3
  · exact rkQ_le_of_block 26 3 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR12 n2cC12 (by decide) (by decide) (by decide) n2cS12 n2cT12 n2cChk12 n2cEnt12
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv26 : IsPiv stairCornerQ 26 (stairPC.getD 26 0) := by
  have hpc : stairPC.getD 26 0 = 3 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 26 3 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 26 3 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 27 3 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 26 4 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 27 4 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR16 n2cC16 (by decide) (by decide) (by decide) n2cS16 n2cT16 n2cChk16 n2cEnt16
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv27 : IsPiv stairCornerQ 27 (stairPC.getD 27 0) := by
  have hpc : stairPC.getD 27 0 = 4 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 27 4 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 27 4 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 28 4 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 27 5 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 28 5 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR8 n2cC8 (by decide) (by decide) (by decide) n2cS8 n2cT8 n2cChk8 n2cEnt8
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv28 : IsPiv stairCornerQ 28 (stairPC.getD 28 0) := by
  have hpc : stairPC.getD 28 0 = 5 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 28 5 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 28 5 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 29 5 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 28 6 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 29 6 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR11 n2cC11 (by decide) (by decide) (by decide) n2cS11 n2cT11 n2cChk11 n2cEnt11
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv29 : IsPiv stairCornerQ 29 (stairPC.getD 29 0) := by
  have hpc : stairPC.getD 29 0 = 6 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 29 6 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 29 6 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 30 6 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 29 7 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 30 7 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR14 n2cC14 (by decide) (by decide) (by decide) n2cS14 n2cT14 n2cChk14 n2cEnt14
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv30 : IsPiv stairCornerQ 30 (stairPC.getD 30 0) := by
  have hpc : stairPC.getD 30 0 = 7 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 30 7 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 30 7 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 31 7 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 30 8 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 31 8 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR18 n2cC18 (by decide) (by decide) (by decide) n2cS18 n2cT18 n2cChk18 n2cEnt18
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv31 : IsPiv stairCornerQ 31 (stairPC.getD 31 0) := by
  have hpc : stairPC.getD 31 0 = 8 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 31 8 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 31 8 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 32 8 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 31 9 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 32 9 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR21 n2cC21 (by decide) (by decide) (by decide) n2cS21 n2cT21 n2cChk21 n2cEnt21
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv32 : IsPiv stairCornerQ 32 (stairPC.getD 32 0) := by
  have hpc : stairPC.getD 32 0 = 9 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 32 9 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 32 9 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 33 9 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 32 10 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 33 10 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR13 n2cC13 (by decide) (by decide) (by decide) n2cS13 n2cT13 n2cChk13 n2cEnt13
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv33 : IsPiv stairCornerQ 33 (stairPC.getD 33 0) := by
  have hpc : stairPC.getD 33 0 = 10 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 33 10 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 33 10 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 34 10 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 33 11 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 34 11 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR17 n2cC17 (by decide) (by decide) (by decide) n2cS17 n2cT17 n2cChk17 n2cEnt17
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv34 : IsPiv stairCornerQ 34 (stairPC.getD 34 0) := by
  have hpc : stairPC.getD 34 0 = 11 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 34 11 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 34 11 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 35 11 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 34 12 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 35 12 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR20 n2cC20 (by decide) (by decide) (by decide) n2cS20 n2cT20 n2cChk20 n2cEnt20
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv35 : IsPiv stairCornerQ 35 (stairPC.getD 35 0) := by
  have hpc : stairPC.getD 35 0 = 12 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 35 12 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 35 12 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 36 12 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 35 13 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 36 13 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR22 n2cC22 (by decide) (by decide) (by decide) n2cS22 n2cT22 n2cChk22 n2cEnt22
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv36 : IsPiv stairCornerQ 36 (stairPC.getD 36 0) := by
  have hpc : stairPC.getD 36 0 = 13 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 36 13 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 36 13 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 37 13 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 36 14 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 37 14 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR10 n2cC10 (by decide) (by decide) (by decide) n2cS10 n2cT10 n2cChk10 n2cEnt10
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv37 : IsPiv stairCornerQ 37 (stairPC.getD 37 0) := by
  have hpc : stairPC.getD 37 0 = 14 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 37 14 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 37 14 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 38 14 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 37 15 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 38 15 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR19 n2cC19 (by decide) (by decide) (by decide) n2cS19 n2cT19 n2cChk19 n2cEnt19
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv38 : IsPiv stairCornerQ 38 (stairPC.getD 38 0) := by
  have hpc : stairPC.getD 38 0 = 15 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 38 15 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 38 15 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 39 15 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 38 16 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 39 16 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR9 n2cC9 (by decide) (by decide) (by decide) n2cS9 n2cT9 n2cChk9 n2cEnt9
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv39 : IsPiv stairCornerQ 39 (stairPC.getD 39 0) := by
  have hpc : stairPC.getD 39 0 = 16 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 39 16 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 39 16 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 40 16 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 39 17 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 40 17 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR23 n2cC23 (by decide) (by decide) (by decide) n2cS23 n2cT23 n2cChk23 n2cEnt23
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv40 : IsPiv stairCornerQ 40 (stairPC.getD 40 0) := by
  have hpc : stairPC.getD 40 0 = 17 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 40 17 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 40 17 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 41 17 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 40 18 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 41 18 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR24 n2cC24 (by decide) (by decide) (by decide) n2cS24 n2cT24 n2cChk24 n2cEnt24
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv41 : IsPiv stairCornerQ 41 (stairPC.getD 41 0) := by
  have hpc : stairPC.getD 41 0 = 18 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 41 18 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 41 18 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 42 18 26 26 (by decide) (by decide)
  · exact rkQ_le_of_block 41 19 25 25 (by decide) (by decide)
  · exact rkQ_le_of_block 42 19 25 25 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR15 n2cC15 (by decide) (by decide) (by decide) n2cS15 n2cT15 n2cChk15 n2cEnt15
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv42 : IsPiv stairCornerQ 42 (stairPC.getD 42 0) := by
  have hpc : stairPC.getD 42 0 = 19 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 42 19 25 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rkQ_le_of_block 42 19 25 25 (by decide) (by decide)
  · refine rk_le_width stairCornerQ 43 19 (by decide)
  · refine rk_le_width stairCornerQ 42 20 (by decide)
  · refine rk_le_width stairCornerQ 43 20 (by decide)
  · refine n2c_rank_lower (by decide) n2cR7 n2cC7 (by decide) (by decide) (by decide) n2cS7 n2cT7 n2cChk7 n2cEnt7
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1

theorem n2cPiv43 : IsPiv stairCornerQ 43 (stairPC.getD 43 0) := by
  have hpc : stairPC.getD 43 0 = 1 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 43 1 43 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 43 1
  · exact rk_le_height stairCornerQ 44 1
  · exact rk_le_height stairCornerQ 43 2
  · refine rk_le_width stairCornerQ 44 2 (by decide)
  · refine n2c_rank_lower (by decide) n2cR2 n2cC2 (by decide) (by decide) (by decide) n2cS2 n2cT2 n2cChk2 n2cEnt2
  · refine n2c_rank_lower (by decide) n2cR6 n2cC6 (by decide) (by decide) (by decide) n2cS6 n2cT6 n2cChk6 n2cEnt6

theorem n2cPiv44 : IsPiv stairCornerQ 44 (stairPC.getD 44 0) := by
  have hpc : stairPC.getD 44 0 = 0 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 44 0 44 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 44 0
  · exact rk_le_height stairCornerQ 45 0
  · exact rk_le_height stairCornerQ 44 1
  · refine rk_le_width stairCornerQ 45 1 (by decide)
  · refine n2c_rank_lower (by decide) n2cR5 n2cC5 (by decide) (by decide) (by decide) n2cS5 n2cT5 n2cChk5 n2cEnt5
  · refine n2c_rank_lower (by decide) n2cR2 n2cC2 (by decide) (by decide) (by decide) n2cS2 n2cT2 n2cChk2 n2cEnt2

/-- Row-level form of N2c. -/
theorem stairPivAt (i : Fin 45) : IsPiv stairCornerQ i.val (stairPC.getD i.val 0) := by
  fin_cases i
  · exact n2cPiv0
  · exact n2cPiv1
  · exact n2cPiv2
  · exact n2cPiv3
  · exact n2cPiv4
  · exact n2cPiv5
  · exact n2cPiv6
  · exact n2cPiv7
  · exact n2cPiv8
  · exact n2cPiv9
  · exact n2cPiv10
  · exact n2cPiv11
  · exact n2cPiv12
  · exact n2cPiv13
  · exact n2cPiv14
  · exact n2cPiv15
  · exact n2cPiv16
  · exact n2cPiv17
  · exact n2cPiv18
  · exact n2cPiv19
  · exact n2cPiv20
  · exact n2cPiv21
  · exact n2cPiv22
  · exact n2cPiv23
  · exact n2cPiv24
  · exact n2cPiv25
  · exact n2cPiv26
  · exact n2cPiv27
  · exact n2cPiv28
  · exact n2cPiv29
  · exact n2cPiv30
  · exact n2cPiv31
  · exact n2cPiv32
  · exact n2cPiv33
  · exact n2cPiv34
  · exact n2cPiv35
  · exact n2cPiv36
  · exact n2cPiv37
  · exact n2cPiv38
  · exact n2cPiv39
  · exact n2cPiv40
  · exact n2cPiv41
  · exact n2cPiv42
  · exact n2cPiv43
  · exact n2cPiv44

/-! **N2c** — every position of the extracted corner runs is an `IsPiv` of the witness
corner (check_stair item 3, kernel-checked: the pivots are the extracted `pc`). -/
theorem stairCorner_pivots_witness :
    ∀ x ∈ runPairs stairCornerRuns45, IsPiv stairCornerQ x.1 x.2 := by
  intro x hx
  rw [stairCornerRuns45_mem] at hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact stairPivAt ⟨i, List.mem_range.mp hi⟩


/-! ## N2d — THE FRAME DELTA (the refutation of `isPiv_stair_lower` as scaffolded)

`isPiv_stair_lower` (above) concludes `IsPiv (qM M) p.1 p.2` for `p ∈ runPairs
(stairDataRuns 23 529)`, from the hypothesis `hdet` that the **staircase frame** corner
`stairCornerQOf M = Matrix.of (corStairQ M)` is invertible.

That statement is FALSE. Two independent reasons, both verified exactly:

1. **The corner of `qM M` is the r6 frame, not the staircase frame.** The platform lemma
   `qM_corner` (used verbatim by the accepted `data_edge` proof, nb_data_edge_solution.lean
   :537-539) identifies the top-right `45 × 45` corner of `qM M` with Defs4's `cor M`
   (`Lterms`/`Rterms`). `n2d_frame_delta` below pins the divergence decidably at entry
   (0,0) of the staircase witness: the r6 frame reads the matrix entry `(0,0),(1,0)`,
   the staircase frame the entry `(0,0),(1,3)`. At the witness these are
   `653217308241796875` and `-54722753962895109375`; `n2d_qm_corner_check.py` reproduces
   the actual corner of `qM stairMQ` from `Tm * M * Ti` with a concrete `flagEquiv`
   (2025/2025 entries = the r6 frame; 1528/2025 differ from the staircase frame).
   So the swap point "restate the corner identity with `cor → corStairQ`"
   (Signature.lean header, point 1, ":527-537") is unsound.

2. **The claimed pivots fail at the witness.** `n2d_refute.py` checks all five hypotheses
   of `isPiv_stair_lower` at the extracted witness labels (`extract/out/cert_data.json`):
   `y₁ ⬝ x₁ = 1`, `y₂ ⬝ x₂ = 1`, `hu = 9`, `hv = 28894092²`, all 21 `hT` values nonzero,
   and `hdet` holds (`stair_data_cert`, rank 45). The actual r6-frame corner has rank 44,
   and **18 of the 39 corner positions** asserted by `stairDataRuns 23 529` are *not*
   pivots — the failing positions are exactly the added staircase run `(25,486,18)`
   (corner coordinates `(i, i-23)`, `25 ≤ i ≤ 42`). The pre-existing r6 corner run
   `(1,507,21)` does hold in the r6 frame.

Consequence: the staircase frame is not the flag basis of Defs4's `qM`. A data edge with
runs `stairDataRuns 23 529` must be certified for the projector built from the STAIRCASE
design (`LtermsStair`/`RtermsStair`) — an R7-side definition that does not exist in this
skeleton (D2/QHNet territory) — not by swapping the corner inside r6's `data_edge`.
`stairCorner_pivots_witness` (N2c) remains true and useful: it is the witness-level pivot
fact for the staircase corner itself. -/

/-- Mirror entry formula for the staircase witness pair matrix. -/
lemma n2d_stairMQ_entry (a b c e : Fin 23) :
    stairMQ (a, b) (c, e) =
      ((if a = c then (1 : ℚ) else 0) - stairQX1 a * stairQY1 c) *
        ((if b = e then (1 : ℚ) else 0) - stairQX2 b * stairQY2 e) := by
  simp only [stairMQ, kronecker_apply, Matrix.sub_apply, vecMulVec_apply, Matrix.one_apply]

lemma n2d_Lterms_0 : Lterms (h := 19) 0 = [(1, ((0 : Fin 23), (0 : Fin 23)))] := by
  simp [Lterms]

lemma n2d_Rterms_0 : Rterms (h := 19) 0 = [(1, ((1 : Fin 23), (0 : Fin 23)))] := by
  simp [Rterms]

lemma n2d_LtermsStair_0 : LtermsStair 0 = [(1, ((0 : Fin 23), (0 : Fin 23)))] := by
  simp [LtermsStair, LtermsZStair]

lemma n2d_RtermsStair_0 : RtermsStair 0 = [(1, ((1 : Fin 23), (3 : Fin 23)))] := by
  simp [RtermsStair, RtermsZStair]

/-- The r6/Defs4 corner at (0,0) reads the matrix entry `(0,0),(1,0)` (label-free). -/
lemma n2d_cor_00 (M : Matrix (Pr 23) (Pr 23) ℚ) :
    cor (h := 19) M 0 0 = M ((0 : Fin 23), (0 : Fin 23)) ((1 : Fin 23), (0 : Fin 23)) := by
  simp [cor, n2d_Lterms_0, n2d_Rterms_0]

/-- The staircase corner at (0,0) reads the matrix entry `(0,0),(1,3)` (label-free). -/
lemma n2d_corStairQ_00 (M : Matrix (Pr 23) (Pr 23) ℚ) :
    corStairQ M 0 0 = M ((0 : Fin 23), (0 : Fin 23)) ((1 : Fin 23), (3 : Fin 23)) := by
  simp [corStairQ, n2d_LtermsStair_0, n2d_RtermsStair_0]

/-- **N2d frame delta** — the two frames read different matrix entries at (0,0), so
`corStairQ` can never replace `cor` in the `qM_corner` identity. At the staircase witness
the two corner entries are `653217308241796875` and `-54722753962895109375`. -/
theorem n2d_frame_delta :
    cor (h := 19) stairMQ 0 0 ≠ corStairQ stairMQ 0 0 := by
  rw [n2d_cor_00, n2d_corStairQ_00, n2d_stairMQ_entry, n2d_stairMQ_entry]
  norm_num [stairQX1, stairQY1, stairQX2, stairQY2, stairWX1L, stairWY1L, stairWX2L, stairWY2L,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, Fin.isValue, ↓reduceIte,
    Fin.mk.injEq]


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



end Stair

end StaircasePort
