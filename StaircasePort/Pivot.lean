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


/-- **N2c** — check_stair item 3 instantiated at the extracted witness: the rightmost-pivot
pattern pc = [(0,44),(1,23..43) 21-run,(22,22),(23,21),(24,20),(25,2..19) 18-run,(43,1),
(44,0)] (staircase_data.json pc/runs_offsets) makes every position of stairCornerRuns45 an
IsPiv of the witness corner. Route: rho-profile identity (rk (i+1) j = #{r ≤ i | pc_r ≥ j},
check_stair.py:176) from N2b upper bounds + invertibility (stair_data_cert, N3) + the
rightmost-pivot computation at the concrete witness (decide/native_decide on the extracted
45×45 integer matrix mod stairCertP, or reflective-kernel certificate à la R6ChkPack). -/
theorem stairCorner_pivots_witness :
    ∀ x ∈ runPairs stairCornerRuns45, IsPiv stairCornerQ x.1 x.2 := by sorry

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
(nb_flag_gen_solution.lean:977-993; nonvanishing factors = N4 + hdet). -/
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


end Stair

end StaircasePort
