/-!
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
        · exact (memSrow.mp h2).1
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
      (fun r hr => Finset.sum_eq_zero fun t ht => (memSrow.mp ht).2 r hr)
  have hQ : (∑ t ∈ Scol, M t).rank ≤ C₀.card :=
    RankKit.rank_le_card_col_support C₀ Subtype.val Subtype.val_injective _
      (fun c hc r => by
        rw [Finset.sum_apply, Finset.sum_apply]
        exact Finset.sum_eq_zero fun t ht => by
        have htS : t ∈ Sc \ Srow := ht
        have htSc : t ∈ Sc := (Finset.mem_sdiff.mp htS).1
        have htSrow : t ∉ Srow := (Finset.mem_sdiff.mp htS).2
        have htT : t ∉ T₀ := (Finset.mem_sdiff.mp htSc).2
        rcases hcut t htT with hrow | hcol
        · exact absurd (memSrow.mpr ⟨htSc, hrow⟩) htSrow
        · exact hcol c hc r)
  calc ((∑ t ∈ T₀, M t) + (∑ t ∈ Srow, M t + ∑ t ∈ Scol, M t)).rank
      ≤ (∑ t ∈ T₀, M t).rank + (∑ t ∈ Srow, M t + ∑ t ∈ Scol, M t).rank :=
        RankKit.rank_add_le _ _
    _ ≤ (∑ t ∈ T₀, M t).rank + ((∑ t ∈ Srow, M t).rank + (∑ t ∈ Scol, M t).rank) :=
        add_le_add le_rfl (RankKit.rank_add_le _ _)
    _ ≤ R₀.card + C₀.card + T₀.card := by omega

/-- **N2b** — check_stair item 2 instantiated: for EVERY pair matrix M (the bound holds
"identically in all parameters", check_stair.py:11), each of the 689 extracted nontrivial
NE blocks of the symbolic staircase corner satisfies rk(rows ≤ i, cols ≥ j) ≤ its min-cut
value (stairNEBlocks t = (i, j, rho_ij, cut_ij); evaluated rho at the witness in column 3,
bound in column 4). Route: rank_le_support_cut with the rows/terms/cols graph of
check_stair.structure (:42-54) — the supports come from LtermsStair/RtermsStair cell
patterns, terms from the shared-parameter groups (l-index/k-index cells, :49-52). -/
theorem stairNE_rk_le (M : Matrix (Pr 23) (Pr 23) ℚ) :
    ∀ t ∈ stairNEBlocks, rk (stairCornerQOf M) (t.1 + 1) t.2.1 ≤ t.2.2.2 := by sorry

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

end Stair

end StaircasePort
