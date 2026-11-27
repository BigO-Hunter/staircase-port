# N2b RESCUE + RESUME (2026-11-05/06)

## WHAT HAPPENED
Host restarts (3+) wiped the scratch workspace: the N2b worktree, the base repo
(commit 3797328, "N2a PROVED"), the jainroot producer-chain copy, and the proven
.lake/Mathlib oleans (11G). No local snapshots. Base commit 3797328 was not found
anywhere else on disk. The 5 commits made in the clone (extract scripts, regenerated
NEBlocks.lean, green probes) died with it — never pushed. This directory is the durable
rescue package, rebuilt from session context. LESSON: scratch-location clones are NOT
durable state across host restarts; workspaces must live in durable storage or push to
a remote.

## STATUS: PARTIAL (phases 1+2 done-and-verified pre-wipe; phase 3 in progress)
- Phase 1 EXTRACTION: DONE, verified. check_stair.py 23 reran certified=True on this
  machine (runs [21,18,1^6], 689 blocks, above=0). Scratch clone of cut_bound returning
  (flow,R0,T0,C0): **689/689 flows reproduce the pinned cut values** AND the producer's
  own cut_bound AND |R0|+|T0|+|C0| = flow. Structure facts: T0 = {46} (400 blocks) or
  {23,46} (289 blocks); |R0| ≤ 35, |C0| ≤ 20; sr/sc supports ≤ 4 elems except term 46
  (= all 45). sr/sc derived-from-cells == structure() terms: verified True.
- Phase 2 NEBLOCKS REGEN: DONE, verified GREEN pre-wipe (lake build StaircasePort,
  "Build completed successfully (8997 jobs)"; commit 1d8e8d7 in the lost clone).
  Final form (v2, getD-based pins — regenerated but NOT yet built when wiped):
  adds stairNECutR0/C0/T0 : List (List ℕ) (689 ea, sorted distinct, zip-aligned with
  stairNEBlocks), stairNESr/Sc : List (List ℕ) (47 ea), length pins (rfl),
  stairNE_cuts_card (bulk kernel `decide`: Finset.univ.filter-cards of the pinned lists
  = column-4 cut value + i<45 + j<45), stairNE_cuts_cover (bulk kernel `decide`:
  ∀ t ∈ range 47, t ∉ T0L(n) → (∀ r ∈ srL[t], r ≤ i(n) → r ∈ R0L(n)) ∨ (∀ c ∈ scL[t],
  j(n) ≤ c → c ∈ C0L(n))). NO native_decide anywhere. Both set_options:
  maxRecDepth 20000 + maxHeartbeats 0 (v1 cover pin hit the 200k-heartbeat default;
  with 0 it passed in the 8997-job build). v1 (zip-based) built GREEN; v2 (getD-based)
  is the rebuild script's output — same decide scale, expected green, MUST rebuild.
- Phase 3 PROOF: in progress at wipe. P1+P2 probe GREEN (verified by execution,
  pre-rework); Nat-indexing rework + P3-part1 (summand_normal) written, NOT re-run.
  Full probe text: n2b_full.lean in this dir. P3-part2/P4 blueprints below.

## THE STATEMENT-SHAPE FINDING (critical, must go into rebuilt Pivot.lean)
The scaffolded stairNE_rk_le (∀ M : Matrix (Pr 23) (Pr 23) ℚ, ...) is **FALSE for
arbitrary M**: counterexample at block (1,24) (cut=1): corner row 0 reads only M-cells
((0,0),·), row 1 only ((1,1),·) — pick M with M[(0,0)][(2,3)]=1/a₂, M[(1,1)][(3,4)]=1/a₃,
rest 0 → block has 2×2 identity minor → rank 2 > 1 = cut. The bound holds identically
in the LABELS when M is a pair matrix. Honest N2b (matches N2d's consumption shape,
cf. its hdet):
```lean
theorem stairNE_rk_le (x₁ y₁ x₂ y₂ : Fin 23 → ℚ) :
    ∀ t ∈ stairNEBlocks,
      rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (t.1 + 1) t.2.1 ≤ t.2.2.2
-- stairPairM x₁ y₁ x₂ y₂ := (1 - vecMulVec x₁ y₁) ⊗ₖ (1 - vecMulVec x₂ y₂)
```

## THE MATH (verified on paper; drives the Lean)
Kronecker expansion q1[a][a']·q2[b][b'] = (δ_{aa'} − x₁[a]y₁[a'])(δ_{bb'} − x₂[b]y₂[b'])
splits corStairQ into 4 pieces; the diagonal piece vanishes identically (L-cells ∩
R-cells = ∅ — Python-verified 0 overlaps; Lean pin stairLR_disjoint_pin); the other
three are exactly the 47 structure() terms, EACH A vecMulVec (rank ≤ 1):
- l-group term t<23 (shared second coord l): −U_l(i)·V_l(j),
  U_l i = Σ_{s∈L i, (s.2.2:ℕ)=l} s.1·x₁(s.2.1); V_l j = Σ_{t∈R j, snd=l} t.1·y₁(t.2.1)
- k-group term 23≤t<46 (shared first coord k=t−23): −U'_k(i)·V'_k(j) (x₂/y₂, fst)
- whole term t=46: P(i)·Q(j), P i = Σ_s s.1·x₁(s.2.1)·x₂(s.2.2), Q j = Σ_t t.1·y₁(t.2.1)·y₂(t.2.2)
Support: term-l matrix vanishes on row-group i iff l ∉ snd-coords(L i) (stairLsndN),
matching sr_t/sc_t of structure() — pinned raw as stairNESr/Sc, tied to the Lean family
defs by coherence pins stairNESr_coh/Sc_coh (decide, disjunctive form). hcut then chains:
cover pin → r ∉ srL[t] → coherence → coordinate absent → factor sum = 0 (vanishing
lemmas) → row/col of Mt t = 0. Whole-term t=46: sr = all rows, so the row-side cover
gives contradiction with r ∉ R0 — handled uniformly. hrank1: every Mt is vecMulVec →
Matrix.rank_vecMulVec_le; block level via submatrix_vecMulVec (submatrix of vecMulVec
= vecMulVec of composites). hsum: master identity + entrywise Matrix.sum_apply;
NO rw under Matrix transparency (N2a landmine) — ext to entries first.

## MATHLIB d13f23b7 NAMES (probe-verified pre-wipe)
Matrix.kroneckerMap_apply (⊗ₖ = kroneckerMap (·*·), Kronecker.lean:278 scoped infixl:100)
Matrix.vecMulVec_apply (Mul.lean:620), Matrix.rank_vecMulVec_le (Rank.lean:198),
Matrix.sum_apply (Basic.lean:71), Fintype.sum_ite_eq (i) (f) : ∑ j, (if i=j then f j else 0) = f i
(NOT Finset.sum_ite_eq — that one takes (s : Finset ι) first!),
Finset.sum_add_distrib : ∑(f+g) = ∑f + ∑g (forward; ← direction is the merge),
Fin.sum_univ_eq_sum_range (f : ℕ → α) (n) : ∑ i : Fin n, f ↑i = ∑ i ∈ range n, f i
(LHS needs the LITERAL coercion ↑i — make summands ℕ-indexed so unification fires!),
Finset.sum_range_add_sum_Ico (f) (h : m ≤ n), Finset.sum_Ico_eq_sum_range (f) (m n)
(= ∑ range (n−m), f (m+k)), Finset.sum_range_one, Finset.sum_neg_distrib,
List.all_eq_true, List.getD_eq_get, List.get_mem, List.mem_iff_getElem, List.length_zip,
List.getD_nil/getD_cons_zero/getD_cons_succ, Finset.mem_filter. NO List.map_congr
(unknown constant — use `congr 1; funext s; split_ifs <;> ring` then the equation).
Decidable.eq_true is UNKNOWN on v4.34.1 — use of_decide_eq_true. push_neg deprecated →
push Not. Landmine CONFIRMED: induction inside a proof drags hypotheses mentioning the
inducted var into generalized implications (outer ih mentioned lL) — avoid nested
induction; factor via standalone lemmas.

## PROBE STATUS (n2b_full.lean in this dir)
GREEN-VERIFIED (pre-rework, Fin-23-indexed factor sums): List.sum_map_add,
List.sum_map_mul_right, List.sum_map_ite_eq_zero (γ-generic), List.sum_sum_ite_eq_group
(regrouping — the algebraic heart), List.sum_sum_mul (product-of-sums),
stairLR_disjoint_pin + mem_stairLcellN/RcellN + stairLR_disjoint, stairNESr_coh/Sc_coh
(both kernel decide, FAST), vanishing lemmas. Reworked to Nat-indexed factor sums
(matches the pin data form; drops the not_mem_map_coord bridge) + added stairTermN/Row/
Col/M, stairTermM_apply, stairTermM_rank_le, submatrix_vecMulVec, P3-part1
(List.sum_map_neg, List.sum_map_const_zero, mul_ite_one, summand_normal):
WRITTEN, NOT RE-RUN — first job on rebuild is `lake env lean n2b_full.lean`.

## REMAINING WORK (blueprints; all mechanics decided)
1. rebuild_all.py (this dir) regenerates NEBlocks.lean (value pins reconstructed from
   the documented pc runs — pc[0]=44, pc[1..21]=23..43, pc[22]=22, pc[23]=21, pc[24]=20,
   pc[25..42]=2..19, pc[43]=1, pc[44]=0; rho[i][j]=#{r≤i: pc[r]≥j}; nontrivial =
   rho≠min(i+1,45−j); MUST come out 689 with spot tuples (1,24,1,1),(20,24,20,20),
   (25,3,25,25),(41,19,25,25)) + the cut-set sections. NEEDS a rebuilt base project
   (Definitions closure + .lake) to build against.
2. P3-part2 in n2b_full.lean: List.sum_map_eq_zero (∀ x∈l, f x=0 → (l.map f).sum=0, by
   induction; for piece A); regroup23 (List.sum_sum_ite_eq_group + per-factor Fin↔Nat
   condition bridge via `have heq : (k₁ s = c) ↔ ((k₁ s : ℕ) = (c : ℕ)) := ⟨congrArg _,
   Fin.val_inj.mp⟩; rw [heq]` + Fin.sum_univ_eq_sum_range forward — ℕ-indexed summands
   make it fire); corStairQ_stairPairM_sumN (a b : ℕ, a<45, b<45): h1 (unfold corStairQ;
   congr 1; funext t; rw [← List.sum_map_mul_right]; congr 1; funext s; summand_normal)
   → h2 (simp only [List.sum_map_add, List.sum_map_sub] inner ∀t then outer) → hA
   (sum_map_eq_zero + stairLR_disjoint via List.mem_map witnesses) → hB/hC (regroup23,
   keys (·.2.1)/(·.2.2), then simp only [stairUk, stairVk]/[stairUl, stairVl]) → hD
   (List.sum_sum_mul; simp only [stairPw, stairQw]) → hR (range-47 split:
   ←sum_range_add_sum_Ico 23≤47, sum_Ico_eq_sum_range, ←sum_range_add_sum_Ico 23≤24,
   sum_Ico_eq_sum_range, sum_range_one; pointwise: if_pos (mem_range.mp hx);
   if_neg/if_pos + Nat.add_sub_cancel_left for 23+x; if_neg decide ×2 for 46;
   sum_neg_distrib ×2; abel) → final: rw [h1,h2,hA,hB,hC,hD,hR]; ring.
3. P4 assembly (Pivot.lean): stairBlockR0/C0/T0 (n : ℕ) := univ.filter ((·:ℕ) ∈ getD n []);
   stairBlockTerms x X Y t := (stairTermM x t).submatrix Subtype.val Subtype.val;
   stairCornerQOf_block_sum (ext r c; submatrix_apply/sum_apply; corStairQ_stairPairM_sumN
   at r.1.val/c.1.val with Fin.isLt bounds; RHS bridge: ptw ∀ t, stairTermM t r.1 c.1 =
   stairTermN (t:ℕ) ... via stairTermM_apply + rfl, then `show ∑ t, (fun n => ...) (t:ℕ)`
   + Fin.sum_univ_eq_sum_range); getD_eq_getElem_of_lt helper (induction on l/i,
   List.getD_cons_succ + List.getElem_cons_succ, zero case rfl);
   stairNE_rk_le_block (n : Fin 689): pins via List.all_eq_true.mp pin n.val
   (List.mem_range.mpr n.isLt) + of_decide_eq_true; hsum := block_sum; hrank1: intro t _;
   rw [stairBlockTerms, submatrix_vecMulVec] (after `simp only [stairTermM]` if needed);
   exact Matrix.rank_vecMulVec_le _ _; hcut: intro t ht; simpa [stairBlockT0,
   Finset.mem_filter] using ht → (t:ℕ) ∉ T0L; hcover at t; coherence pins at (t.val,
   r.1.val) → hnotsr : r.val ∉ srL[t]; by_cases t.val<23 → stairUl_eq_zero (contradict
   hnotsr.1 ⟨h23, hs⟩) → funext c; rw [stairBlockTerms, Matrix.submatrix_apply,
   stairTermM_apply, stairTermN, if_pos h23, hv]; ring; elif t.val<46 → stairUk_eq_zero
   via hnotsr.2.1 ⟨by omega, h46, hs⟩ + if_neg/if_pos + (t.val−23); else exfalso
   hnotsr.2.2 (by omega : 46 ≤ t.val); col side symmetric (stairNESc_coh, RsndN/RfstN,
   stairVl_eq_zero/stairVk_eq_zero, goal ∀ r, Mt t r c = 0 — Col factor = 0 → ring);
   hcard: pin card-eq → le_of_eq; concl: le_trans (rank_le_support_cut _ (i+1) j R₀ C₀ T₀
   (stairBlockTerms x (i+1) j) hsum hcut hrank1) hcardLE;
   stairNE_rk_le: intro t ht; obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp ht;
   have := stairNE_rk_le_block x ⟨n, stairNEBlocks_length ▸ hn⟩; rw [← hgetD-bridge] —
   bridge: getD_eq_getElem_of_lt stairNEBlocks (0,0,0,0) n hn = t; exact this.
4. #print axioms on everything (target [propext, Classical.choice, Quot.sound]; the two
   NEBlocks bulk pins: propext+decide internals only; NO native_decide, NO sorry).
5. Replace the scaffold sorry for stairNE_rk_le with the proved version + SHAPE NOTE
   docstring (entry: arbitrary-M version false, counterexample above; pair-matrix form
   is what N2d consumes).
6. Append "## N2b NOTES" to SCAFFOLD.md (statement-shape finding + pin inventory).
7. If context remains: N2c (stairCorner_pivots_witness) per its docstring route.

## FILES IN THIS RESCUE DIR
- RESUME.md (this)
- n2b_full.lean — P1+P2(reworked)+P3-part1 probe, import StaircasePort.Pivot
- vendored_check_stair_core.py — design()/structure()/cut_bound() verbatim from
  jainroot check_stair.py (reconstructed from session context; the ONLY copy — original
  was at leaf-recon/jainroot/independent/deferred-readout/check_stair.py, wiped)
- rebuild_all.py — regenerates ne_cuts.json + NEBlocks.lean fully (run it; asserts 689)
- SCAFFOLD_reconstructed.md — full pre-wipe SCAFFOLD.md incl. N3/N4/N2a notes (verbatim
  from session context) — the base repo's soul doc; ALSO LOST elsewhere
- NEBlocks.lean, ne_cuts.json — generated outputs (after rebuild_all.py run)
