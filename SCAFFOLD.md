# SCAFFOLD.md — staircase witness-1 Lean port skeleton (r7 leaf e27d1a90, bounded first increment)

Date: 2026-11-04. Skeleton only: definitions + sorry'd statements + extracted data.
Every statement elaborates against the REAL platform definitions (Defs4 closure below).

## Environment
- Toolchain v4.34.1 + Mathlib d13f23b7 (project copied from the intmult-sol development, its
  `.lake` cache cloned; intmult-sol itself untouched).
- `Definitions/` = exact 64-file import closure of `Def_IntMul_Kappa_R6_Defs4` (source:
  the platform Definitions workspace, bodies identical to intmult-sol's migrated copies —
  only provenance headers differ) + `Def_IntMul_KappaJainData`. Built GREEN on v4.34.1:
  `build_defs.log` "Build completed successfully (8987 jobs)", 0 errors. This validates the
  whole r6 vocabulary (QHNet, Edge, EdgeQ, rk, IsPiv, RunOK, runPairs, runPiv, pswQ, qM,
  cor/corZ, certChk, dataRuns, DataE/AuxE/SideE, MZ, certRows/certCols) on the dev toolchain.
- Build: `lake build StaircasePort` (lib root `StaircasePort.lean`; there is no
  `Definitions.lean` root module — build leaf targets like
  `lake build Definitions.Def_IntMul_Kappa_R6_Defs4` or the StaircasePort root, never bare
  `lake build Definitions`).

## Extraction (all exact ints/Fractions, stdlib-only, rerunnable)
| script | output | content |
|---|---|---|
| extract/fetch_statements.py | extract/statements/pivot_statements.{json,lean} | verbatim formal_statements: isPiv_rank1_lower (e90110dd), isPiv_mid (06f02169), edge_of_pivs (f66c9619), isPiv_side (ef7049d3) — all Proved |
| extract/extract_T.py | extract/out/T_data.json | **T = 3217907 RESOLVED** = 46v+N, v=C(23,3)=1771, N=v²=3136441 (h=23 unchanged from r6; only R=28866 and W=2N+2vR=108516254 change). Cross-checks: s=57403754177, Σn_w=1905413587, all from frozen witness_23/deferred_23.json.gz |
| extract/extract_staircase.py | extract/out/staircase_data.json | (a) dominant pc, runs+offsets [(0,44,1),(1,23,21),(22,22,1),(23,21,1),(24,20,1),(25,2,18),(43,1,1),(44,0,1)]; dataRuns' = [(45,45,439),(1,507,21),(25,486,18)]; rs'.length=6; 689 NE blocks (i,j,rho,cut), cut≥rho on all; (c) 45×45 corner + 45×23 B block at witness; (d) middle-run (45,45,439) confirmation incl. disjointness; --ij control: identical pc, certified |
| extract/extract_cert.py | extract/out/cert_data.json | N3 data: ℤ labels x₁=p,y₁=ξ,x₂=v,y₂=ν with y⬝x=1 EXACT over ℤ (extended-Euclid lift of the --ij witness, values mod P untouched), family coeffs (al,be,a[],b[] lifted from [1,P)), 45×45 ℤ corner (≤36 digits), det≠0 mod 67108859, certRows/certCols with rows·cols=1 verified (r6 certChk convention) |
| extract/gen_lean_data.py | StaircasePort/CertData.lean, StaircasePort/NEBlocks.lean | generated Lean data (exact ints only) |

Producer chain copy: extract/jainroot/ (check_stair.py + linalg/check_lifted/deferred/
certificate_round7 @ c05adfe, from the producer recon copy — jain-verify NOT touched).

## N-item map
| N | file | statements | depends on |
|---|---|---|---|
| N1 | StaircasePort/Data.lean | stairCornerRuns/stairDataRuns/stairSingles/stairCornerRuns45, **DataE'** (rs'.length 6, not h+5=24), pins stairDataRuns_eval/_delta (rfl), stair_pivot_budget, stairRunOK, stairNodup (native_decide — NO sorry), stairT/stairW | Defs4 |
| N2 | StaircasePort/Pivot.lean | Platform restatements (4, verbatim) + **rank_le_support_cut** (N2a generic), **stairNE_rk_le** (N2b, 689-block table), **stairCorner_pivots_witness** (N2c), **isPiv_stair_lower** (N2d master, generalizes isPiv_rank1_lower) | N1, N3 (labels/corner), NEBlocks |
| N3 | StaircasePort/Cert.lean (+ generated CertData.lean) | LtermsZStair/RtermsZStair/corZStair/corStairQ/stairMZ/stairMQ/stairCornerQOf/stairCornerQ; stairQxy1/2, stairMZ_map, stair_cert_chk, stair_cert_entries, **stair_data_cert** (det ≠ 0, mirrors nb_flagBasis_solution.lean:97-147) | CertData only |
| N4 | StaircasePort/Nonvan.lean | stairF1..F4 defs (explicit --ij line algebra), **stair_f_nonvanishing** (f1..f4 every line + inner corners), **stair_hu/stair_hv/stair_hT** at witness labels (all verified numerically TRUE by gen_lean_data.py) | CertData only |
| N5 | StaircasePort/Signature.lean | **data_edge_stair** (DataE' conclusion, hpiv = N2d), **flagBasis_stair** (verbatim flagBasis_sol_aux signature, DataE→DataE'); header comment lists ALL swap points (data_edge :503-517/:536-552/:554-555, flag_gen :1049, flagBasis :196-198, accepted_bitNetR6_mom :2289/:2291/:2323-2325/:2353/:2539) | N1, N3, N2d |
| Top | StaircasePort/Top.lean | **staircase_bitNetR7_mom** (BitNetMomStmtG 108516254 529 Jain.bitR7 unfolded verbatim, RG_Defs:31-34), stair_hist_target/stair_ranksum_target (native_decide, no sorry) | N1 |

## Fan-out independence & recommended proving order
Independent (claimable in parallel, no cross-deps): **N3**, **N4**, **N2a**, **N5-1
(data_edge_stair assembly, given N2d as hyp)**.
Chain: N2a → N2b → N2c (needs N3 witness + stair_data_cert) → N2d (needs Platform.isPiv_mid
+ isPiv_block port) → N5-2 (flagBasis_stair, needs N3+N5-1).
Recommended order: N4 (hours) ∥ N3 (days, mechanical — r6 proofs port verbatim) ∥ N2a
(generic toolkit, days) → N2b → N5-1 → N2c → N2d → N5-2 → then OUTSIDE this skeleton:
D2 dataset regen (R=28866, pre-verify offline — the plain line died on defective frozen
data), QHNet construction (T confirmation lives there), RunsOK/EdgesOK (generic
edgesOK_large_of_edgeQ route, REPORT §6), FormalOK assembly (good_primes pattern), D3
moment equality (trivial, pins already proved here).

## N2 proof-route summary (per plan)
NE-rank UPPER bound via row/col/term-support factorization (rank_le_support_cut) using
data_edge's rank toolkit — rank_eq_of_range_rows/cols (nb_data_edge_solution.lean:26-30)
and rank_submatrix_range (:83), both PROVED with full proofs in the fetched body — plus
RIGHTMOST-PIVOT LOWER bound at the extracted witness (N2c). The min-cut computation stays
offline: cut VALUES are extracted data (stairNEBlocks), each re-checkable against
check_stair.cut_bound. Informal certificate: check_stair.py 23 → `certified=True` on this
machine (runs [21,18,1⁶], 689 blocks, invertible, single pivot pattern over 20 pairs) with
DISCRIMINATING negative control (--control: certified=False, 3 rank violations).
**Fallback if support-factorization fails: formalize the max-flow bound (+weeks).**

## Statement/build fixes made during scaffolding (build-driven; the scaffold's job)
1. **NEW GOTCHA (v4.34.1): a leading `/-! ... -/` module doc-comment BEFORE the imports is a
   PARSE ERROR** ("invalid 'import' command, it must be used in the beginning of the file") —
   minimal repro confirmed. File headers must use plain `/- -/`; `/-!` blocks are fine AFTER
   imports (Mathlib + the platform bodies use exactly that order). Applied to all 7 files.
2. `set_option maxRecDepth 20000` required for the big literals (689-tuple NEBlocks list,
   45×45 certRows/certCols) — default depth fails at parse ("maximum recursion depth").
   Baked into gen_lean_data.py's templates.
3. `stairRunOK`: `decide` cannot synthesize `Decidable (∀ ρ ∈ l, RunOK 529 ρ)` through the
   opaque `RunOK` def — route: simp the membership to equalities, `rcases` with the NESTED
   pattern `(rfl|rfl|rfl)|rfl|...` (List.mem_append leaves a nested Or group; mem_cons
   orientation is `ρ = t`), then `unfold RunOK; decide` per literal.
4. `stairT_eq`/`stairW_eq`: `norm_num` does not unfold the defs → `rfl` (closed numerals).
5. `flagBasis_stair`: explicit `(h := 19)` on the DataE' clause (h not inferable from
   Fin 529 by unification — the r6 original likewise writes `AuxE (h := 19)`).
6. N2b bound reads the CUT column `t.2.2.2` of stairNEBlocks tuples (i,j,rho,cut); the
   generated self-check asserts cut ≥ rho (`t.2.2.2 ≥ t.2.2.1`).
7. Pivot.lean needs `open scoped Kronecker` for `⊗ₖ` (scoped notation; "expected token").

## Build status (GREEN)
- `lake build Definitions.Def_IntMul_Kappa_R6_Defs4 ...` → build_defs.log: "Build completed
  successfully (8987 jobs)", 0 errors — the full r6 vocabulary compiles on v4.34.1/d13f23b7.
- `lake build StaircasePort` → build_scaffold.log: "Build completed successfully (8997
  jobs)", 0 errors; only `declaration uses sorry` warnings (expected for a skeleton).
- axcheck.lean (`lake env lean axcheck.lean`) prints the axiom profiles: sorryAx appears
  EXACTLY on the sorry'd statements; stairRunOK [propext], stairDataRuns_delta [no axioms],
  stairT_eq [propext]; the native_decide pins carry only their native_decide axioms
  (standard; if a submission gate forbids native_decide, downgrade to `decide` — slower but
  kernel-checked).

## GAPs (nothing below is guessed; each is flagged where consumed)
1. T=3217907 resolved structurally (46v+N; h=23, v, N all recomputed from frozen JSON) but
   the τ-addressing itself lives in the Lean QHNet construction (Defs), not the JSON —
   final confirmation = the net definition (D2). Data.lean stairT docstring carries this.
2. DataE''s rs' singletons come from edge_of_pivs' construction; the extracted stairSingles
   positions are informational (length 6 is forced by the rank count; positions not claimed).
3. Exact extra nonvanishing factors for the staircase deviation steps (RC/CC cells beyond
   hu/hv/hT) = N2 proof work; flag_gen's Pall product (nb_flag_gen_solution.lean:977-988)
   absorbs them structurally. N4 states the verified f1..f4/inner-corner/hu/hv/hT set.
4. N2b is stated at the flag-basis corner (stairCornerQOf M); the corner-transfer identity
   (hCe: Cp i j = cor M i j restated with corStairQ, nb_data_edge_solution.lean:534-537)
   and isPiv_block (PROVED at :227-238) are inside N2d's route, not separately stated.
5. Platform bodies of isPiv_mid/edge_of_pivs/isPiv_side not fetched (statements verbatim
   from search; bodies platform-side). At submission, Platform.* sorries → imports of the
   Proved children (ids in Pivot.lean header).
6. flag_gen' (the internal generic consumer of data_edge_stair) is NOT restated;
   flagBasis_stair states the consumed signature directly. The fetched 1071-line flag_gen
   body ports with the single :1049 call swap.
7. stair_cert_entries `decide +kernel` load: 36-digit ℤ entries vs r6's small ints — if the
   kernel balks, re-search a small-integer witness (Zariski-open ⇒ exists; not done here).
8. RG_Defs (BitNetMomStmtG) not imported — would pull 13 more R6 Defs files; Top.lean
   unfolds the def body verbatim instead (checked line-by-line against the fetched source).
9. Dataset regen (D2: recChk/dimAll/nestOK analogues for R=28866) is out of skeleton scope
   by design — it is mechanical and must be Python-pre-verified first (REPORT.md lesson).

## Gotchas honored (banked)
- No dangling `/--` doc-comments (parse error) — prose uses `/-!` (after imports) or `/- -/`
  file headers; every `/--` is attached to a declaration.
- Bare `end` for unnamed sections; no `end noncomputable section` anywhere.
- All builds detached (nohup + log): build_defs.log, build_scaffold.log.
## N4 NOTES (2026-11-04)
- N4 PROVED: stair_f_nonvanishing + stair_hu/hv/hT, axioms [propext, Classical.choice,
  Quot.sound], NO native_decide, zero sorry in Nonvan.lean. Same-file helpers: stairTv_mem,
  stairG_val, stairA/C/B/D_ne_zero, stairCoeffA/B_ne_zero ([propext, Quot.sound]).
- Statement delta (cosmetic only): binder `ht` renamed `_ht` in stair_f_nonvanishing.
  Nonvanishing is cardinality-free (tv in {0,1} for ANY t); hyp kept, unused. Pass positionally.
- LANDMINE (for N3 cert_entries decide+kernel and N2 tables): `decide` STICKS on Q `*`/`+`
  here (whnf won't unfold mkRat/Rat.add gcd-normalization: "reduction got stuck at ...add...").
  decide DOES work for pure getD -> Int.cast -> decEq literal checks (no arithmetic) --
  interval_cases + decide route used for the 22-entry coeff lists.
- For Q-arithmetic nonzeroness: `simp [accessor defs, LIST defs]` -- BOTH must be passed
  (simp won't unfold stairWX1L etc. otherwise; getD stays stuck at `l[i]?`), then `norm_num`
  fallback (simp arith leaves forms like `!1+3 = 0`). hu/hv closed by simp alone.
- Benign warnings left in place (2x unnecessarySeqFocus, 2x never-executed norm_num) --
  file is green; not worth a re-verification cycle.
## N3 RESUME (2026-11-04) — STATUS: PROVED, item COMPLETE
Stopping point: ALL six N3 statements proved in StaircasePort/Cert.lean, zero sorry in the
file; `lake build StaircasePort` GREEN (8997 jobs); commit e91cda8 (+ final axcheck commit).
stair_data_cert axioms: [propext, Classical.choice, Quot.sound] — kernel-checked, no
native_decide, no sorryAx (n3_axcheck.lean prints all 6 + 3 ported helpers).

GAP-7 TIMING (decide +kernel; wall via /usr/bin/time -l; baseline import ≈60s wall):
| stage | content | wall | CPU(u+s) | axioms |
|---|---|---|---|---|
| t0 | native_decide sanity: all props TRUE (dots, worst entry, all 2025, certChk) | 89s | 17s | VM (test-only) |
| t1 | kernel, single worst entry (22,23) 36-digit | 64s | 11s | propext,Quot.sound |
| t4 | kernel, full certChk (2025 Nat dotL) | 68s | 14s | propext |
| t2 | kernel, worst row (22, 45 entries) | 62s | 12s | propext,Quot.sound |
| FINAL | lake build StaircasePort incl. real stair_cert_entries (all 2025) | 176s | 49s | — |
Verdict: GAP-7 outcome (a) — kernel decide FEASIBLE at 36-digit scale; per-entry marginal
kernel cost ≈ negligible (1 entry ≈ 1 row ≈ full build minus baseline); NO native_decide
fallback used, NO small-integer witness re-search needed (GAP 7 fallback can be struck).

What failed: nothing on the proof side — every port elaborated and kernel-checked on first
build. One env gotcha: nohup'd `lake env` needs `export LEAN_TOOLCHAIN=$(cat lean-toolchain)`
(transient elan "no default toolchain" otherwise).

Files: StaircasePort/Cert.lean (proofs; generic lemmas dotL_eq/certChk_sound/
det_ne_zero_of_certChk ported verbatim from nb_flagBasis_solution.lean:46-93; corStairQ_cast
= cor_cast analogue, no Lterms_eq step needed). CertData.lean UNCHANGED. New: n3_t0_native.lean
n3_t1_kernel_entry.lean n3_t2_kernel_row.lean n3_t4_kernel_chk.lean n3_axcheck.lean
extract/n3_corner_stats.py. No shared-file change requests.
Next for successors: N2c (stairCorner_pivots_witness) and N5-2 flagBasis_stair hcert can now
consume stair_data_cert; nothing blocked on N3.
## N52 RESUME (2026-11-05) — STATUS: PROVED, item COMPLETE

`StaircasePort.Stair.flagBasis_stair` (Signature.lean:1525) is PROVED with its statement
UNCHANGED. `lake build StaircasePort` GREEN (8997 jobs). Axioms:
`[propext, sorryAx, Classical.choice, Quot.sound]` — the only road to sorryAx is four
documented stubs (below); no `native_decide`, no `axiom`, no `admit`. The N5-2 machinery
(`corStairR`/`pDatStair`/`eval_pDatStair_of`/`pDatStair_ne`) is axiom-CLEAN
(`[propext, Classical.choice, Quot.sound]`).

### What was actually needed (the scaffold's route was INCOMPLETE)
The plan ("port flag_gen, swap only the :1049 data_edge call") does not close, and the reason
is a FRAME discovery, not a proof gap:

* `flag_gen`'s Pall corner factor is `pDat` (Defs4:1497), which encodes the r6/Defs4 `cor`
  frame (`Lterms`/`Rterms`, Defs4:834-949).
* At the STAIRCASE witness (CertData's `stairWX1L..stairWY2L`) that frame's 45x45 corner is
  **SINGULAR**: det = 0 exactly (0 mod 2^31-1, 67108859, 1000003, 998244353), rank 44.
  `scratch_corner_check2.py` validates the implementation two ways: it reproduces Defs4's r6
  `certRows` EXACTLY (0/2025 mismatches at the r6 witness) and reproduces CertData's
  `stairCertRows` structure; the r6 witness is invertible in the r6 frame (as `data_cert` says)
  and the staircase witness is invertible in the STAIRCASE frame (N3's `stair_data_cert`).
  => `pDat`'s hcert cannot be instantiated at the staircase witness. The corner factor must be
  rebuilt in the staircase frame: `pDatStair` (Signature.lean, `corStairR` =
  coefficient-ring-generic `corStairQ`), whose witness nonvanishing is exactly `stair_data_cert`.
* Consequence for N2d: `isPiv_stair_lower`'s `hdet` is `stairCornerQOf` (staircase frame) and
  the flag_gen Pall machinery can now produce exactly that (`eval_pDatStair_of`). Whoever
  discharges N2d must NOT assume `corStairQ = cor`; the two frames are genuinely different
  (random-label sampling finds points where the r6 frame is singular and the staircase frame is
  not — `scratch_corner_check2.py`'s sample loop).
* The `(h := 19)` / `Fin (19 + 4)` convention in the target statement is CORRECT: verified
  against the fetched r6 bodies (`nb_flagBasis_solution.lean:184-198` writes `DataE (h := 19)`
  with `Fin (19 + 4)`). No statement change was made or needed.

### Files / artifacts (all committed)
* `ref/nb_{flagBasis,flag_gen,data_edge,aux_edge_of,side_edge_of,idem_similar}_solution.lean` —
  re-fetched platform bodies (subs dc203a4d, 3a50ac98, d536680e, c2aac1ea, db51f0bf, 92d6f177).
* `StaircasePort/Signature.lean` — the port. Structure: N5-1 (unchanged) → N5-2 machinery →
  `namespace N52` port (platform stubs, `pDatStair`, the 1000-line `flag_gen` body specialized
  to h = 19) → `flagBasis_stair` (one-line delegation, mirrors
  `nb_flagBasis_solution.lean:198`).
* `gen_port.py` + `n52_platform_stubs.lean` + `n52_stairfactor.lean` → `n52_port.lean`
  (reproducible generator for the port body); `assemble_sig.py` assembles Signature.lean;
  `n52_axcheck.lean` prints the axiom profiles; `scratch_corner_check{,2}.py` the frame evidence.

### Remaining sorryAx in flagBasis_stair's footprint (all documented)
1. `N52.aux_edge_of` — PLATFORM STUB of `IntMul.Kappa.R6.Bit.NB.aux_edge_of`
   (Proved, c973e50d-124a-489e-b0fd-ac3804a68d0b). Body in `ref/nb_aux_edge_of_solution.lean:561`.
2. `N52.side_edge_of` — PLATFORM STUB of `.side_edge_of` (Proved,
   f2e5b569-5d59-4157-8761-498f52b51299). Body in `ref/nb_side_edge_of_solution.lean:196`.
3. `StaircasePort.Stair.isPiv_stair_lower` — N2d (Pivot.lean:310), a later wave, consumed as a
   hypothesis by design (`data_edge_stair`'s `hpiv`).
4. `Platform.edge_of_pivs` (f66c9619) inside `data_edge_stair` (N5-1's documented stub).
`N52.idem_similar` is NOT a stub: ported verbatim from `ref/nb_idem_similar_solution.lean`.

### Next moves (in order)
1. Port `aux_edge_of` + `side_edge_of` from the committed ref bodies (each needs
   `edge_exact`/`isPiv_diag_of_lower`/`isPiv_block`; `isPiv_mid` is already a `Platform` stub in
   Pivot.lean) — drops 2 of the 4 sorryAx sources; then flagBasis_stair's footprint reduces to
   N2d + `edge_of_pivs`.
2. Discharge N2d (Pivot.lean:310) — the last real math. Note the frame warning above: its
   `hdet` is the staircase frame, and the r6-frame identity `Cp i j = cor M i j`
   (nb_data_edge_solution.lean:534-537) does NOT transfer to `corStairQ` (`corStairQ_cast` in
   Cert.lean is the Z->Q cast only). N2d needs its own corner-transfer lemma.
3. Statement audit item: `DataE'`'s `rs'.length = 6` is h-only; fine.

### Gotchas added (banked, new)
* `lake env lean <file>` does NOT refresh `.olean`s — an `import` of a file you just edited via
  `lake env lean` still sees the OLD olean. Run `lake build` before importing your own changes.
* Substituting a concrete `h := 19` into a generic body breaks `simp` matching: `Fin (19 + 4)`
  and `Fin 23` are defeq but NOT syntactically equal, so simp lemmas stated at one shape will
  not fire at the other. Use `rw [<specialized lemma> ...]` (syntactic) or `show ... from`.
* When regex-substituting a variable name in Lean source, protect named-argument LABELS
  (`(h := ...)` must keep the `h`).
* A hypothesis named `h` (`intro h`, `have h :`) is silently rewritten by such a substitution.
