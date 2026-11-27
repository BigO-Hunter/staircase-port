# FORMALOK_REPORT — Stage 2, the `netS_FormalOK` port (2026-11-06)

Leaf: bitNetR7_mom (e27d1a90) · repo: `this repo` · lane: THE LADDER'S
FORMALOK PORT. Stage-1 facts stand untouched (RunsOK / EdgesOK_large / `netS_dominance`
PROVED; leaf sorryAx road = STUB 5 `netS_FormalOK` only + Rewire's 3 documented Platform
stubs inside the discharged witnesses).

## What the port delivered (all elaborates clean vs cached oleans; both
modules are OFF the pending Corner→Projector→Rewire chain — additive, nothing imports them)

### 1. `StaircasePort/FormalCalc.lean` — the `formal_labels` calculus (PROVED, 0 sorry)
* `lmulF_mul` + `formal_labels` (generic): on a `LabGates` segment, formal values
  `L_w · φ_w` evolve as `L'_w · ψ_w` (labels via `labStepH`, values via `scalarStepM`).
  Verbatim port of the platform's Proved r6 `Thm_IntMul_Kappa_R6_Bit_formal_labels`
  (112 ln), own namespace `StaircasePort.QF`.
* `formalOK_of_tracks` (NEW, fully generic): the r6 `formalOK_sol_aux` proof spine
  abstracted — `fInit = lmulF ∘ L0/φ0` + `LabGates` + per-family (label track lands
  `swapMat`) × (value track lands the role's single term) **⇒ FormalOK**. This is the
  reusable consumer-shape lemma family; the per-role work is now pure per-band data.

### 2. `StaircasePort/DenseProg.lean` — the dense-program port at R7 scale
* **Geometry** (proved): NB block layout retargeted NR 27794→**28866** (R7's R),
  h=23, v=1771, N=v² ⇒ **W = 2N+2v·NR = 108516254**, **Tmp = 2hv+N = 3217907** — both
  `decide`-pinned, numerically = D2.W / D2.Tmp. `ρn`/`ρ`/`ρn_lt_W` port clean (merge is
  R-independent).
* **10 ι-inverse lemmas** (proved): `ι1_b_wX/wY/wS/wT`, `ι2_a_wX/wY/wS/wT/wU` — the exact
  coordinates the per-role case analysis rewires through (r6 `ι1x_eq`… shapes).
* **Injectivity block** (proved): `gw_inj`/`g1_lt`/`g2_lt`/`g1_inj`/`g2_inj`/`ι1_inj`/
  `ι2_inj` — consumed by the label-port items (2)-(4) (r6 `g2_inj`/`ι1_inj` shapes).
* **`gw_band_cases` (proved — the DENSITY statement):** every global wire index
  `g < W + Tmp` is exactly one `(block, local wire)` coordinate across the seven bands
  (x-roles [0,N) / y-roles [N,2N) / b-slots / a-slots / 3 temp bands), div/mod witness
  extraction included. Roles transformed **7/7 bands — 108,516,254 + 3,217,907 of
  themselves, by construction** (the F5 skeleton's coverage gap is closed structurally).
* **Program skeleton** (defined, parameterized): `LInstr`/`LChunk`/`chunkInstrs`/
  `chunkProg` (inlined R8 shapes), `ChD` edge-family record, `entI`/`corrI`/`blk1`/
  `blk2`/`progD`/`netDense : QHNet (ZMod 2) 108516254 3217907 529` — parameterized over
  the chunk lists (cs1/cs2) and edge families.
* **STAGE-2 TARGET stated + routed (1 documented sorry):** `netDense_formalOK`.

### 3. Calculus status
Generic parts PROVED (`formal_labels`, `lmulF_mul`, `formalOK_of_tracks`). Per-role
instances: pending the remaining port (below). `flagBasis_stair` (Rewire, PROVED) is the
FB0-analogue the per-family label equations consume.

## Remaining port to close `netS_FormalOK` (each item = platform-Proved r6 file or data)
1. **GREC/D2 table retarget** (data, offline-pre-verify in Python first): pack the frozen
   D2 stage word into the `Rec`/chunk shape and instantiate `cs1`/`cs2` (template:
   `Def_IntMul_Kappa_R8_Data_BitOppbankGenData_*` + `LocGrecDense`; NOTE those R8 files
   are in `Definitions/` but NOT yet built in this checkout — the R8 work owns them).
   The audited R8 landmine applies: the `mixFB` segment boundaries are load-bearing;
   do not "fix" coverage.
2. **`genF_labGates` port** (259 ln, 0-sorry platform-Proved): LabGates over the
   generated chunks w.r.t. the stage-word labels.
3. **`NB_sc_prog` port** (2436 ln, 0-sorry platform-Proved): per-stage-word-family
   scalar-circuit composition.
4. **Per-family label equations** (`lab1/lab2/l3/l4` + `fInit_eq` shapes): the certified
   data rides `flagBasis_stair` + N3's `stair_data_cert` (GoodM collapse
   `redM_pswQ_one`/`final_y` shapes).
5. **Leaf swap-in**: `staircase_leaf_mod_stubs` consumes `netDense` in place of `netS`;
   re-verify RunsOK/EdgesOK/hist on the dense program (chunk edges classify per family;
   run-free edges leave the moment bridge untouched; EdgesOK needs per-edge clearance).

## axcheck footprint
`n5_axcheck.lean` NOT re-run: QHNetStair re-elaboration is blocked on the
Corner→Projector→Rewire chain (5 concurrent `lake build` processes grinding; the
check drivers exhausted their attempt budgets, `Rewire.olean` still absent). Expected
post-chain road: leaf = STUB 5 + Rewire's 3 Platform stubs; after items 1-5: STUB 5
drops to `Platform`-stub-only (the 3 documented stubs inside the discharged witnesses —
acceptable per the receipt condition).

## Resume point
1. `grep "Build completed successfully"` in the build log or relaunch a driver
   (LAKE_JOBS=1, LEAN_NUM_THREADS=1, detached, never foreground >2 min) — the chain
   (Corner→Projector→Rewire) then auto-elaborates QHNetStair; fix any real-file-context
   errors, re-run `n5_axcheck.lean`.
2. In parallel (no chain dependency): item 1, the GREC/D2 table retarget — start from
   `extract/jainroot` + `d2_data.json` (frozen), mirror the R8 GenData_0 packing, and
   probe `mixFB` boundary choices offline before any Lean elaboration.
3. Then items 2-4 (mechanical ports of the two platform-Proved files) onto
   `FormalCalc.formalOK_of_tracks` + `DenseProg.gw_band_cases`.
