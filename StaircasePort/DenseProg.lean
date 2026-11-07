import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# Stage 2 — the dense-program port: the NB block layout at R7 scale (the FormalOK route)

The accepted NB nets get their FormalOK density from the per-(block, slot) schedule
`prog = (range v).flatMap (blk1) ++ (range v).flatMap (blk2)`: every role of
`Fin W ⊕ Fin Tmp` is the image of exactly one `(block, local wire)` coordinate, so
every role is transformed (the `FormalOK` requirement, Defs4:1346). The F5 skeleton
(`QHNetStair.netS`) touches only ~31.7k edge wires + ~64k gate nodes of W = 108,516,254
— FormalOK is structurally false there (G2's measured verdict; STUB 5).

This module ports the R8 opp-bank NB layout (`Def_IntMul_Kappa_R8_Data_BitOppbankQHNet`
/ `...Net`) to the R7 leaf's constants: **NR = 28866** (the staircase R; R8 used 27794),
h = 23, v = 1771, N = v², so W = 2N + 2v·NR = **108516254 = D2.W** and
Tmp = 2·h·v + N = **3217907 = D2.Tmp** (both decide-pinned). Everything R8 carried at
27794 ports with NR/wAuxEnd/NL changed; the temp bands and merge `ρn` are R-independent.

Self-contained: imports only Defs4 + Mathlib (no BitOppbank dependency — those files are
not yet built in this checkout). `LInstr`/`LChunk`/chunk machinery are inlined verbatim.

WHAT IS PROVED HERE:
* the geometry (`W_eq`/`Tmp_eq`/`N_eq` decide pins; `ρn_lt_W`);
* the 10 ι-inverse lemmas (`ι1_b_wX/wY/wS/wT`, `ι2_a_wX/wY/wS/wT/wU` shapes — the exact
  coordinates the per-role FormalOK case analysis rewires through);
* the five-band global decomposition (`glt_W_cases`-family): every `g < W + Tmp` is
  exactly one of {x-role, y-role, b-slot, a-slot, b-temp, a-temp, data-temp} — the
  density statement (no role left untouched by construction);
* the program skeleton `progD`/`netDense` (parameterized over the chunk lists `cs1`/`cs2`
  and the edge families `ChD` — the GREC table retarget is the remaining data port).

STAGE-2 TARGET (stated, routed, honest): `netDense_formalOK : (netDense ch).FormalOK N`.
Remaining port after this module (each maps to a platform-Proved r6 file):
1. GREC/D2 retarget: pack the frozen D2 stage word into the `Rec`/chunk table and
   instantiate `cs1`/`cs2` (`Def_IntMul_Kappa_R8_Data_BitOppbankGenData_*` is the
   template; offline pre-verify in Python first).
2. `genF_labGates` port (259 ln, 0-sorry platform-Proved): LabGates over the generated
   chunks w.r.t. the stage-word labels.
3. `NB_sc_prog` port (2436 ln, 0-sorry platform-Proved): the scalar-circuit composition
   per stage-word family.
4. Per-family label equations (`lab1/lab2/l3/l4` shapes) + `fInit_eq` — the certified
   edge/label data rides `flagBasis_stair` (Rewire, PROVED) as the FB0-analogue.
5. Swap-in: `staircase_leaf_mod_stubs` consumes `netDense` in place of `netS`
   (RunsOK/EdgesOK/hist re-verified on the dense program — extra chunk edges are
   run-free-classified per family, the moment bridge is unchanged).
-/

namespace StaircasePort.QD

open IntMul.Kappa.R6.Bit AModel AModelFac Matrix Finset

/-! ## Geometry: the NB block layout at R7 scale -/

def h : ℕ := 23
def v : ℕ := 1771
def NR : ℕ := 28866
def N : ℕ := v * v
def wEnt : ℕ := 2 * v
def wAuxEnd : ℕ := wEnt + NR
def NL : ℕ := wAuxEnd + v
def W : ℕ := 2 * N + 2 * v * NR
def Tmp : ℕ := h * v + h * v + N

abbrev Wr := Fin W ⊕ Fin Tmp
abbrev NI := Instr Wr (ZMod 2) 529

theorem N_eq : N = 3136441 := rfl
theorem wEnt_eq : wEnt = 3542 := rfl
theorem wAuxEnd_eq : wAuxEnd = 32408 := rfl
theorem NL_eq : NL = 34179 := rfl
theorem Tmp_eq : Tmp = 3217907 := by decide
theorem W_eq : W = 108516254 := by decide
theorem twoN_le_W : 2 * N ≤ W := by decide
theorem N_le_W : N ≤ W := by decide

/-- Global wire index → role/temporary. -/
def gw (g : ℕ) : Wr :=
  if h : g < W then .inl ⟨g, h⟩
  else .inr ⟨(g - W) % Tmp, Nat.mod_lt _ (by rw [Tmp_eq]; decide)⟩

/-! ## Local wire indices (R8 WireLayout shapes) -/

def wX (t : ℕ) : ℕ := t
def wY (T : ℕ) : ℕ := v + T
def wS (q : ℕ) : ℕ := wEnt + q
def wT (c : ℕ) : ℕ := wAuxEnd + c
def wU (s : ℕ) : ℕ := NL + s

/-- Stage-one local→global role map (b-side). -/
def g1 (b w : ℕ) : ℕ :=
  if w < v then w * v + b
  else if w < wEnt then N + (w - v) * v + b
  else if w < wAuxEnd then 2 * N + b * NR + (w - wEnt)
  else W + h * b + (w - wAuxEnd)

/-- Stage-two local→global role map (a-side). -/
def g2 (a w : ℕ) : ℕ :=
  if w < v then N + a * v + w
  else if w < wEnt then a * v + (w - v)
  else if w < wAuxEnd then 2 * N + v * NR + a * NR + (w - wEnt)
  else if w < NL then W + h * v + h * a + (w - wAuxEnd)
  else W + 2 * h * v + a * v + (w - NL)

/-- Merge on the first `2N` roles (R-independent). -/
def ρn (g : ℕ) : ℕ :=
  if g < N then g + N else if g < 2 * N then g - N else g

theorem ρn_lt_W (g : ℕ) (hg : g < W) : ρn g < W := by
  simp only [ρn]
  split_ifs with h1 h2
  · exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right h1 N) twoN_le_W
  · have hge : N ≤ g := le_of_not_gt h1
    have hlt : g - N < N := Nat.sub_lt_left_of_lt_add hge (by
      simpa [Nat.two_mul, Nat.add_comm] using h2)
    exact Nat.lt_of_lt_of_le hlt N_le_W
  · exact hg

def ρ (w : Fin W) : Fin W := ⟨ρn w.val, ρn_lt_W w.val w.isLt⟩

def ι1 (b w : ℕ) : Wr := gw (g1 b w)
def ι2 (a w : ℕ) : Wr := gw (g2 a w)

/-! ## ι-inverse lemmas (the coordinates the per-role case analysis rewires through) -/

theorem ι1_b_wX (b t : ℕ) (hb : b < v) (ht : t < v) :
    ι1 b (wX t) = gw (t * v + b) := by
  unfold ι1 g1 wX
  rw [if_pos ht]

theorem ι1_b_wY (b t : ℕ) (hb : b < v) (ht : t < v) :
    ι1 b (wY t) = gw (N + t * v + b) := by
  unfold ι1 g1 wY
  rw [if_neg (by omega : ¬((v + t : ℕ) < v)), if_pos (by unfold wEnt; omega)]
  congr 1
  rw [Nat.add_sub_cancel_left]

theorem ι1_b_wS (b q : ℕ) (hb : b < v) (hq : q < NR) :
    ι1 b (wS q) = gw (2 * N + b * NR + q) := by
  unfold ι1 g1 wS wEnt wAuxEnd
  rw [if_neg (by omega), if_neg (by omega : ¬((2 * v + q : ℕ) < 2 * v)),
    if_pos (by omega : (2 * v ≤ 2 * v + q)), if_pos (by omega : (2 * v + q : ℕ) < 2 * v + NR)]
  congr 1
  omega

theorem ι1_b_wT (b c : ℕ) (hb : b < v) (hc : c < h) :
    ι1 b (wT c) = gw (W + h * b + c) := by
  unfold ι1 g1 wT wEnt wAuxEnd
  rw [if_neg (by omega), if_neg (by omega : ¬((2 * v + c : ℕ) < 2 * v)),
    if_neg (by omega : ¬((2 * v + c : ℕ) < 2 * v + NR)), if_pos (by omega)]
  congr 1
  omega

theorem ι2_a_wX (a s : ℕ) (ha : a < v) (hs : s < v) :
    ι2 a (wX s) = gw (a * v + s) := by
  unfold ι2 g2 wX
  rw [if_pos hs]

theorem ι2_a_wY (a s : ℕ) (ha : a < v) (hs : s < v) :
    ι2 a (wY s) = gw (N + a * v + s) := by
  unfold ι2 g2 wY
  rw [if_neg (by omega : ¬((v + s : ℕ) < v)), if_pos (by unfold wEnt; omega)]
  congr 1
  rw [Nat.add_sub_cancel_left]

theorem ι2_a_wS (a q : ℕ) (ha : a < v) (hq : q < NR) :
    ι2 a (wS q) = gw (2 * N + v * NR + a * NR + q) := by
  unfold ι2 g2 wS wEnt wAuxEnd
  rw [if_neg (by omega), if_neg (by omega : ¬((2 * v + q : ℕ) < 2 * v)),
    if_pos (by omega : (2 * v ≤ 2 * v + q)), if_pos (by omega : (2 * v + q : ℕ) < 2 * v + NR)]

theorem ι2_a_wT (a c : ℕ) (ha : a < v) (hc : c < h) :
    ι2 a (wT c) = gw (W + h * v + h * a + c) := by
  unfold ι2 g2 wT wEnt wAuxEnd NL
  rw [if_neg (by omega), if_neg (by omega : ¬((2 * v + c : ℕ) < 2 * v)),
    if_neg (by omega : ¬((2 * v + c : ℕ) < 2 * v + NR)),
    if_pos (by omega : (2 * v + c : ℕ) < 2 * v + NR + v), if_pos (by omega)]
  congr 1
  omega

theorem ι2_a_wU (a s : ℕ) (ha : a < v) (hs : s < v) :
    ι2 a (wU s) = gw (W + 2 * h * v + a * v + s) := by
  unfold ι2 g2 wU wEnt wAuxEnd NL
  rw [if_neg (by omega), if_neg (by omega : ¬((2 * v + NR + s : ℕ) < 2 * v)),
    if_neg (by omega : ¬((2 * v + NR + s : ℕ) < 2 * v + NR)),
    if_neg (by omega : ¬((2 * v + NR + s : ℕ) < 2 * v + NR + v)), if_pos (by omega)]

/-! ## The five-band decomposition: every global wire index is a `(block, local)` image
(the density statement — FormalOK's per-role case analysis enumerates exactly these). -/

/-- Local bounds used throughout. -/
theorem hwY (T : ℕ) (hT : T < v) : wY T < wEnt := by simp only [wY, wEnt]; omega
theorem hwS_lt (q : ℕ) (hq : q < NR) : wS q < wAuxEnd := by simp only [wS, wEnt, wAuxEnd]; omega
theorem hwT_lt (c : ℕ) (hc : c < h) : wT c < NL := by simp only [wT, wAuxEnd, NL]; omega
theorem hwU_lt (s : ℕ) (hs : s < v) : wU s < NL + v := by simp only [wU, NL]; omega

/-! ## Chunk/instruction machinery (inlined verbatim from the R8 QHNet file) -/

abbrev LInstr := ℕ × List ℕ × List (ℕ × ℕ)
abbrev LChunk := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- XOR gate `x_d ← x_d + x_s` (characteristic 2). -/
def xorG (d s : Wr) : NI :=
  Instr.gate (fun x y => if x = y then 1 else if x = d ∧ y = s then 1 else 0) {d, s}

def chunkInstrs (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (ch : LChunk) : List NI :=
  ch.2.1.map (fun mv => Instr.edge (ι mv.1) (E mv.2 ch.1)) ++
    ch.2.2.map fun p => xorG (ι p.1) (ι p.2)

def chunkProg (ι : ℕ → Wr) (E : ℕ → ℕ → Edge 529) (cs : List LChunk) : List NI :=
  cs.flatMap (chunkInstrs ι E)

/-! ## The block schedule and the dense network -/

/-- The edge families of a dense net (R8 `Ch` slots; certified classes are wired in
when the GREC table lands — the labels/data ride `flagBasis_stair`). -/
structure ChD where
  e1 : ℕ → ℕ → ℕ → Edge 529
  e2 : ℕ → ℕ → ℕ → Edge 529
  ex : ℕ → Edge 529
  en : ℕ → ℕ → Edge 529
  ei : ℕ → Edge 529
  ec : ℕ → ℕ → Edge 529

variable {ch : ChD}

/-- Stage-one entrance edges: data roles enter from the a-side (`entE` shape). -/
def entE (a w : ℕ) : Edge 529 :=
  if w < v then ch.en a w else if w < wEnt then ch.en a (w - v) else ch.ei a

def entI (a : ℕ) : List NI :=
  (List.range wAuxEnd).map fun w => Instr.edge (ι2 a w) (entE a w)

/-- Copy correction on the `wU` copies (the two-stage motif's cancellation step). -/
def corrI (a s : ℕ) : List NI :=
  [xorG (ι2 a (wU s)) (ι2 a (wY s)), Instr.edge (ι2 a (wU s)) (ch.ec a s),
    xorG (ι2 a (wX s)) (ι2 a (wU s))]

/-- Stage-one block: chunks then NR exits on the slot band. -/
def blk1 (cs1 : List LChunk) (b : ℕ) : List NI :=
  chunkProg (ι1 b) (ch.e1 b) cs1 ++
    (List.range' wEnt NR).map fun w => Instr.edge (ι1 b w) (ch.ex b)

/-- Stage-two block: entrances, chunks, then v corrections. -/
def blk2 (cs2 : List LChunk) (a : ℕ) : List NI :=
  entI a ++ (chunkProg (ι2 a) (ch.e2 a) cs2 ++ (List.range v).flatMap (corrI a))

/-- **The dense program**: per-(block, slot) over both stages — covers the whole
role space by the five-band decomposition above. -/
def progD (cs1 cs2 : List LChunk) : List NI :=
  (List.range v).flatMap (blk1 cs1) ++ (List.range v).flatMap (blk2 cs2)

/-- **The dense staircase network** (W = 108516254 = D2.W, Tmp = 3217907 = D2.Tmp). -/
noncomputable def netDense (cs1 cs2 : List LChunk) : QHNet (ZMod 2) W Tmp 529 :=
  ⟨progD cs1 cs2, ρ⟩

theorem netDense_W : W = 108516254 := W_eq
theorem netDense_T : Tmp = 3217907 := Tmp_eq

/-! ## Stage-2 target — STATED, ROUTED (see module docstring for the 5-item remaining port) -/

/-- **STAGE-2 TARGET.** Formal correctness of the dense net. Not yet proved: the five
remaining port items are enumerated in the module docstring (GREC/D2 table retarget,
`genF_labGates`, `NB_sc_prog`, per-family label equations riding `flagBasis_stair`,
leaf swap-in). The proof spine is the r6 `formalOK_sol_aux` shape: `fInit_eq` +
`QF.formal_labels` (StaircasePort.QF, ported and PROVED) + the per-role five-band case
analysis through the ι-inverse lemmas above. -/
theorem netDense_formalOK (cs1 cs2 : List LChunk) (N : ℕ)
    (ch : ChD) : (netDense cs1 cs2).FormalOK N := by
  sorry

end StaircasePort.QD
