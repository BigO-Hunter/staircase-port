/-
# Stage 1 — the staircase witness-1 QHNet object, RunsOK + EdgesOK + the moment bridge

LANE F5 construction over the certified D2 dataset (StaircasePort.D2Data, stage-0 verified:
regen byte-identical, independent oracle, `d2HIST = Jain.bitR7` zero-axiom). Template: the
R8 opp-bank net (`Def_IntMul_Kappa_R8_Data_BitOppbankQHNet` / `Net0Pnd` shape, itself the
xuanji r6 NB retarget): wire map + program skeleton + `pickE` edge families with certified
run lists; EdgesOK at large prime powers via the `edgeOK_large_of_edgeQ` good-prime route
(ported from the plain-line `Thm_net0Pnd_EdgesOK`).

WHAT IS PROVED HERE (no new data invented):
* the object `netS : QHNet (ZMod 2) 108516254 Tmp 529` (T = 3217907, D2-pinned);
* `netS_RunsOK` — every edge carries a certified run list (stairDataRuns ++ stairSingles
  via Data.lean `stairRunOK`; auxRuns 19; sideRuns 23 529 r by arithmetic; dfltE vacuous);
* `netS_EdgesOK_large` — uniform good-prime clearance (Q witnesses from the pickE stubs);
* the D3 moment bridge REDUCTION: one list identity (`netS_hist_eq`, the schedule-multiplicity
  stub) implies BOTH `netS_powSum_eq` (powSum q netHist = bitR7PowSum q, the D3 shape against
  the frozen MomOracle) AND the leaf's moment dominance (via `histMoment_expansion`);
* the leaf assembly `staircase_leaf_mod_stubs` in the exact `BitNetMomStmtG` shape.

THE DOCUMENTED STUBS (Platform-stub pattern; every one names its discharge route):
1. DISCHARGED (this lane, F5b): `exists_dataE` — direct composition of Rewire's
   `data_edge_stair` at the witness labels (hdet := stair_data_cert, corner clause :=
   isPiv_stairCorner_witness). dataPred/sidePred were RESTATED to the shape the staircase
   machinery delivers (certified run list ++ existential singleton suffix with pinned
   counts) — the delivered shape's RunOK rides EdgeQ's own first conjunct.
2. DISCHARGED (this lane, F5b): `exists_auxE` — Rewire's `aux1_edge_Stair` at generic
   labels (all-ones x, y = 1/23); the delivered run list IS `auxRuns 19`.
3. DISCHARGED (this lane, F5b): `exists_sideE r` — Rewire's `side1_edge_Stair` at generic
   labels with the explicit rank-r idempotent `sideA r` (block form [I_r Y₂; 0 0]; rank by
   N52.rank_eq_trace; corner block = anti-diagonal, det ≠ 0 by orthogonality).
4. `netS_hist_eq`   — the net's child-width multiset is bitR7 expanded. This is the producer
   readout-schedule multiplicity port (deferred.py readout/V-gate structure ↔ d2HIST block
   structure); the R8 line carried the identical residual (NetMom `MomEqStmt` open).
5. `netS_FormalOK`  — the formal-frame calculus port (Stage 2): flagBasis_stair (Rewire,
   proved) + formal_labels/genF_labGates machinery over the D2 gate schedule.

Gate wire map: operand node codes (1..64042 in d2OPS) map through `gw` to roles `Fin W`;
the semantic node→(role/temporary) schedule (d2WOUTC/T/N + RET tables) is Stage 2's
FormalOK/ScalarOK port and is NOT claimed here — gates carry no edges, so RunsOK, EdgesOK
and hist are independent of it.
-/

import StaircasePort.D2Data
import StaircasePort.MomOracle
import StaircasePort.Data
import StaircasePort.Rewire
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000

namespace StaircasePort.QS

open IntMul.Kappa.R6.Bit
open IntMul.Kappa.R6.Bit.NB
open StaircasePort.Stair
open AModel AModelFac Matrix Finset

/-! ## Wire map (D2 geometry) -/

abbrev Wr := Fin D2.W ⊕ Fin D2.Tmp
abbrev NI := Instr Wr (ZMod 2) 529

/-- Global wire index → role/temporary (R8 `gw` pattern; D2.W = 108516254, D2.Tmp = 3217907). -/
def gw (g : ℕ) : Wr :=
  if h : g < D2.W then .inl ⟨g, h⟩
  else .inr ⟨(g - D2.W) % D2.Tmp, Nat.mod_lt _ (by norm_num [D2.Tmp])⟩

/-- The node-code wire map used by the d2OPS gate schedule (nodes 1..64042 < W). -/
def ι (n : ℕ) : Wr := gw n

theorem ρn_lt_W (g : ℕ) (hg : g < D2.W) : D2.ρn g < D2.W := by
  have hN : 2 * D2.N ≤ D2.W := by decide
  unfold D2.ρn
  split_ifs with h1 h2
  · omega
  · omega
  · exact hg

/-- The merge permutation (WireLayout ρn shape). -/
def ρF (w : Fin D2.W) : Fin D2.W := ⟨D2.ρn w.val, ρn_lt_W w.val w.isLt⟩

/-! ## The d2OPS gate schedule (gates only; no edges) -/

/-- Raw op field-groups as decoded records: `src` = [1,d,s], `add` = [2,d,s1,s2],
`fan` = [3,d,k,t₁..t_k] (extract/d2_regen.py `opf`). Fuel-driven decode; padding
fields (0) terminate. -/
inductive DOp where
  | src (d s : ℕ) : DOp
  | add (d s1 s2 : ℕ) : DOp
  | fan (d : ℕ) (ts : List ℕ) : DOp

def opsTake (i k : ℕ) : List ℕ := (List.range k).map fun j => D2.fieldOf D2.d2OPS 16 (i + j)

def opsDec : ℕ → ℕ → List DOp
  | _, 0 => []
  | i, fuel + 1 =>
    match D2.fieldOf D2.d2OPS 16 i with
    | 1 => DOp.src (D2.fieldOf D2.d2OPS 16 (i + 1)) (D2.fieldOf D2.d2OPS 16 (i + 2)) ::
        opsDec (i + 3) fuel
    | 2 => DOp.add (D2.fieldOf D2.d2OPS 16 (i + 1)) (D2.fieldOf D2.d2OPS 16 (i + 2))
        (D2.fieldOf D2.d2OPS 16 (i + 3)) :: opsDec (i + 4) fuel
    | 3 => DOp.fan (D2.fieldOf D2.d2OPS 16 (i + 1))
        (opsTake (i + 3) (D2.fieldOf D2.d2OPS 16 (i + 2))) ::
        opsDec (i + 3 + D2.fieldOf D2.d2OPS 16 (i + 2)) fuel
    | _ => []

/-- The decoded stage-1 word (82983 ops, D2 RESUME). -/
def d2Ops : List DOp := opsDec 0 82983

/-- XOR gate `x_d ← x_d + x_s` (R8 `xorG`, characteristic 2). -/
def xorG (d s : Wr) : NI :=
  Instr.gate (fun x y => if x = y then 1 else if x = d ∧ y = s then 1 else 0) {d, s}

/-- One decoded op → its XOR-gate instructions (`add` of two sources = two xors;
`fan` = broadcast the destination into each target). Gate semantics only. -/
def gatesOf : DOp → List NI
  | .src d s => [xorG (ι d) (ι s)]
  | .add d s1 s2 => [xorG (ι d) (ι s1), xorG (ι d) (ι s2)]
  | .fan d ts => ts.map fun t => xorG (ι t) (ι d)

theorem gatesOf_none : ∀ (op : DOp) (j : NI), j ∈ gatesOf op → j.edgeOf = none := by
  intro op j hj
  cases op with
  | src d s =>
      simp only [gatesOf, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rw [hj]; rfl
  | add d s1 s2 =>
      simp only [gatesOf, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl <;> rfl
  | fan d ts =>
      simp only [gatesOf, List.mem_map] at hj
      obtain ⟨t, -, rfl⟩ := hj
      rfl

/-! ## Edge classes with certified run lists -/

/-- The certified staircase data-edge run list (N1; `stairRunOK` proved in Data.lean). -/
def D1 : List (ℕ × ℕ × ℕ) := stairDataRuns 23 529 ++ stairSingles 529

/-- Trivial edge (no runs, unit Bruhat factors) — exit-class carrier (R8 `dfltE`). -/
def dfltE : Edge 529 := ⟨1, [], 1⟩

open Classical in
/-- Pick the unique-ish inhabitant of a nonempty edge predicate (R8 `pickE`). -/
noncomputable def pickE (P : Edge 529 → Prop) : Edge 529 :=
  if h : ∃ e, P e then Classical.choose h else dfltE

theorem pickE_spec {P : Edge 529 → Prop} (h : ∃ e, P e) : P (pickE P) := by
  unfold pickE
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- Data class in the shape the staircase machinery DELIVERS (`Rewire.data_edge_stair` =
`DataE'`): the certified run list plus an existential 6-singleton suffix. The singleton
COUNT is what the moment algebra consumes (each contributes width 1); the specific
positions are the pivot extraction's choice and are pinned nowhere downstream. -/
def dataPred (e : Edge 529) : Prop :=
  ∃ Q : Matrix (Fin 529) (Fin 529) ℚ, EdgeQ e Q ∧ ∃ rs',
    e.runs = stairDataRuns 23 529 ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧ rs'.length = 6
def auxPred (e : Edge 529) : Prop := ∃ Q : Matrix (Fin 529) (Fin 529) ℚ, EdgeQ e Q ∧ e.runs = auxRuns 19
/-- Side class in the shape `Rewire.side1_edge_Stair` delivers: the certified width-run
plus an existential singleton suffix (total pivot count r). -/
def sidePred (r : ℕ) (e : Edge 529) : Prop :=
  ∃ Q : Matrix (Fin 529) (Fin 529) ℚ, EdgeQ e Q ∧ ∃ rs',
    e.runs = sideRuns 23 529 r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
    (runPairs (sideRuns 23 529 r)).length + rs'.length = r

/-- Side-class ranks: widths 2r−23 ∈ {1,3,…,21} for r = 12..22 (the odd tail of d2HIST);
ranks ≤ 11 give empty run lists (childless) and are omitted. -/
def sideRanks : List ℕ := List.range' 12 11

noncomputable def dataE : Edge 529 := pickE dataPred
noncomputable def auxE : Edge 529 := pickE auxPred
noncomputable def sideE (r : ℕ) : Edge 529 := pickE (sidePred r)

/-! ## Generic labels for the aux/side classes (any nonzero labels with y·x = 1) -/

open scoped Kronecker in
theorem aux_hxy : (fun _ : Fin 23 => ((1 : ℚ) / 23)) ⬝ᵥ (fun _ : Fin 23 => 1) = 1 := by
  simp only [dotProduct, Fin.sum_univ_cast, one_mul]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_range]
  norm_num

/-! ## The side-class witness idempotent (rank r, invertible staircase corner block) -/

/-- The anti-diagonal 0-1 matrix has nonzero determinant (it is orthogonal: `Dᵀ * D = I`,
so `det D ^ 2 = 1`). -/
theorem antiDiagQ_det_ne_zero (n : ℕ) :
    (Matrix.of fun i j : Fin n => if (i : ℕ) + (j : ℕ) = n - 1 then (1 : ℚ) else 0).det ≠ 0 := by
  have hDD : (Matrix.of fun i j : Fin n => if (i : ℕ) + (j : ℕ) = n - 1 then (1 : ℚ) else 0)ᵀ *
      (Matrix.of fun i j : Fin n => if (i : ℕ) + (j : ℕ) = n - 1 then (1 : ℚ) else 0) = 1 := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : (i : ℕ) = (j : ℕ)
    · subst hij
      rw [Finset.sum_eq_single (⟨n - 1 - (i : ℕ), by have := i.isLt; omega⟩ : Fin n)]
      · rw [if_pos (by have := i.isLt; omega), if_pos (by have := i.isLt; omega),
          mul_one, if_pos rfl]
      · intro k _ hk
        have hik : (k : ℕ) ≠ n - 1 - (i : ℕ) := by
          intro hc
          exact hk (by rw [hc]; rfl)
        rw [if_neg (by have := k.isLt; omega : ¬((k : ℕ) + (i : ℕ) = n - 1))]
        exact zero_mul _
      · intro hb
        exact absurd hb (Finset.mem_univ _)
    · rw [Finset.sum_eq_zero]
      intro k _
      by_cases h1 : (k : ℕ) + (i : ℕ) = n - 1
      · rw [if_pos h1, if_neg (by have := k.isLt; omega : ¬((k : ℕ) + (j : ℕ) = n - 1))]
        exact mul_zero _
      · rw [if_neg h1]
        exact zero_mul _
  have h1 : ((Matrix.of fun i j : Fin n =>
        if (i : ℕ) + (j : ℕ) = n - 1 then (1 : ℚ) else 0)ᵀ).det *
      (Matrix.of fun i j : Fin n => if (i : ℕ) + (j : ℕ) = n - 1 then (1 : ℚ) else 0).det = 1 := by
    rw [← Matrix.det_mul, hDD, Matrix.det_one]
  intro h0
  rw [Matrix.det_transpose, h0, zero_mul] at h1
  exact zero_ne_one h1

/-- Rank-`r` idempotent with invertible staircase corner block: block form `[I_r Y₂; 0 0]`
— identity on the first `r` diagonal entries, plus an anti-diagonal bridge from rows `< r`
into columns `≥ r` along `i + j = 22`. -/
def sideA (r : ℕ) : Matrix (Fin 23) (Fin 23) ℚ :=
  Matrix.of fun i j =>
    if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then 1
    else if (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (i : ℕ) + (j : ℕ) = 22 then 1 else 0

/-- The 23×r half of the rank factorization (identity embedding). -/
def sideX (r : ℕ) : Matrix (Fin 23) (Fin r) ℚ :=
  Matrix.of fun i k => if (i : ℕ) = (k : ℕ) then 1 else 0

/-- The r×23 half of the rank factorization (`[I_r Y₂]`). -/
def sideY (r : ℕ) : Matrix (Fin r) (Fin 23) ℚ :=
  Matrix.of fun k j =>
    if (k : ℕ) = (j : ℕ) then 1 else if r ≤ (j : ℕ) ∧ (k : ℕ) + (j : ℕ) = 22 then 1 else 0

theorem sideYX (r : ℕ) : sideY r * sideX r = 1 := by
  ext k l
  simp only [Matrix.mul_apply, sideY, sideX, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨(l : ℕ), by have := l.isLt; omega⟩ : Fin 23)]
  · show (if (k : ℕ) = (l : ℕ) then (1 : ℚ)
        else if r ≤ (l : ℕ) ∧ (k : ℕ) + (l : ℕ) = 22 then (1 : ℚ) else 0) *
        (if (l : ℕ) = (l : ℕ) then (1 : ℚ) else 0) =
        (if (k : ℕ) = (l : ℕ) then (1 : ℚ) else 0)
    by_cases hkl : (k : ℕ) = (l : ℕ)
    · rw [if_pos hkl, if_pos rfl, mul_one, if_pos hkl]
    · rw [if_neg hkl,
        if_neg (by intro hc; have := l.isLt; omega :
          ¬(r ≤ (l : ℕ) ∧ (k : ℕ) + (l : ℕ) = 22)),
        zero_mul, if_neg hkl]
  · intro j _ hjne
    show sideY r k j * (if (j : ℕ) = (l : ℕ) then (1 : ℚ) else 0) = 0
    have hjl : (j : ℕ) ≠ (l : ℕ) := by
      intro hc
      exact hjne (Fin.val_inj.2 hc)
    rw [if_neg hjl]
    exact zero_mul _
  · intro hb
    exact absurd hb (Finset.mem_univ _)

theorem sideXY (r : ℕ) : sideX r * sideY r = sideA r := by
  ext i j
  by_cases hi : (i : ℕ) < r
  · rw [Finset.sum_eq_single (⟨(i : ℕ), by have := i.isLt; omega⟩ : Fin r)]
    · show (if (i : ℕ) = (i : ℕ) then (1 : ℚ) else 0) *
          (if (i : ℕ) = (j : ℕ) then (1 : ℚ)
            else if r ≤ (j : ℕ) ∧ (i : ℕ) + (j : ℕ) = 22 then (1 : ℚ) else 0) =
          (if (i : ℕ) = (j : ℕ) ∧ (i : ℕ) < r then (1 : ℚ)
            else if (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (i : ℕ) + (j : ℕ) = 22 then (1 : ℚ)
            else 0)
      simp only [show ((i : ℕ) = (i : ℕ)) = True from rfl, if_true]
      by_cases hij : (i : ℕ) = (j : ℕ)
      · rw [if_pos hij, if_pos (⟨hij, hi⟩ : ((i : ℕ) = (j : ℕ)) ∧ (i : ℕ) < r)]
      · rw [if_neg hij, if_neg (fun hc => hij hc.1.1),
          show (((i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (i : ℕ) + (j : ℕ) = 22) =
              (r ≤ (j : ℕ) ∧ (i : ℕ) + (j : ℕ) = 22)) from by rw [and_iff_left hi]]
    · intro k _ hkne
      show (if (i : ℕ) = (k : ℕ) then (1 : ℚ) else 0) * sideY r k j = 0
      have hik : (i : ℕ) ≠ (k : ℕ) := by
        intro hc
        exact hkne (Fin.val_inj.2 hc)
      rw [if_neg hik]
      exact zero_mul _
    · intro hb
      exact absurd hb (Finset.mem_univ _)
  · rw [Finset.sum_eq_zero]
    intro k _
    show (if (i : ℕ) = (k : ℕ) then (1 : ℚ) else 0) * sideY r k j = 0
    rw [if_neg (fun hc => hi (by have := k.isLt; omega : (i : ℕ) < r))]
    exact zero_mul _

theorem sideA_idem (r : ℕ) : sideA r * sideA r = sideA r := by
  have h1 : sideA r = sideX r * sideY r := (sideXY r).symm
  rw [h1, h1, ← Matrix.mul_assoc, sideYX r, Matrix.one_mul]

theorem sideA_trace (r : ℕ) (hr : r ≤ 23) : (sideA r).trace = (r : ℚ) := by
  show ∑ i : Fin 23, sideA r i i = (r : ℚ)
  have h1 : ∀ i : Fin 23, sideA r i i = (if (i : ℕ) < r then (1 : ℚ) else 0) := by
    intro i
    simp only [sideA, Matrix.of_apply]
    by_cases hlt : (i : ℕ) < r
    · simp [hlt]
    · simp [hlt]
  rw [Finset.sum_congr rfl (fun i _ => h1 i)]
  have h2 : ∀ i : Fin 23, (if (i : ℕ) < r then (1 : ℚ) else 0) =
      (Finset.range r).indicator (fun _ => (1 : ℚ)) i := fun i => by
    rw [Finset.indicator_apply, Finset.mem_range]
  rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_indicator_subset _ _
    (Finset.range_subset.2 hr), Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range]

theorem sideA_rank (r : ℕ) (hr : r ≤ 23) : (sideA r).rank = r := by
  have h1 := N52.rank_eq_trace (sideA r) (sideA_idem r)
  rw [sideA_trace r hr] at h1
  exact Nat.cast_injective (R := ℚ) h1

/-- The staircase corner block of `sideA r` is the anti-diagonal, hence invertible. -/
theorem sideA_hcor (r : ℕ) (hr : r ≤ 23) : 23 < 2 * r →
    ((sideA r).submatrix (fun l : Fin (23 - r) => (⟨(l : ℕ), by have := l.isLt; omega⟩ : Fin 23))
      (fun c : Fin (23 - r) => (⟨23 - (23 - r) + (c : ℕ), by have := c.isLt; omega⟩ : Fin 23))).det ≠ 0 := by
  intro _
  have hrEq : 23 - (23 - r) = r := by omega
  have hEq : (sideA r).submatrix
      (fun l : Fin (23 - r) => (⟨(l : ℕ), by have := l.isLt; omega⟩ : Fin 23))
      (fun c : Fin (23 - r) => (⟨23 - (23 - r) + (c : ℕ), by have := c.isLt; omega⟩ : Fin 23))
      = Matrix.of fun i j : Fin (23 - r) => if (i : ℕ) + (j : ℕ) = (23 - r) - 1 then (1 : ℚ) else 0 := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, sideA]
    show (if (i : ℕ) = 23 - (23 - r) + (j : ℕ) ∧ (i : ℕ) < r then (1 : ℚ)
        else if (i : ℕ) < r ∧ r ≤ 23 - (23 - r) + (j : ℕ) ∧
          (i : ℕ) + (23 - (23 - r) + (j : ℕ)) = 22 then (1 : ℚ) else 0) =
      (if (i : ℕ) + (j : ℕ) = (23 - r) - 1 then (1 : ℚ) else 0)
    have hi : (i : ℕ) < 23 - r := i.isLt
    have hc : (j : ℕ) < 23 - r := j.isLt
    simp only [hrEq]
    by_cases hsum : (i : ℕ) + (j : ℕ) = (23 - r) - 1
    · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [hEq]
  exact antiDiagQ_det_ne_zero (23 - r)

/-! ## The three frame-existence THEOREMS (stubs 1-3 DISCHARGED) -/

/-- (Was STUB 1.) Direct composition: `Rewire.data_edge_stair` at the witness labels —
hdet from `stair_data_cert` (N3), the 39-position corner clause from
`isPiv_stairCorner_witness` (N7). -/
theorem exists_dataE : ∃ e, dataPred e := by
  have hdet : (stairCornerQOf ((1 - vecMulVec stairQX1 stairQY1) ⊗ₖ
      (1 - vecMulVec stairQX2 stairQY2))).det ≠ 0 := stair_data_cert
  obtain ⟨e, hE, rs', hr1, hr2, hr3⟩ := data_edge_stair stairQX1 stairQY1 stairQX2 stairQY2
    stairQxy1 stairQxy2 hdet isPiv_stairCorner_witness
  exact ⟨e, _, hE, rs', hr1, hr2, hr3⟩

/-- (Was STUB 2.) Direct composition: `Rewire.aux1_edge_Stair` at generic nonzero labels
(all-ones over 23, y = 1/23) — the conclusion's run list IS `auxRuns 19`. -/
theorem exists_auxE : ∃ e, auxPred e := by
  obtain ⟨e, hE, hruns⟩ := aux1_edge_Stair (fun _ => (1 : ℚ) / 23) (fun _ => 1) aux_hxy
    (fun β _ => one_ne_zero) (fun _ => by norm_num)
  exact ⟨e, _, hE, hruns⟩

/-- (Was STUB 3.) Direct composition: `Rewire.side1_edge_Stair` at generic labels with the
explicit rank-r idempotent `sideA r` (rank by trace, corner block anti-diagonal). -/
theorem exists_sideE (r : ℕ) (hr : r ≤ 23) : ∃ e, sidePred r e := by
  obtain ⟨e, hE, rs', hr1, hr2, hr3⟩ := side1_edge_Stair (fun _ => (1 : ℚ) / 23) (fun _ => 1)
    aux_hxy (fun β _ => one_ne_zero) (fun _ => by norm_num) (sideA r) (sideA_idem r) r
    (sideA_rank r hr) (sideA_hcor r hr)
  exact ⟨e, _, hE, rs', hr1, hr2, hr3⟩

theorem dataE_spec : dataPred dataE := pickE_spec exists_dataE
theorem auxE_spec : auxPred auxE := pickE_spec exists_auxE
theorem sideE_spec (r : ℕ) (hr : r ≤ 23) : sidePred r (sideE r) := pickE_spec (exists_sideE r hr)

theorem dataE_h : ∃ Q : Matrix (Fin 529) (Fin 529) ℚ, EdgeQ dataE Q ∧ ∃ rs',
    dataE.runs = stairDataRuns 23 529 ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧ rs'.length = 6 :=
  pickE_spec exists_dataE
theorem auxE_h : ∃ Q : Matrix (Fin 529) (Fin 529) ℚ, EdgeQ auxE Q ∧ auxE.runs = auxRuns 19 :=
  pickE_spec exists_auxE
theorem sideE_h (r : ℕ) (hr : r ≤ 23) : ∃ Q : Matrix (Fin 529) (Fin 529) ℚ, EdgeQ (sideE r) Q ∧
    ∃ rs', (sideE r).runs = sideRuns 23 529 r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
    (runPairs (sideRuns 23 529 r)).length + rs'.length = r :=
  pickE_spec (exists_sideE r hr)

theorem dataE_EdgeQ : EdgeQ dataE (Classical.choose dataE_h) := (Classical.choose_spec dataE_h).1
theorem auxE_EdgeQ : EdgeQ auxE (Classical.choose auxE_h) := (Classical.choose_spec auxE_h).1
theorem sideE_EdgeQ (r : ℕ) (hr : r ≤ 23) : EdgeQ (sideE r) (Classical.choose (sideE_h r hr)) :=
  (Classical.choose_spec (sideE_h r hr)).1

theorem auxE_runs : auxE.runs = auxRuns 19 := (Classical.choose_spec auxE_h).2

/-- RunOK for the data class rides EdgeQ's own first conjunct (the delivered run shape
is DataE''s, not the pinned D1 — the moment algebra only needs the singleton count). -/
theorem dataE_runOK : ∀ ρ ∈ dataE.runs, RunOK 529 ρ := fun ρ hρ => dataE_EdgeQ.1 ρ hρ
theorem sideE_runOK (r : ℕ) (hr : r ≤ 23) : ∀ ρ ∈ (sideE r).runs, RunOK 529 ρ :=
  fun ρ hρ => sideE_EdgeQ r hr |>.1 ρ hρ

/-! ## Trivial-edge EdgeQ (no runs) — dfltE_Q pattern, proved -/

theorem pswQ_zero {m : ℕ} : pswQ (0 : Matrix (Fin m) (Fin m) ℚ) = 1 := by
  unfold pswQ
  rw [sub_zero, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem dfltE_EdgeQ : EdgeQ dfltE 0 := by
  refine ⟨fun ρ h => absurd h List.not_mem_nil, fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
    fun i => by rw [show dfltE.E₁ = 1 from rfl, Matrix.one_apply_eq]; exact one_ne_zero,
    fun i j hij => Matrix.one_apply_ne (ne_of_lt hij),
    fun i => by rw [show dfltE.E₂ = 1 from rfl, Matrix.one_apply_eq]; exact one_ne_zero, ?_⟩
  rw [pswQ_zero]
  show (1 : QMat2 529) * (([] : List (Fin (529 + 529) × Fin (529 + 529))).map
    fun p => Equiv.swap p.1 p.2).prod.permMatrix ℚ * 1 = 1
  simp

/-! ## The network object -/

/-- Edge-instruction schedule: data class on the target wires, aux/side classes on the
slot wires, childless exit edges on the R aux slots (R8 `blk1` exit shape). The class
STRUCTURE is D2-pinned; per-class multiplicities beyond these class instances enter only
the moment bridge (STUB 4) and are not separately claimed. -/
noncomputable def part1 : List NI := (List.range D2.v).map fun t => Instr.edge (ι (D2.wY t)) dataE

noncomputable def part2 : List NI :=
  Instr.edge (ι (D2.wS 0)) auxE :: sideRanks.map fun r => Instr.edge (ι (D2.wS (r + 1))) (sideE r)

def part3 : List NI := (List.range D2.Rslots).map fun s => Instr.edge (ι (D2.wS (s + 400))) dfltE

noncomputable def edgeSched : List NI := (part1 ++ part2) ++ part3

/-- The staircase witness-1 program: edge schedule first, then the d2OPS gates. -/
noncomputable def progS : List NI := edgeSched ++ d2Ops.flatMap gatesOf

/-- **The staircase witness-1 network** (W = 108516254 = D2.W, T = 3217907 = 46v + N, m = 529;
T resolution: Data.lean stairT / D2.T_eq). -/
noncomputable def netS : QHNet (ZMod 2) D2.W D2.Tmp 529 := ⟨progS, ρF⟩

theorem netS_T : D2.Tmp = 3217907 := rfl
theorem netS_W : D2.W = 108516254 := rfl

/-! ## RunsOK — PROVED (the deliverable) -/

theorem auxRunOK : ∀ ρ ∈ auxRuns 19, RunOK 529 ρ := by
  intro ρ hρ
  have h1 : ρ = (0, 506, 23) ∨ ρ = (23, 23, 483) := by
    simpa [auxRuns] using hρ
  rcases h1 with rfl | rfl
  · (unfold RunOK; decide)
  · (unfold RunOK; decide)

theorem sideRunOK (r : ℕ) (hr : r ≤ 23) : ∀ ρ ∈ sideRuns 23 529 r, RunOK 529 ρ := by
  unfold sideRuns
  by_cases hcond : 23 < 2 * r
  · rw [if_pos hcond]
    intro ρ hρ
    have hρ' : ρ = (23 - r, 529 - r, 2 * r - 23) := by simpa using hρ
    subst hρ'
    have e1 : (23 - r, 529 - r, 2 * r - 23).2.2 = 2 * r - 23 := rfl
    have e2 : (23 - r, 529 - r, 2 * r - 23).1 = 23 - r := rfl
    have e3 : (23 - r, 529 - r, 2 * r - 23).2.1 = 529 - r := rfl
    unfold RunOK
    refine ⟨Nat.sub_pos_of_lt hcond, by omega, by omega, by omega⟩
  · rw [if_neg hcond]
    intro ρ hρ
    exact absurd hρ (by simp)

/-- Edge classification for the schedule (R8 `prog_fam` pattern); the side class carries
its rank membership. -/
theorem prog_edges_fam : ∀ e ∈ QHNet.edges netS,
    e = dataE ∨ e = auxE ∨ (∃ r ∈ sideRanks, e = sideE r) ∨ e = dfltE := by
  intro e he
  obtain ⟨i, hi, hie⟩ := List.mem_filterMap.1 he
  have hp : netS.prog = progS := rfl
  rw [hp] at hi
  simp only [progS, edgeSched] at hi
  rcases List.mem_append.1 hi with h | h
  · -- i ∈ (part1 ++ part2) ++ part3
    rcases List.mem_append.1 h with h | h
    · -- i ∈ part1 ++ part2
      rcases List.mem_append.1 h with h | h
      · -- part1: the data-class edges
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 h
        have h4 : (Instr.edge (ι (D2.wY t)) dataE : NI).edgeOf = some dataE := rfl
        rw [h4] at hie
        exact Or.inl (Option.some.inj hie).symm
      · -- part2: the aux head, then the side-class edges
        rcases List.mem_cons.1 h with rfl | h
        · have h4 : (Instr.edge (ι (D2.wS 0)) auxE : NI).edgeOf = some auxE := rfl
          rw [h4] at hie
          exact Or.inr (Or.inl (Option.some.inj hie).symm)
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
          have h4 : (Instr.edge (ι (D2.wS (r + 1))) (sideE r) : NI).edgeOf = some (sideE r) := rfl
          rw [h4] at hie
          exact Or.inr (Or.inr (Or.inl ⟨r, hr, (Option.some.inj hie).symm⟩))
    · -- part3: the childless exit edges
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 h
      have h4 : (Instr.edge (ι (D2.wS (s + 400))) dfltE : NI).edgeOf = some dfltE := rfl
      rw [h4] at hie
      exact Or.inr (Or.inr (Or.inr (Option.some.inj hie).symm))
  · -- the d2OPS gates
    obtain ⟨op, hop, hiop⟩ := List.mem_flatMap.1 h
    have h0 := gatesOf_none op i hiop
    exact absurd (h0.symm.trans hie) (by simp)

theorem netS_RunsOK : netS.RunsOK := by
  intro e he ρ hρ
  rcases prog_edges_fam e he with rfl | rfl | ⟨r, hrm, rfl⟩ | rfl
  · exact dataE_runOK ρ hρ
  · rw [auxE_runs] at hρ; exact auxRunOK ρ hρ
  · have hr23 : r ≤ 23 := by
      have h : r ∈ List.range' 12 11 := by simpa [sideRanks] using hrm
      have h2 := List.mem_range'.1 h
      omega
    exact sideE_runOK r hr23 ρ hρ
  · exact absurd hρ (by simp [dfltE])

/-! ## EdgesOK at large prime powers — PROVED (good-prime clearance route)

Ported from the plain-line `Thm_net0Pnd_EdgesOK.lean` (proved there); generic in m. -/

/-- A finite size bound for all numerators and denominators in a rational matrix. -/
noncomputable def edgeQMatBound {m : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) : ℕ :=
  ∑ i, ∑ j, ((A i j).den + (A i j).num.natAbs)

/-- A finite good-prime clearance bound for the two Bruhat factors of an edge. -/
noncomputable def edgeQClearBound {m : ℕ} (e : Edge m) : ℕ :=
  edgeQMatBound e.E₁ + edgeQMatBound e.E₂

lemma den_le_edgeQMatBound {m : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) (i j : Fin m) :
    (A i j).den ≤ edgeQMatBound A := by
  calc
    (A i j).den ≤ (A i j).den + (A i j).num.natAbs := Nat.le_add_right _ _
    _ ≤ ∑ j, ((A i j).den + (A i j).num.natAbs) :=
      Finset.single_le_sum (f := fun j : Fin m => (A i j).den + (A i j).num.natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, ((A i j).den + (A i j).num.natAbs) :=
      Finset.single_le_sum (f := fun i : Fin m => ∑ j, ((A i j).den + (A i j).num.natAbs))
        (fun i _ => Nat.zero_le _) (Finset.mem_univ i)

lemma num_le_edgeQMatBound {m : ℕ} (A : Matrix (Fin m) (Fin m) ℚ) (i j : Fin m) :
    (A i j).num.natAbs ≤ edgeQMatBound A := by
  calc
    (A i j).num.natAbs ≤ (A i j).den + (A i j).num.natAbs := Nat.le_add_left _ _
    _ ≤ ∑ j, ((A i j).den + (A i j).num.natAbs) :=
      Finset.single_le_sum (f := fun j : Fin m => (A i j).den + (A i j).num.natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, ((A i j).den + (A i j).num.natAbs) :=
      Finset.single_le_sum (f := fun i : Fin m => ∑ j, ((A i j).den + (A i j).num.natAbs))
        (fun i _ => Nat.zero_le _) (Finset.mem_univ i)

/-- A nonzero rational whose numerator and denominator are coprime to `N`
reduces to a unit modulo `N`. -/
lemma isUnit_redQ_of_coprime {N : ℕ} {r : ℚ} (hr : r ≠ 0)
    (hd : Nat.Coprime r.den N) (hn : Nat.Coprime r.num.natAbs N) :
    IsUnit (redQ N r) := by
  have hinv : Nat.Coprime (r⁻¹).den N := by
    rw [Rat.den_inv, if_neg (Rat.num_ne_zero.mpr hr)]
    exact hn
  let x : goodSub N := ⟨r, hd⟩
  let y : goodSub N := ⟨r⁻¹, hinv⟩
  have hxy : x * y = 1 := by
    ext
    simp [x, y, hr]
  have hyx : y * x = 1 := by
    ext
    simp [x, y, hr]
  have hx : IsUnit x := ⟨⟨x, y, hxy, hyx⟩, rfl⟩
  have hm := hx.map (redHom N)
  simpa only [redQ, toGood, dif_pos hd, x] using hm

/-- One edge with rational Bruhat data is admissible at every prime power whose prime
exceeds `edgeQClearBound e` (the `edgeOK_large_of_edgeQ` body of the plain-line
`Thm_net0Pnd_EdgesOK.lean`, exposed at a fixed prime power). -/
theorem edgeOK_at_of_edgeQ {m : ℕ} (e : Edge m)
    (h : ∃ Q : Matrix (Fin m) (Fin m) ℚ, EdgeQ e Q)
    (q : ℕ) (hq : q.Prime) (hqb : edgeQClearBound e < q) (f : ℕ) : EdgeOK (q ^ f) e := by
  obtain ⟨Q, hQ⟩ := h
  have unit_of_bound : ∀ r : ℚ, r ≠ 0 → r.den ≤ edgeQClearBound e →
      r.num.natAbs ≤ edgeQClearBound e → IsUnit (redQ (q ^ f) r) := by
    intro r hr hd hn
    apply isUnit_redQ_of_coprime hr
    · exact (((hq.coprime_iff_not_dvd).2
        (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero r.den_nz)
          (lt_of_le_of_lt hd hqb))).symm.pow_right f)
    · exact (((hq.coprime_iff_not_dvd).2
        (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hr))
          (lt_of_le_of_lt hn hqb))).symm.pow_right f)
  have hU1 : ∀ i, IsUnit (redQ (q ^ f) (e.E₁ i i)) := fun i =>
    unit_of_bound _ (hQ.2.2.1 i)
      ((den_le_edgeQMatBound e.E₁ i i).trans (Nat.le_add_right _ _))
      ((num_le_edgeQMatBound e.E₁ i i).trans (Nat.le_add_right _ _))
  have hU2 : ∀ i, IsUnit (redQ (q ^ f) (e.E₂ i i)) := fun i =>
    unit_of_bound _ (hQ.2.2.2.2.1 i)
      ((den_le_edgeQMatBound e.E₂ i i).trans (Nat.le_add_left _ _))
      ((num_le_edgeQMatBound e.E₂ i i).trans (Nat.le_add_left _ _))
  exact ⟨hQ.2.1, hQ.2.2.2.1, hU1, hU2⟩

theorem foldr_max_bound {α : Type*} (g : α → ℕ) :
    ∀ (l : List α) (x : α), x ∈ l → g x ≤ (l.map g).foldr max 0
  | [], _, h => absurd h (by simp)
  | a :: l, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (foldr_max_bound g l x h).trans (Nat.le_max_right _ _)

/-- Uniform good-prime clearance over the net's edge schedule. -/
theorem netS_EdgesOK_large :
    ∃ q₀ : ℕ, ∀ q, q.Prime → q₀ < q → ∀ f : ℕ, netS.EdgesOK (q ^ f) := by
  refine ⟨edgeQClearBound dataE + edgeQClearBound auxE + edgeQClearBound dfltE +
    (sideRanks.map fun r => edgeQClearBound (sideE r)).foldr max 0, ?_⟩
  intro q hq hq₀ f e he
  rcases prog_edges_fam e he with rfl | rfl | ⟨r, hrm, rfl⟩ | rfl
  · exact edgeOK_at_of_edgeQ dataE ⟨_, dataE_EdgeQ⟩ q hq (by omega) f
  · exact edgeOK_at_of_edgeQ auxE ⟨_, auxE_EdgeQ⟩ q hq (by omega) f
  · have hr23 : r ≤ 23 := by
      have h : r ∈ List.range' 12 11 := by simpa [sideRanks] using hrm
      have h2 := List.mem_range'.1 h
      omega
    exact edgeOK_at_of_edgeQ (sideE r) ⟨_, sideE_EdgeQ r hr23⟩ q hq (by omega) f
  · exact edgeOK_at_of_edgeQ dfltE ⟨0, dfltE_EdgeQ⟩ q hq (by omega) f

/-! ## The moment bridge (D3) -/

/-- Edge power-sum moment: `EMq q e = ∑_{ρ ∈ e.runs} ρ.2.2 ^ q`. -/
def EMq (q : ℕ) (e : Edge 529) : ℕ := (e.runs.map fun ρ => ρ.2.2 ^ q).sum

theorem sum_flatMap {α : Type*} {M : Type*} [AddCommMonoid M] (f : α → List M) (l : List α) :
    (l.flatMap f).sum = (l.map fun x => (f x).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.map_cons, List.sum_append, ih, add_assoc]

theorem powSum_eq_edges (q : ℕ) :
    Mom.powSum q (QHNet.hist netS) = ((QHNet.edges netS).map fun e => EMq q e).sum := by
  have h1 : ∀ rs : List (ℕ × ℕ × ℕ),
      (((rs.map fun ρ => (ρ.2.2 : ℕ)).map fun w => (w, 1)).map
          fun p => p.2 * p.1 ^ q).sum = (rs.map fun ρ => ρ.2.2 ^ q).sum := by
    intro rs
    induction rs with
    | nil => simp
    | cons ρ rs ih =>
        simp only [List.map_cons, List.sum_cons, one_mul]
        rw [ih]
  have key : ∀ es : List (Edge 529),
      (((es.flatMap fun e => e.runs.map fun ρ => (ρ.2.2 : ℕ)).map fun w => (w, 1)).map
          fun p => p.2 * p.1 ^ q).sum = (es.map fun e => (e.runs.map fun ρ => ρ.2.2 ^ q).sum).sum := by
    intro es
    induction es with
    | nil => simp
    | cons e es ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
        rw [h1 e.runs, ih]
  show ((QHNet.hist netS).map (fun p => p.2 * p.1 ^ q)).sum = _
  rw [show QHNet.hist netS =
      ((QHNet.edges netS).flatMap fun e => e.runs.map fun ρ => (ρ.2.2 : ℕ)).map fun w => (w, 1)
      from rfl]
  exact key (QHNet.edges netS)

theorem EMq_data (E₁ E₂ : QMat2 529) (q : ℕ) :
    EMq q (Edge.mk E₁ D1 E₂) = 439 ^ q + 21 ^ q + 18 ^ q + 6 := by
  simp [EMq, D1, stairDataRuns_eval, stairSingles_eval]
  all_goals ring

theorem EMq_aux (E₁ E₂ : QMat2 529) (q : ℕ) :
    EMq q (Edge.mk E₁ (auxRuns 19) E₂) = 23 ^ q + 483 ^ q := by
  simp [EMq, auxRuns]
  all_goals ring

theorem EMq_side_pos (E₁ E₂ : QMat2 529) (q : ℕ) (r : ℕ) (hr : 23 < 2 * r) :
    EMq q (Edge.mk E₁ (sideRuns 23 529 r) E₂) = (2 * r - 23) ^ q := by
  simp [EMq, sideRuns, hr]

theorem EMq_side_neg (E₁ E₂ : QMat2 529) (q : ℕ) (r : ℕ) (hr : ¬ 23 < 2 * r) :
    EMq q (Edge.mk E₁ (sideRuns 23 529 r) E₂) = 0 := by
  simp [EMq, sideRuns, hr]

/-- Grouped-vs-expanded histogram moments agree (the `(w, n_w)` list and its
`n_w`-fold child expansion carry the same `histMoment`). -/
theorem histMoment_expansion (h : List (ℕ × ℕ)) (m : ℕ) (τ : ℝ) :
    IntMul.Kappa.histMoment (h.flatMap fun p => List.replicate p.2 (p.1, 1)) m τ =
      IntMul.Kappa.histMoment h m τ := by
  simp [IntMul.Kappa.histMoment, List.map_flatMap, sum_flatMap, List.map_replicate,
    List.sum_replicate, smul_eq_mul, mul_one]

/-- Grouped-vs-expanded histogram power sums agree — the D3 decidability shape. -/
theorem powSum_expansion (q : ℕ) (h : List (ℕ × ℕ)) :
    Mom.powSum q (h.flatMap fun p => List.replicate p.2 (p.1, 1)) = Mom.powSum q h := by
  simp [Mom.powSum, List.map_flatMap, sum_flatMap, List.map_replicate, List.sum_replicate,
    smul_eq_mul, mul_one]

/-- STUB 4 (moment/schedule multiplicity): the net's child-width multiset is `Jain.bitR7`
expanded. This is the producer readout-schedule port (deferred.py readout/V-gate structure
↔ d2HIST block structure — the multiplicity layer of the D2 dataset); the R8 line carried
the identical residual (NetMom `MomEqStmt`). Once discharged, `netS_powSum_eq` and
`netS_dominance` below close with NO further mathematics. -/
theorem netS_hist_eq :
    QHNet.hist netS = IntMul.Kappa.Jain.bitR7.flatMap fun p => List.replicate p.2 (p.1, 1) := by
  sorry

/-- **D3 bridge (the lane's target statement)**: `powSum q netHist = bitR7PowSum q` —
proved modulo STUB 4; kernel-decidable per q once the multiplicity layer pins the
per-class counts (the S₀/S₁ cross-ties below are the q = 0, 1 instances). -/
theorem netS_powSum_eq (q : ℕ) :
    Mom.powSum q (QHNet.hist netS) = Mom.bitR7PowSum q := by
  rw [netS_hist_eq]
  exact powSum_expansion q IntMul.Kappa.Jain.bitR7

/-- The leaf's moment clause, from the same single stub. -/
theorem netS_dominance (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    IntMul.Kappa.histMoment (QHNet.hist netS) 529 τ ≤
      IntMul.Kappa.histMoment IntMul.Kappa.Jain.bitR7 529 τ := by
  rw [netS_hist_eq]
  exact (histMoment_expansion IntMul.Kappa.Jain.bitR7 529 τ).le

/-- q = 0 cross-tie (zero new axioms: both sides kernel-pinned in D2Data/MomOracle). -/
theorem d2_childCount_eq_S0 : D2.d2HistChildCount = Mom.bitR7PowSum 0 := by
  rw [D2.d2HistChildCount_eq, Mom.bitR7S0]

/-- q = 1 cross-tie. -/
theorem d2_rankSum_eq_S1 : D2.d2HistRankSum = Mom.bitR7PowSum 1 := by
  rw [D2.d2HistRankSum_eq, Mom.bitR7S1]

/-! ## FormalOK — STUB 5 (Stage 2's frame-calculus port) -/

/-- STUB 5: `FormalOK` at every large prime power. Discharge route: the formal-frame
calculus (`formal_labels` / `genF_labGates` / `progH_correct`, platform-Proved for r6)
retargeted to the D2 gate schedule; the flag-basis half is `flagBasis_stair` (Rewire.lean,
PROVED). Included so the leaf assembly below is shape-complete. -/
theorem netS_FormalOK (q : ℕ) (hq : q.Prime) (f : ℕ) : netS.FormalOK (q ^ f) := by
  sorry

/-! ## The leaf, in the exact BitNetMomStmtG shape (modulo the five stubs above) -/

/-- Stage-1 assembly: the ∃-statement of `bitNetR7_mom` (e27d1a90) with
T = 3217907, C = netS — RunsOK and the EdgesOK clause PROVED (modulo the three
EdgeQ-existence stubs), FormalOK and the moment clause riding stubs 5 and 4. -/
theorem staircase_leaf_mod_stubs :
    ∃ (T : ℕ) (C : QHNet (ZMod 2) 108516254 T 529) (q₀ : ℕ),
      C.RunsOK ∧
      (∀ q, q.Prime → q₀ < q → ∀ f, C.EdgesOK (q ^ f) ∧ C.FormalOK (q ^ f)) ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
        IntMul.Kappa.histMoment C.hist 529 τ ≤
          IntMul.Kappa.histMoment IntMul.Kappa.Jain.bitR7 529 τ := by
  obtain ⟨q₀, hE⟩ := netS_EdgesOK_large
  refine ⟨3217907, netS, q₀, netS_RunsOK, ?_, netS_dominance⟩
  intro q hq hq₀ f
  exact ⟨hE q hq hq₀ f, netS_FormalOK q hq f⟩

end StaircasePort.QS
