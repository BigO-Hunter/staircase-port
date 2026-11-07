import Definitions.Def_IntMul_Kappa_R6_Defs4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# Stage 2 — the label generator engine, ported from the platform's Proved r6
`Thm_IntMul_Kappa_R6_Bit_genF_labGates` (prove2me_workspace, 259 ln, 0 sorry).

This is the LabGates ENGINE both dense-program label ports consume:

* `genF`/`genStepF`/`mvF` — the chunk generator on code states (inlined verbatim from the
  R8 QHNet inline of Defs51; `LInstr`/`LChunk`/`xorG`/`chunkInstrs`/`chunkProg` match
  `DenseProg.QD` shapes but are restated here so the module is self-contained vs Defs4
  and elaborates chain-free — the QD duplication collapses at the chain-landing pass).
* `genF_cons`/`genF_append` — the generator's structural lemmas.
* `moves_labels` — the per-instruction label carry: edges map the frame of the old code
  to the frame of the new code.
* **`genF_labGates`** — for chunks produced by `genF`, all gates are label consistent
  (`LabGates`) as soon as every move edge carries its labels; the final labels are the
  frames of the final codes; untouched wires keep their labels.

Fully generic (any Wr/R/m/N; wire domain `D` arbitrary) — the D2 dense program supplies
`ι`/`D`/`lab`/`E` per family; geometry-free, OFF the pending Corner→Projector→Rewire chain.

Proof: verbatim port of the platform's `genF_labGates_sol_aux` + its five helper lemmas
(`foldl_genStepF_acc`, `genF_append`, `genF_cons`, `labGates_append`, `labGates_edges`,
`foldl_mvF_acc`, `foldl_mvF_cons`, `foldl_mvF_state`, `moves_labels`). Every def consumed
(`LabGates/labStepH/edgeMat/Instr`) is Defs4.
-/

namespace StaircasePort.QL

open IntMul.Kappa.R6.Bit Matrix

/-! ## The chunk machinery (DenseProg.QD shapes; restated self-contained) -/

abbrev LInstr := ℕ × List ℕ × List (ℕ × ℕ)
abbrev LChunk := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

variable {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R] {m : ℕ}

/-- XOR gate `x_d ← x_d + x_s` (characteristic-2 shape at generic `R`; only its support
`{d, s}` is read by `LabGates`/`labStepH`). -/
def xorG (d s : Wr) : Instr Wr R m :=
  Instr.gate (fun x y => if x = y then (1 : R) else if x = d ∧ y = s then (1 : R) else (0 : R)) {d, s}

def chunkInstrs (ι : ℕ → Wr) (E : ℕ → ℕ → Edge m) (ch : LChunk) : List (Instr Wr R m) :=
  ch.2.1.map (fun mv => Instr.edge (ι mv.1) (E mv.2 ch.1)) ++
    ch.2.2.map fun p => xorG (ι p.1) (ι p.2)

def chunkProg (ι : ℕ → Wr) (E : ℕ → ℕ → Edge m) (cs : List LChunk) : List (Instr Wr R m) :=
  cs.flatMap (chunkInstrs ι E)

/-! ## The generator (R8 QHNet inline of Defs51) -/

def mvF (c : ℕ) (acc : (ℕ → ℕ) × List (ℕ × ℕ)) (w : ℕ) :
    (ℕ → ℕ) × List (ℕ × ℕ) :=
  if acc.1 w = c then acc
  else (Function.update acc.1 w c, (w, acc.1 w) :: acc.2)

def genStepF (acc : (ℕ → ℕ) × List LChunk) (i : LInstr) :
    (ℕ → ℕ) × List LChunk :=
  let r := i.2.1.foldl (mvF i.1) (acc.1, [])
  (r.1, (i.1, r.2.reverse, i.2.2) :: acc.2)

def genF (f : ℕ → ℕ) (W : List LInstr) : (ℕ → ℕ) × List LChunk :=
  let r := W.foldl genStepF (f, [])
  (r.1, r.2.reverse)

/-! ## Generator structure (r6 foldl_genStepF_acc / genF_append / genF_cons) -/

theorem foldl_genStepF_acc : ∀ (W : List LInstr) (f : ℕ → ℕ) (acc : List LChunk),
    W.foldl genStepF (f, acc) = ((W.foldl genStepF (f, [])).1, (W.foldl genStepF (f, [])).2 ++ acc)
  | [], f, acc => rfl
  | i :: W, f, acc => by
    simp only [List.foldl_cons, genStepF]
    rw [foldl_genStepF_acc W _ ((i.1, _, i.2.2) :: acc), foldl_genStepF_acc W _ [(i.1, _, i.2.2)]]
    simp

theorem genF_append (f : ℕ → ℕ) (W W' : List LInstr) :
    genF f (W ++ W') = ((genF (genF f W).1 W').1, (genF f W).2 ++ (genF (genF f W).1 W').2) := by
  simp only [genF, List.foldl_append]
  rw [foldl_genStepF_acc W' _ (W.foldl genStepF (f, [])).2]
  simp

theorem genF_cons (f : ℕ → ℕ) (i : LInstr) (W : List LInstr) :
    genF f (i :: W) = ((genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).1,
      (i.1, (i.2.1.foldl (mvF i.1) (f, [])).2.reverse, i.2.2) ::
        (genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).2) := by
  have := genF_append f [i] W
  simp only [List.singleton_append] at this
  rw [this]
  simp [genF, genStepF]

/-! ## LabGates structure (r6 labGates_append / labGates_edges) -/

variable (N : ℕ)

theorem labGates_append (p q : List (Instr Wr R m)) (L : Wr → FMat m N) :
    LabGates N (p ++ q) L ↔ LabGates N p L ∧ LabGates N q (p.foldl (labStepH N) L) := by
  induction p generalizing L with
  | nil => simp [LabGates]
  | cons i p ih =>
    simp only [List.cons_append, LabGates, List.foldl_cons]
    rw [ih]; tauto

theorem labGates_edges (l : List (Wr × Edge m)) (L : Wr → FMat m N) :
    LabGates N (l.map fun p => (Instr.edge p.1 p.2 : Instr Wr R m)) L := by
  induction l generalizing L with
  | nil => trivial
  | cons p l ih => exact ⟨trivial, ih _⟩

/-! ## The moved state (r6 foldl_mvF_acc / _cons / _state) -/

theorem foldl_mvF_acc (c : ℕ) : ∀ (ts : List ℕ) (g : ℕ → ℕ) (acc : List (ℕ × ℕ)),
    ts.foldl (mvF c) (g, acc) = ((ts.foldl (mvF c) (g, [])).1, (ts.foldl (mvF c) (g, [])).2 ++ acc)
  | [], g, acc => rfl
  | w :: ts, g, acc => by
    simp only [List.foldl_cons, mvF]
    split_ifs
    · exact foldl_mvF_acc c ts g acc
    · rw [foldl_mvF_acc c ts _ ((w, g w) :: acc), foldl_mvF_acc c ts _ [(w, g w)]]; simp

theorem foldl_mvF_cons (c : ℕ) (w : ℕ) (ts : List ℕ) (g : ℕ → ℕ) :
    (w :: ts).foldl (mvF c) (g, []) =
      if g w = c then ts.foldl (mvF c) (g, [])
      else ((ts.foldl (mvF c) (Function.update g w c, [])).1,
        (ts.foldl (mvF c) (Function.update g w c, [])).2 ++ [(w, g w)]) := by
  simp only [List.foldl_cons, mvF]
  split_ifs
  · rfl
  · exact foldl_mvF_acc c ts _ _

/-- The moved state: touched wires end at `c`, others keep their code. -/
theorem foldl_mvF_state (c : ℕ) : ∀ (ts : List ℕ) (g : ℕ → ℕ),
    (∀ w ∈ ts, (ts.foldl (mvF c) (g, [])).1 w = c) ∧
      ∀ w, w ∉ ts → (ts.foldl (mvF c) (g, [])).1 w = g w
  | [], g => ⟨by simp, fun _ _ => rfl⟩
  | w :: ts, g => by
    rw [foldl_mvF_cons]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := foldl_mvF_state c ts g
      refine ⟨fun x hx => ?_, fun x hx => h2 x (fun h' => hx (by simp [h']))⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · by_cases hxt : x ∈ ts
        · exact h1 x hxt
        · rw [h2 x hxt, h]
      · exact h1 x hx
    · obtain ⟨h1, h2⟩ := foldl_mvF_state c ts (Function.update g w c)
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · by_cases hxt : x ∈ ts
          · exact h1 x hxt
          · rw [h2 x hxt]; simp
        · exact h1 x hx
      · have hx' : x ∉ ts := fun h' => hx (by simp [h'])
        have hxw : x ≠ w := fun h' => hx (by simp [h'])
        rw [h2 x hx', Function.update_of_ne hxw]

/-! ## Per-instruction label carry (r6 moves_labels) -/

variable (ι : ℕ → Wr) (D : ℕ → Prop) (lab : ℕ → FMat m N) (E : ℕ → ℕ → Edge m)

/-- The edges of the moves of one instruction carry the labels along. -/
theorem moves_labels {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} {ι : ℕ → Wr} {D : ℕ → Prop} {lab : ℕ → FMat m N} {E : ℕ → ℕ → Edge m}
    (hι : ∀ w w', D w → D w' → ι w = ι w' → w = w') (c : ℕ) :
    ∀ (ts : List ℕ) (g : ℕ → ℕ) (L : Wr → FMat m N), (∀ w ∈ ts, D w) →
      (∀ mv ∈ (ts.foldl (mvF c) (g, [])).2, edgeMat N (E mv.2 c) * lab mv.2 = lab c) →
      (∀ w, D w → L (ι w) = lab (g w)) →
      let L' := ((ts.foldl (mvF c) (g, [])).2.reverse.map
        (fun mv => (Instr.edge (ι mv.1) (E mv.2 c) : Instr Wr R m))).foldl (labStepH N) L
      (∀ w, D w → L' (ι w) = lab ((ts.foldl (mvF c) (g, [])).1 w)) ∧
        ∀ x, (∀ w, D w → ι w ≠ x) → L' x = L x
  | [], g, L, _, _, hL => ⟨hL, fun _ _ => rfl⟩
  | w :: ts, g, L, hts, hE, hL => by
    have hw : D w := hts w (by simp)
    have hts' : ∀ x ∈ ts, D x := fun x hx => hts x (by simp [hx])
    rw [foldl_mvF_cons] at hE ⊢
    by_cases h : g w = c
    · rw [if_pos h] at hE ⊢
      exact moves_labels hι c ts g L hts' hE hL
    · rw [if_neg h] at hE ⊢
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.map_cons, List.foldl_cons]
      have hE1 : edgeMat N (E (g w) c) * lab (g w) = lab c := hE (w, g w) (by simp)
      have hE' : ∀ mv ∈ (ts.foldl (mvF c) (Function.update g w c, [])).2,
          edgeMat N (E mv.2 c) * lab mv.2 = lab c := fun mv hmv => hE mv (by simp [hmv])
      have hL1 : ∀ x, D x → labStepH N L (Instr.edge (ι w) (E (g w) c) : Instr Wr R m) (ι x) =
          lab (Function.update g w c x) := by
        intro x hx
        simp only [labStepH]
        by_cases hxw : x = w
        · subst hxw; simp [hL x hx, hE1]
        · rw [Function.update_of_ne (fun h' => hxw (hι x w hx hw h')), Function.update_of_ne hxw, hL x hx]
      obtain ⟨h1, h2⟩ := moves_labels (R := R) hι c ts (Function.update g w c) _ hts' hE' hL1
      refine ⟨h1, fun x hx => ?_⟩
      rw [h2 x hx]
      simp only [labStepH]
      rw [Function.update_of_ne (fun h' => hx w hw h'.symm)]

/-! ## Label consistency of generated chunks (r6 genF_labGates_sol_aux) -/

/-- **Label consistency of generated chunks.** For chunks produced by `genF`, all gates
are label consistent as soon as every move edge maps the frame of its old code to the
frame of its new code; the final labels are the frames of the final codes; untouched
wires keep their labels. -/
theorem genF_labGates {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {R : Type*} [CommRing R]
    {m N : ℕ} {ι : ℕ → Wr} {D : ℕ → Prop} {lab : ℕ → FMat m N} {E : ℕ → ℕ → Edge m}
    (hι : ∀ w w', D w → D w' → ι w = ι w' → w = w') :
    ∀ (W : List LInstr) (f : ℕ → ℕ) (L : Wr → FMat m N),
      (∀ i ∈ W, (∀ w ∈ i.2.1, D w) ∧ ∀ p ∈ i.2.2, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1) →
      (∀ ch ∈ (genF f W).2, ∀ mv ∈ ch.2.1, edgeMat N (E mv.2 ch.1) * lab mv.2 = lab ch.1) →
      (∀ w, D w → L (ι w) = lab (f w)) →
      LabGates N (chunkProg (R := R) ι E (genF f W).2) L ∧
        (∀ w, D w → (chunkProg (R := R) ι E (genF f W).2).foldl (labStepH N) L (ι w) =
          lab ((genF f W).1 w)) ∧
        ∀ x, (∀ w, D w → ι w ≠ x) → (chunkProg (R := R) ι E (genF f W).2).foldl (labStepH N) L x = L x
  | [], f, L, _, _, hL => ⟨trivial, hL, fun _ _ => rfl⟩
  | i :: W, f, L, hW, hE, hL => by
    rw [genF_cons] at hE ⊢
    have hi := hW i (by simp)
    have hW' : ∀ j ∈ W, (∀ w ∈ j.2.1, D w) ∧ ∀ p ∈ j.2.2, p.1 ∈ j.2.1 ∧ p.2 ∈ j.2.1 :=
      fun j hj => hW j (by simp [hj])
    set r := i.2.1.foldl (mvF i.1) (f, []) with hr
    have hEi : ∀ mv ∈ r.2, edgeMat N (E mv.2 i.1) * lab mv.2 = lab i.1 := fun mv hmv =>
      hE _ (List.mem_cons_self) mv (by simpa using hmv)
    have hEW : ∀ ch ∈ (genF r.1 W).2, ∀ mv ∈ ch.2.1, edgeMat N (E mv.2 ch.1) * lab mv.2 = lab ch.1 :=
      fun ch hch => hE ch (List.mem_cons_of_mem _ hch)
    obtain ⟨hm1, hm2⟩ := moves_labels (R := R) (N := N) hι i.1 i.2.1 f L hi.1 hEi hL
    set Lm := (r.2.reverse.map (fun mv => (Instr.edge (ι mv.1) (E mv.2 i.1) : Instr Wr R m))).foldl
      (labStepH N) L with hLm
    have hstate := foldl_mvF_state i.1 i.2.1 f
    -- gates of the instruction: labels equal (all touched wires at code `i.1`)
    have hgates : LabGates N (i.2.2.map fun p => (xorG (ι p.1) (ι p.2) : Instr Wr R m)) Lm ∧
        (i.2.2.map fun p => (xorG (ι p.1) (ι p.2) : Instr Wr R m)).foldl (labStepH N) Lm = Lm := by
      have : ∀ (l : List (ℕ × ℕ)), (∀ p ∈ l, p.1 ∈ i.2.1 ∧ p.2 ∈ i.2.1) →
          LabGates N (l.map fun p => (xorG (ι p.1) (ι p.2) : Instr Wr R m)) Lm ∧
            (l.map fun p => (xorG (ι p.1) (ι p.2) : Instr Wr R m)).foldl (labStepH N) Lm = Lm := by
        intro l hl
        induction l with
        | nil => exact ⟨trivial, rfl⟩
        | cons p l ih =>
          have hp := hl p (by simp)
          obtain ⟨ih1, ih2⟩ := ih (fun q hq => hl q (by simp [hq]))
          have heq : Lm (ι p.1) = Lm (ι p.2) := by
            rw [hm1 p.1 (hi.1 p.1 hp.1), hm1 p.2 (hi.1 p.2 hp.2), hstate.1 p.1 hp.1, hstate.1 p.2 hp.2]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro x hx y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [heq]
          · simpa [xorG, labStepH] using ih1
          · simpa [xorG, labStepH] using ih2
      exact this i.2.2 hi.2
    obtain ⟨ih1, ih2, ih3⟩ := genF_labGates (R := R) (N := N) hι W r.1 Lm hW' hEW hm1
    have hprog : chunkProg (R := R) ι E ((i.1, r.2.reverse, i.2.2) :: (genF r.1 W).2) =
        (r.2.reverse.map fun mv => (Instr.edge (ι mv.1) (E mv.2 i.1) : Instr Wr R m)) ++
          ((i.2.2.map fun p => (xorG (ι p.1) (ι p.2) : Instr Wr R m)) ++
            chunkProg (R := R) ι E (genF r.1 W).2) := by
      simp [chunkProg, chunkInstrs, List.flatMap_cons, List.append_assoc]
    rw [hprog]
    refine ⟨?_, ?_, ?_⟩
    · rw [labGates_append, labGates_append]
      have := labGates_edges (R := R) (N := N) (r.2.reverse.map fun mv => (ι mv.1, E mv.2 i.1)) L
      rw [List.map_map] at this
      refine ⟨this, hgates.1, ?_⟩
      rw [← hLm, hgates.2]; exact ih1
    · intro w hw
      rw [List.foldl_append, List.foldl_append, ← hLm, hgates.2]
      exact ih2 w hw
    · intro x hx
      rw [List.foldl_append, List.foldl_append, ← hLm, hgates.2, ih3 x hx, hm2 x hx]

end StaircasePort.QL
