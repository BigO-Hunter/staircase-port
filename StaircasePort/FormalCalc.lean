import Definitions.Def_IntMul_Kappa_R6_Defs4

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# Stage 2 — the formal-frame calculus (`FormalOK` route), ported from the platform's
Proved r6 theorem `Thm_IntMul_Kappa_R6_Bit_formal_labels` (prove2me_workspace).

This is the REUSABLE LEMMA FAMILY the dense-program port plugs into:

* `lmulF_mul` — edge left-multiplications compose through the frame labels;
* `formal_labels` — on a program segment whose gates are label consistent
  (`LabGates N prog L`), formal values `L_w · φ_w` evolve as
  `L'_w · (scalar circuit on φ)_w`, where `L'` is tracked by `labStepH N` and the
  scalar circuit runs on module-valued wires (`scalarStepM`; the module of formal
  values). Edges act only on the labels; gates act only on the values.

Consumers (Stage 2, dense-program port): `fInit` decomposes as
`lmulF (L0 w) (φ0 w)` (single-term values), `formal_labels` then factors the whole
program run into the label track (`labStepH`) + the value track (`scalarStepM`),
and the per-role work is per-family label equations (`lab1/lab2` shapes) plus
per-family scalar identities (`sc_prog` shapes). Identical to the r6 proof spine —
only the wire geometry (NR = 28866, W = 108516254) and the certified edge/label
data differ.

Proof: verbatim port of the platform's `formal_labels_sol_aux` body (namespace +
import surface adjusted). Every def consumed (`FMat/FV/lmulF/gateVecM/scalarStepM/
fStep/labStepH/LabGates`) is Defs4.
-/

namespace StaircasePort.QF

open IntMul.Kappa.R6.Bit AModel AModelFac Matrix

section Formal

variable {R : Type*} [CommRing R] {U : Type*} {m N : ℕ}

lemma lmulF_mul (L L' : FMat m N) (φ : FV R U m N) :
    lmulF L (lmulF L' φ) = lmulF (L * L') φ := by
  simp only [lmulF, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext p
  simp [mul_assoc]

end Formal

section FormalRun

variable {R : Type*} [CommRing R] {m : ℕ} {Wr : Type*} [Fintype Wr] [DecidableEq Wr] {U : Type*}
  (N : ℕ)

/-- **Label-consistent segments.** If the gates of `prog` touch equal labels (from `L`),
formal values `L_w · φ_w` evolve as `L'_w · ψ_w`, with `L'` the tracked labels and `ψ`
the module-valued scalar circuit applied to `φ`. -/
theorem formal_labels : ∀ (prog : List (Instr Wr R m)) (L : Wr → FMat m N) (φ : Wr → FV R U m N),
    LabGates N prog L →
      prog.foldl (fStep N) (fun w => lmulF (L w) (φ w)) =
        fun w => lmulF (prog.foldl (labStepH N) L w) (prog.foldl scalarStepM φ w) := by
  intro prog
  induction prog with
  | nil => intro L φ _; rfl
  | cons i l ih =>
    intro L φ hlab
    simp only [List.foldl_cons]
    rw [← ih _ _ hlab.2]
    congr 1
    funext w
    cases i with
    | gate g S =>
      have hS := hlab.1
      simp only [fStep, scalarStepM, labStepH, gateVecM]
      split_ifs with hw
      · rw [map_sum]
        refine Finset.sum_congr rfl fun w' hw' => ?_
        rw [map_smul, hS w hw w' hw']
      · rfl
    | edge w0 e =>
      simp only [fStep, scalarStepM, labStepH]
      by_cases h : w = w0
      · subst h; simp [lmulF_mul]
      · rw [Function.update_of_ne h, Function.update_of_ne h]

/-- **The FormalOK consumer shape** (the r6 `formalOK_sol_aux` spine, abstracted).
If (1) `fInit` factors as `lmulF (L0 x) (φ0 x)` with single-term `φ0`, (2) the program's
gates are label-consistent for `L0`, and (3) per role-family the composed LABEL track
(`labStepH`) lands at `swapMat` while the composed VALUE track (`scalarStepM`) lands at
the role's own single term, then the network is formally correct. The dense-program port
supplies (3) per band through `DenseProg.gw_band_cases` + the ι-inverse lemmas. -/
theorem formalOK_of_tracks {W T : ℕ} (ρ : Fin W → Fin W)
    (prog : List (Instr (Fin W ⊕ Fin T) R m)) (L0 : (Fin W ⊕ Fin T) → FMat m N)
    (φ0 : (Fin W ⊕ Fin T) → FV R (Fin W) m N)
    (hf : QHNet.fInit (R := R) (W := W) (T := T) (m := m) N
        = fun x => lmulF (L0 x) (φ0 x))
    (hl1 : LabGates N prog L0)
    (hrho : ∀ w : Fin W,
      lmulF (prog.foldl (labStepH N) L0 (.inl (ρ w)))
        (prog.foldl scalarStepM φ0 (.inl (ρ w))) = Finsupp.single (swapMat, w) 1) :
    (QHNet.mk prog ρ : QHNet R W T m).FormalOK N := by
  intro w
  show (QHNet.mk prog ρ).prog.foldl (fStep N) (QHNet.fInit N)
    (.inl ((QHNet.mk prog ρ).ρ w)) = _
  rw [hf, formal_labels N prog L0 φ0 hl1]
  exact hrho w

end FormalRun

end StaircasePort.QF
