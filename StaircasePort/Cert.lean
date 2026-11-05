/-
# N3 — kernel certificate for the staircase data corner + the staircase flag family

Mirrors nb_flagBasis_solution.lean:95-147 (Cert section: MZ / cert_chk / cert_entries /
MZ_map / data_cert over certChk, Defs4:1000) with:
* the r6 flag family LtermsZ/RtermsZ (Defs4:1004-1016 region) → the STAIRCASE family
  LtermsZStair/RtermsZStair below (check_stair.py:30-34 design(23,'stair') rows/cols,
  coefficients :164-165 with the extracted witness values stairAlZ/stairBeZ/stairAZL/stairBZL
  of StaircasePort/CertData.lean);
* the r6 witness labels wx*/wy* (Defs4:1008-1011) → the extracted staircase witness
  stairWX1L/stairWY1L/stairWX2L/stairWY2L (check_stair --ij point U = V = I + J,
  check_stair.py:157, seed 1, first sampled line pair, lifted to Z with y ⬝ x = 1 EXACT,
  extract/extract_cert.py fix_dot);
* the r6 cert prime 2³¹−1 (Defs4 certP) → stairCertP = 67108859 (check_stair.py:26).

Extraction evidence (extract/out/cert_data.json): det(45×45 staircase corner) ≠ 0 mod
stairCertP; certRows·certCols = 1 mod stairCertP in the r6 certChk convention
(nb_flagBasis_solution.lean:57-59); Z-corner ≡ check_stair corner mod P entrywise.

The generic certificate lemmas certChk_sound / det_ne_zero_of_certChk
(nb_flagBasis_solution.lean:57-93) are PROVEd there with full proofs, generic in
rows/cols/k/p — port verbatim when discharging stair_data_cert (proof route below).
-/

import Definitions.Def_IntMul_Kappa_R6_Defs4
import StaircasePort.CertData

namespace StaircasePort.Stair

open Matrix IntMul.Kappa.R6.Bit.NB
open scoped Kronecker

set_option maxRecDepth 20000
set_option maxHeartbeats 0
set_option Elab.async false

/-! ## The staircase flag family (integer version, mirroring LtermsZ/RtermsZ, Defs4) -/

/-- Staircase row family λ_i (check_stair.py:43 rows + :164 coefficients):
i < 22 → E(i,i); i = 22 → al·E(22,0) + be·E(0,22); i = 23 → E(0,3) (= RC[0],
check_stair.py:32); 24 ≤ i < 45 → E(i−22, i−24) (= RC[i−23] = (r+1, r−1), r = i−23). -/
def LtermsZStair (i : ℕ) : List (ℤ × Pr 23) :=
  if h1 : i < 22 then [(1, (⟨i, by omega⟩, ⟨i, by omega⟩))]
  else if i = 22 then
    [(stairAlZ, (⟨22, by omega⟩, ⟨0, by omega⟩)), (stairBeZ, (⟨0, by omega⟩, ⟨22, by omega⟩))]
  else if i = 23 then [(1, (⟨0, by omega⟩, ⟨3, by omega⟩))]
  else if h2 : i < 45 then [(1, (⟨i - 22, by omega⟩, ⟨i - 24, by omega⟩))]
  else []

/-- Staircase column family μ_j (check_stair.py:44 cols + :165 coefficients):
j < 20 → E(j+1,j+3) (= CC[j], check_stair.py:33); j = 20 → E(0,20); j = 21 → E(0,21);
22 ≤ j < 44 → a_{j−22}·E(j−22,j−21) + b_{j−22}·E(j−21,j−22); j = 44 → E(22,22). -/
def RtermsZStair (j : ℕ) : List (ℤ × Pr 23) :=
  if h1 : j < 20 then [(1, (⟨j + 1, by omega⟩, ⟨j + 3, by omega⟩))]
  else if j = 20 then [(1, (⟨0, by omega⟩, ⟨20, by omega⟩))]
  else if j = 21 then [(1, (⟨0, by omega⟩, ⟨21, by omega⟩))]
  else if h2 : j < 44 then
    [(stairAZL.getD (j - 22) 0, (⟨j - 22, by omega⟩, ⟨j - 21, by omega⟩)),
     (stairBZL.getD (j - 22) 0, (⟨j - 21, by omega⟩, ⟨j - 22, by omega⟩))]
  else if j = 44 then [(1, (⟨22, by omega⟩, ⟨22, by omega⟩))]
  else []

/-- Integer staircase corner entries — exact mirror of corZ (Defs4:990) at the staircase
family. -/
def corZStair (M : Matrix (Pr 23) (Pr 23) ℤ) (i j : ℕ) : ℤ :=
  ((RtermsZStair j).map fun t => ((LtermsZStair i).map fun s => s.1 * M s.2 t.2).sum * t.1).sum

/-! ## The witness (mirroring the Defs4 Cert section) -/

/-- Integer witness labels, Fin-indexed (mirroring wx1..wy2, Defs4:1008-1011). -/
def stairWX1 : Fin 23 → ℤ := fun i => stairWX1L.getD i 0
def stairWY1 : Fin 23 → ℤ := fun i => stairWY1L.getD i 0
def stairWX2 : Fin 23 → ℤ := fun i => stairWX2L.getD i 0
def stairWY2 : Fin 23 → ℤ := fun i => stairWY2L.getD i 0

/-- The staircase data pair matrix at the witness, over Z (mirroring MZ, Defs4:1014). -/
def stairMZ : Matrix (Pr 23) (Pr 23) ℤ :=
  (1 - vecMulVec stairWX1 stairWY1) ⊗ₖ (1 - vecMulVec stairWX2 stairWY2)

/-- The rational pair matrix (mirroring MZ_map's target, nb_flagBasis_solution.lean:112). -/
def stairMQ : Matrix (Pr 23) (Pr 23) ℚ :=
  (1 - vecMulVec stairQX1 stairQY1) ⊗ₖ (1 - vecMulVec stairQX2 stairQY2)

/-! ## Rational family and corner (mirroring Lterms_eq/cor, nb_flagBasis_solution.lean:30-42) -/

def LtermsStair (i : ℕ) : List (ℚ × Pr 23) :=
  (LtermsZStair i).map fun s => ((s.1 : ℚ), s.2)

def RtermsStair (j : ℕ) : List (ℚ × Pr 23) :=
  (RtermsZStair j).map fun s => ((s.1 : ℚ), s.2)

/-- Rational staircase corner entries — mirror of cor (Defs4:942) at the staircase family.
This is the corner whose nondegeneracy the flagBasis data clause consumes (the qM-corner
identity Cp i j = cor M i j of nb_data_edge_solution.lean:534-537 ports verbatim with
Lterms/Rterms → LtermsStair/RtermsStair). -/
def corStairQ (M : Matrix (Pr 23) (Pr 23) ℚ) (i j : ℕ) : ℚ :=
  ((RtermsStair j).map fun t => ((LtermsStair i).map fun s => s.1 * M s.2 t.2).sum * t.1).sum

/-- The symbolic 45×45 staircase corner of a pair matrix (N2's rank statements live here). -/
def stairCornerQOf (M : Matrix (Pr 23) (Pr 23) ℚ) : Matrix (Fin 45) (Fin 45) ℚ :=
  Matrix.of fun i j => corStairQ M i.val j.val

/-- The witness corner over Z (certificate source) and over Q (pivot source). -/
def stairCornerZ : Matrix (Fin 45) (Fin 45) ℤ :=
  Matrix.of fun i j => corZStair stairMZ i.val j.val

def stairCornerQ : Matrix (Fin 45) (Fin 45) ℚ := stairCornerQOf stairMQ

/-! ## Generic certificate lemmas — verbatim ports of nb_flagBasis_solution.lean:46-93
(proved there with full proofs; generic in rows/cols/k/p — this file's header instructs
porting them verbatim when discharging stair_data_cert). -/

lemma dotL_eq {R : Type*} [CommRing R] : ∀ (a b : List ℕ) (hab : a.length = b.length),
    ((dotL a b : ℕ) : R) = ∑ l : Fin a.length, ((a.getD l 0 : ℕ) : R) * ((b.getD l 0 : ℕ) : R)
  | [], [], _ => by simp [dotL]
  | a :: as, b :: bs, hab => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hab
    rw [dotL, Nat.cast_add, Nat.cast_mul, dotL_eq as bs hab]
    simp only [List.length_cons, Fin.sum_univ_succ, Fin.val_zero, List.getD_cons_zero,
      Fin.val_succ, List.getD_cons_succ]
  | [], _ :: _, hab => by simp at hab
  | _ :: _, [], hab => by simp at hab

lemma certChk_sound (rows cols : List (List ℕ)) (k p : ℕ) (hc : certChk rows cols k p = true) :
    (Matrix.of fun i l : Fin k => (((rows.getD i []).getD l 0 : ℕ) : ZMod p)) *
      (Matrix.of fun l j : Fin k => (((cols.getD j []).getD l 0 : ℕ) : ZMod p)) = 1 := by
  simp only [certChk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hr, hcl⟩, hrl⟩, hcll⟩, hall⟩ := hc
  ext i j
  have hri : (rows.getD i []).length = k := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hrl _ (List.getElem_mem _)
  have hcj : (cols.getD j []).length = k := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcll _ (List.getElem_mem _)
  have h1 := dotL_eq (R := ZMod p) (rows.getD i []) (cols.getD j []) (hri.trans hcj.symm)
  have h2 := hall i i.isLt j j.isLt
  rw [Matrix.mul_apply]
  simp only [of_apply]
  have h3 : ((dotL (rows.getD i []) (cols.getD j []) : ℕ) : ZMod p) =
      ((if (i : ℕ) = j then 1 else 0 : ℕ) : ZMod p) := by
    rw [← ZMod.natCast_mod, h2]
  rw [h1] at h3
  have h4 : (∑ l : Fin (rows.getD i []).length,
      (((rows.getD i []).getD l 0 : ℕ) : ZMod p) * (((cols.getD j []).getD l 0 : ℕ) : ZMod p)) =
      ∑ l : Fin k, (((rows.getD i []).getD l 0 : ℕ) : ZMod p) *
        (((cols.getD j []).getD l 0 : ℕ) : ZMod p) := by
    rw [hri]
  rw [h4] at h3
  rw [h3, Matrix.one_apply]
  by_cases e : i = j
  · subst e; simp
  · rw [if_neg (fun h => e (Fin.ext h)), if_neg e]; simp

lemma det_ne_zero_of_certChk {k p : ℕ} [Fact (1 < p)] (rows cols : List (List ℕ))
    (hc : certChk rows cols k p = true) :
    (Matrix.of fun i l : Fin k => (((rows.getD i []).getD l 0 : ℕ) : ZMod p)).det ≠ 0 := by
  have h := congrArg Matrix.det (certChk_sound rows cols k p hc)
  rw [det_mul, det_one] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-! ## The staircase analogue of cor_cast (nb_flagBasis_solution.lean:38-42).
LtermsStair/RtermsStair are DEFINED as the ℚ-maps of the Z families here, so the port
needs no Lterms_eq/Rterms_eq rewrite step — just the unfolds. -/

lemma corStairQ_cast (M : Matrix (Pr 23) (Pr 23) ℤ) (i j : ℕ) :
    corStairQ (M.map (Int.cast : ℤ → ℚ)) i j = (corZStair M i j : ℚ) := by
  unfold corStairQ corZStair LtermsStair RtermsStair
  simp only [List.map_map, Function.comp_def, Int.cast_list_sum, Int.cast_mul, map_apply]

/-! ## N3 statements (each mirrors the cited r6 lemma; routes are the r6 proofs verbatim) -/

/-- **N3-1** (mirror of qxy1, nb_flagBasis_solution.lean:104-106). Route: simp [dotProduct]
+ norm_num on the literal lists — extract_cert.py verified dot(y1,x1) = 1 EXACTLY over Z. -/
theorem stairQxy1 : stairQY1 ⬝ᵥ stairQX1 = 1 := by decide +kernel

/-- **N3-2** (mirror of qxy2, nb_flagBasis_solution.lean:108-110). -/
theorem stairQxy2 : stairQY2 ⬝ᵥ stairQX2 = 1 := by decide +kernel

/-- **N3-3** (mirror of MZ_map, nb_flagBasis_solution.lean:112-118). Route: ext + simp
[stairMZ, stairMQ, stairQX1, stairWX1, ...] + push_cast, verbatim pattern. -/
theorem stairMZ_map : stairMZ.map (Int.cast : ℤ → ℚ) = stairMQ := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [stairMZ, stairMQ, map_apply, kronecker_apply, Matrix.sub_apply, vecMulVec_apply,
    Matrix.one_apply, stairWX1, stairWY1, stairWX2, stairWY2, stairQX1, stairQY1, stairQX2,
    stairQY2]
  push_cast
  split_ifs <;> simp

/-- **N3-4** (mirror of cert_chk, nb_flagBasis_solution.lean:97). Route: `decide +kernel`;
extract_cert.py verified stairCertRows · stairCertCols = 1 mod stairCertP. -/
theorem stair_cert_chk : certChk stairCertRows stairCertCols 45 stairCertP = true := by
  decide +kernel

/-- **N3-5** (mirror of cert_entries, nb_flagBasis_solution.lean:99-102). Route:
`decide +kernel`; entries ≤ 36 digits (cert_data.json cornerZ_entry_sizes) — heavier than
r6's small-int witness but same mechanism; if kernel time is a problem, reduce entries mod
stairCertP first (they already are) and/or switch to the r6-style small-label search
(SCAFFOLD.md N3 note). -/
theorem stair_cert_entries : ((List.range 45).all fun i => (List.range 45).all fun j =>
    decide (corZStair stairMZ i j % (stairCertP : ℤ) =
      (((stairCertRows.getD i []).getD j 0 : ℕ) : ℤ))) = true := by
  decide +kernel

/-- **N3-6 — the kernel-cert nonvanishing target** (mirror of data_cert,
nb_flagBasis_solution.lean:121-147): the 45×45 staircase data corner is invertible at the
witness. Route: the r6 proof verbatim — hD (cor_cast pattern :123-128 with
LtermsZStair/RtermsZStair ↔ LtermsStair/RtermsStair, needs the stair analogue of Lterms_eq
:30-36), e1 RingHom.map_det (Int.castRingHom ℚ), e2 reduction mod stairCertP, e3 via
stair_cert_entries, then det_ne_zero_of_certChk (PROVED, nb_flagBasis_solution.lean:86-93,
generic — port verbatim) with stair_cert_chk. Consumed by flagBasis_stair's hcert
(nb_flag_gen_solution.lean:956-971 shape). -/
theorem stair_data_cert :
    (Matrix.of fun i j : Fin 45 => corStairQ stairMQ i.val j.val).det ≠ 0 := by
  have hD : (Matrix.of fun i j : Fin 45 => corStairQ stairMQ i.val j.val) =
      (Matrix.of fun i j : Fin 45 => corZStair stairMZ i.val j.val).map (Int.cast : ℤ → ℚ) := by
    ext i j
    rw [← stairMZ_map, of_apply, corStairQ_cast]; rfl
  rw [hD]
  set Dz := Matrix.of fun i j : Fin 45 => corZStair stairMZ i.val j.val with hDz
  have e1 : (Dz.map (Int.cast : ℤ → ℚ)).det = ((Dz.det : ℤ) : ℚ) := by
    have := RingHom.map_det (Int.castRingHom ℚ) Dz
    rw [RingHom.mapMatrix_apply] at this
    exact this.symm
  rw [e1, Int.cast_ne_zero]
  intro h0
  have e2 := RingHom.map_det (Int.castRingHom (ZMod stairCertP)) Dz
  rw [RingHom.mapMatrix_apply, h0, map_zero] at e2
  have e3 : Dz.map (Int.castRingHom (ZMod stairCertP)) =
      Matrix.of fun i l : Fin 45 => (((stairCertRows.getD i []).getD l 0 : ℕ) : ZMod stairCertP) := by
    ext i l
    have hc := stair_cert_entries
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
    have := hc i i.isLt l l.isLt
    rw [map_apply, hDz, of_apply, of_apply, eq_intCast, ← ZMod.intCast_mod, this,
      Int.cast_natCast]
  rw [e3] at e2
  exact det_ne_zero_of_certChk stairCertRows stairCertCols stair_cert_chk e2.symm

end StaircasePort.Stair
