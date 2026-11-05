import StaircasePort.Pivot

set_option maxHeartbeats 0

namespace StaircasePort.Stair

open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB
open scoped Kronecker
/-! ### N2c — the rightmost-pivot lower bound at the extracted witness (check_stair item 3)

`stairPC` is the extracted rightmost-pivot pattern (staircase_data.json `pc`), a permutation
of `0..44`; the corner runs are exactly its graph (`stairCornerRuns45_pairs`, kernel
`decide`). For row `i` the four NE blocks around `(i, pc i)` have

  A = rk q i (pc i) = k,     B = rk q (i+1) (pc i) = k+1,
  C = rk q i (pc i+1) = k,   D = rk q (i+1) (pc i+1) = k,   k = #{r < i | pc r ≥ pc i},

which is `IsPiv q i (pc i)` by `isPiv_of_bounds`. Uppers are trivial (`min(#rows,#cols)`) or
N2b's cut table (`rkQ_le_of_block`); lowers are explicit nonzero minors certified by a
modular inverse mod `stairCertP` (the N3 `certChk` mechanism) — `n2c_rank_lower`.
-/

/-- The extracted rightmost-pivot pattern: row `i`'s rightmost pivot is column `pc i`. -/
def stairPC : List ℕ := [44, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 22, 21, 20, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 1, 0]

/-- The extracted corner runs are exactly the graph of `stairPC` (as a set: `runPairs`
emits them in run order, not row order). -/
theorem stairCornerRuns45_toFinset :
    (runPairs stairCornerRuns45).toFinset
      = ((List.range 45).map (fun i => (i, stairPC.getD i 0))).toFinset := by
  decide

theorem stairCornerRuns45_mem {x : ℕ × ℕ} :
    x ∈ runPairs stairCornerRuns45 ↔
      x ∈ (List.range 45).map (fun i => (i, stairPC.getD i 0)) := by
  rw [← List.mem_toFinset, stairCornerRuns45_toFinset, List.mem_toFinset]

/-! #### generic rank lemmas -/

/-- NE-block rank is monotone in the row cut. -/
lemma rk_rows_mono {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    {X X' Y : ℕ} (h : X ≤ X') : rk q X Y ≤ rk q X' Y := by
  rw [rk, rk]
  have he : (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)) =
      (q.submatrix (fun r : {r : Fin a // r.val < X'} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)).submatrix
        (fun r : {r : Fin a // r.val < X} =>
          (⟨r.1, by have := r.2; omega⟩ : {r : Fin a // r.val < X'})) (fun c => c) := by
    ext i j
    rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _

/-- NE-block rank is monotone in the column cut (larger `Y` = smaller block). -/
lemma rk_cols_mono {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    {X Y Y' : ℕ} (h : Y' ≤ Y) : rk q X Y ≤ rk q X Y' := by
  rw [rk, rk]
  have he : (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y ≤ c.val} => c.1)) =
      (q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // Y' ≤ c.val} => c.1)).submatrix (fun r => r)
        (fun c : {c : Fin b // Y ≤ c.val} =>
          (⟨c.1, by have := c.2; omega⟩ : {c : Fin b // Y' ≤ c.val})) := by
    ext i j
    rfl
  rw [he]
  exact Matrix.rank_submatrix_le _ _ _

/-- Trivial height bound. -/
lemma rk_le_height {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) : rk q X Y ≤ X := by
  rw [rk]
  refine (Matrix.rank_le_card_height _).trans ?_
  have h := Fintype.card_le_of_embedding
    (α := {r : Fin a // r.val < X}) (β := Fin X)
    ⟨fun r => ⟨r.1.val, r.2⟩, fun u v huv => by
      simp only [Fin.mk.injEq] at huv
      exact Subtype.ext (Fin.ext huv)⟩
  simpa using h

/-- Trivial width bound. -/
lemma rk_le_width {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) (hY : Y ≤ b) : rk q X Y ≤ b - Y := by
  rw [rk]
  refine (Matrix.rank_le_card_width _).trans ?_
  have h := Fintype.card_le_of_embedding
    (α := {c : Fin b // Y ≤ c.val}) (β := Fin (b - Y))
    ⟨fun c => ⟨c.1.val - Y, by have := c.2; have := c.1.isLt; omega⟩, fun u v huv => by
      simp only [Fin.mk.injEq] at huv
      have h1 := u.2; have h2 := v.2
      exact Subtype.ext (Fin.ext (by omega))⟩
  simpa using h

/-- A nonzero `n × n` minor forces `n ≤` the NE-block rank. -/
lemma rk_ge_of_det {K : Type*} [Field K] {a b : ℕ} (q : Matrix (Fin a) (Fin b) K)
    (X Y : ℕ) {n_ : ℕ} (R : Fin n_ → {r : Fin a // r.val < X})
    (Cc : Fin n_ → {c : Fin b // Y ≤ c.val})
    (hdet : (Matrix.of fun i j => q (R i).1 (Cc j).1).det ≠ 0) : n_ ≤ rk q X Y := by
  have h1 : (Matrix.of fun i j => q (R i).1 (Cc j).1).rank = n_ := by
    rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin]
  have h2 : ((q.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
      (fun c : {c : Fin b // Y ≤ c.val} => c.1)).submatrix R Cc).rank =
      (Matrix.of fun i j => q (R i).1 (Cc j).1).rank := rfl
  rw [← h1, ← h2, rk]
  exact Matrix.rank_submatrix_le _ _ _

/-- `IsPiv` from four exact rank values. -/
lemma isPiv_of_exact {a b : ℕ} (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j = k) (hB : rk q (i+1) j = k+1)
    (hC : rk q i (j+1) = k) (hD : rk q (i+1) (j+1) = k) : IsPiv q i j := by
  unfold IsPiv
  rw [hA, hB, hC, hD]
  omega

/-- `IsPiv` from two-sided bounds. -/
lemma isPiv_of_bounds {a b : ℕ} (q : Matrix (Fin a) (Fin b) ℚ) (i j k : ℕ)
    (hA : rk q i j ≤ k) (hB : rk q (i+1) j ≤ k+1)
    (hC : rk q i (j+1) ≤ k) (hD : rk q (i+1) (j+1) ≤ k)
    (hBlo : k+1 ≤ rk q (i+1) j) (hClo : k ≤ rk q i (j+1)) : IsPiv q i j := by
  have hAe : rk q i j = k := le_antisymm hA (hClo.trans (rk_cols_mono q (by omega)))
  have hCe : rk q i (j+1) = k := le_antisymm hC hClo
  have hDe : rk q (i+1) (j+1) = k := le_antisymm hD (hClo.trans (rk_rows_mono q (by omega)))
  exact isPiv_of_exact q i j k hAe (le_antisymm hB hBlo) hCe hDe

/-- N2b's cut bound, restated for `stairCornerQ` at the table block `(X-1, Y)`. -/
lemma rkQ_le_of_block (X Y c r : ℕ) (hX : 1 ≤ X)
    (h : (X - 1, Y, r, c) ∈ stairNEBlocks) : rk stairCornerQ X Y ≤ c := by
  have hb := stairNE_rk_le stairQX1 stairQY1 stairQX2 stairQY2 (X - 1, Y, r, c) h
  simp only [stairCornerQ, stairMQ, stairPairM] at hb ⊢
  rwa [Nat.sub_add_cancel hX] at hb

/-- **The modular minor certificate as a rank lower bound.** `rl`/`cl` are the minor's
row/column indices, `rows` the minor mod `stairCertP` and `cols` the transpose of its
inverse mod `stairCertP` (the N3 `certChk` convention); `hent` pins `rows` against the
concrete corner entries. -/
lemma n2c_rank_lower {n_ X Y : ℕ} (hX : X ≤ 45) (rl cl : List ℕ)
    (hrl : ∀ i : Fin n_, rl.getD i.val 0 < X)
    (hcl : ∀ i : Fin n_, Y ≤ cl.getD i.val 0)
    (hclB : ∀ i : Fin n_, cl.getD i.val 0 < 45)
    (rows cols : List (List ℕ))
    (hchk : certChk rows cols n_ stairCertP = true)
    (hent : ((List.range n_).all fun i => (List.range n_).all fun j =>
      decide (corZStair stairMZ (rl.getD i 0) (cl.getD j 0) % (stairCertP : ℤ) =
        (((rows.getD i []).getD j 0 : ℕ) : ℤ))) = true) :
    n_ ≤ rk stairCornerQ X Y := by
  set Dz : Matrix (Fin n_) (Fin n_) ℤ :=
    Matrix.of fun i j => corZStair stairMZ (rl.getD i.val 0) (cl.getD j.val 0) with hDz
  have hentQ : (Matrix.of fun i j : Fin n_ =>
        stairCornerQ (⟨rl.getD i.val 0, by have := hrl i; omega⟩ : Fin 45)
          (⟨cl.getD j.val 0, hclB j⟩ : Fin 45)) =
      Dz.map (Int.cast : ℤ → ℚ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, hDz, stairCornerQ, stairCornerQOf,
      ← stairMZ_map, corStairQ_cast]
  have hdetQ : (Dz.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    have e1 : (Dz.map (Int.cast : ℤ → ℚ)).det = ((Dz.det : ℤ) : ℚ) := by
      have h := RingHom.map_det (Int.castRingHom ℚ) Dz
      rw [RingHom.mapMatrix_apply] at h
      exact h.symm
    rw [e1, Int.cast_ne_zero]
    intro h0
    have e2 := RingHom.map_det (Int.castRingHom (ZMod stairCertP)) Dz
    rw [RingHom.mapMatrix_apply, h0, map_zero] at e2
    have e3 : Dz.map (Int.castRingHom (ZMod stairCertP)) =
        Matrix.of fun i l : Fin n_ =>
          (((rows.getD i.val []).getD l.val 0 : ℕ) : ZMod stairCertP) := by
      ext i l
      rw [Matrix.map_apply, hDz, Matrix.of_apply, Matrix.of_apply, eq_intCast,
        ← ZMod.intCast_mod]
      have hc := hent
      simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
      rw [hc i.val i.isLt l.val l.isLt, Int.cast_natCast]
    rw [e3] at e2
    exact det_ne_zero_of_certChk rows cols hchk e2.symm
  refine rk_ge_of_det stairCornerQ X Y
    (fun i => ⟨⟨rl.getD i.val 0, by have := hrl i; omega⟩, hrl i⟩)
    (fun j => ⟨⟨cl.getD j.val 0, hclB j⟩, hcl j⟩) ?_
  have heq : (Matrix.of fun i j : Fin n_ => stairCornerQ
        ((⟨⟨rl.getD i.val 0, by have := hrl i; omega⟩, hrl i⟩ :
          {r : Fin 45 // r.val < X}).1)
        ((⟨⟨cl.getD j.val 0, hclB j⟩, hcl j⟩ : {c : Fin 45 // Y ≤ c.val}).1)) =
      (Matrix.of fun i j : Fin n_ => stairCornerQ
        (⟨rl.getD i.val 0, by have := hrl i; omega⟩ : Fin 45)
        (⟨cl.getD j.val 0, hclB j⟩ : Fin 45)) := rfl
  rw [heq, hentQ]
  exact hdetQ

/-- N2c minor certificate 0: rows [0], cols [44] (det mod P = 15495622). -/
def n2cR0 : List ℕ := [0]
def n2cC0 : List ℕ := [44]
def n2cS0 : List (List ℕ) := [[15495622]]
def n2cT0 : List (List ℕ) := [[29527921]]

/-- N2c minor certificate 1: rows [0, 1], cols [23, 24] (det mod P = 14891056). -/
def n2cR1 : List ℕ := [0, 1]
def n2cC1 : List ℕ := [23, 24]
def n2cS1 : List (List ℕ) := [[65097439, 31673818],
   [55442623, 31673818]]
def n2cT1 : List (List ℕ) := [[2074659, 65926728],
   [65034200, 48799886]]


theorem n2cChk0 : certChk n2cS0 n2cT0 1 stairCertP = true := by decide +kernel
theorem n2cEnt0 : ((List.range 1).all fun i => (List.range 1).all fun j =>
    decide (corZStair stairMZ (n2cR0.getD i 0) (n2cC0.getD j 0) % (stairCertP : ℤ) =
      (((n2cS0.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cChk1 : certChk n2cS1 n2cT1 2 stairCertP = true := by decide +kernel
theorem n2cEnt1 : ((List.range 2).all fun i => (List.range 2).all fun j =>
    decide (corZStair stairMZ (n2cR1.getD i 0) (n2cC1.getD j 0) % (stairCertP : ℤ) =
      (((n2cS1.getD i []).getD j 0 : ℕ) : ℤ))) = true := by decide +kernel

theorem n2cPiv0 : IsPiv stairCornerQ 0 (stairPC.getD 0 0) := by
  have hpc : stairPC.getD 0 0 = 44 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 0 44 0 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 0 44
  · exact rk_le_height stairCornerQ 1 44
  · exact rk_le_height stairCornerQ 0 45
  · refine rk_le_width stairCornerQ 1 45 (by decide)
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0
  · exact Nat.zero_le _

theorem n2cPiv1 : IsPiv stairCornerQ 1 (stairPC.getD 1 0) := by
  have hpc : stairPC.getD 1 0 = 23 := by decide
  rw [hpc]
  refine isPiv_of_bounds stairCornerQ 1 23 1 ?_ ?_ ?_ ?_ ?_ ?_
  · exact rk_le_height stairCornerQ 1 23
  · exact rk_le_height stairCornerQ 2 23
  · exact rk_le_height stairCornerQ 1 24
  · exact rkQ_le_of_block 2 24 1 1 (by decide) (by decide)
  · refine n2c_rank_lower (by decide) n2cR1 n2cC1 (by decide) (by decide) (by decide) n2cS1 n2cT1 n2cChk1 n2cEnt1
  · refine n2c_rank_lower (by decide) n2cR0 n2cC0 (by decide) (by decide) (by decide) n2cS0 n2cT0 n2cChk0 n2cEnt0

end StaircasePort.Stair
