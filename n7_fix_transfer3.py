cd_path = '/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/CornerData.lean'
cd = open(cd_path).read()
cut = cd.index('lemma n7_rk_block')
transfer = '''/-- NE-block ranks transfer through a top-left block reindexing: `B` is `C`'s rows
`0..a'-1` and cols `c0..c0+b'-1`, so the NE blocks agree and so do the ranks. -/
lemma n7_rk_block {a b a' b' c0 X Y : ℕ} (C : Matrix (Fin a) (Fin b) ℚ)
    (B : Matrix (Fin a') (Fin b') ℚ) (ha : a' ≤ a) (hb : c0 + b' = b) (hX : X ≤ a')
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C (⟨i.val, by omega⟩ : Fin a) (⟨c0 + j.val, by omega⟩ : Fin b)) :
    rk C X (c0 + Y) = rk B X Y := by
  rw [rk, rk]
  -- the row/col reindexings as plain functions (term proofs: no omega atom games)
  have fr : {r : Fin a' // r.val < X} → {r : Fin a // r.val < X} :=
    fun r => ⟨⟨r.1.val, lt_of_lt_of_le r.2 (le_trans hX ha)⟩, r.2⟩
  have fc : {c : Fin b' // Y ≤ c.val} → {c : Fin b // c0 + Y ≤ c.val} :=
    fun c => ⟨⟨c0 + c.1.val, (Nat.add_lt_add_left c.1.isLt c0).trans_le (le_of_eq hb)⟩,
      Nat.add_le_add_left c.2 c0⟩
  have fr' : {r : Fin a // r.val < X} → {r : Fin a' // r.val < X} :=
    fun r => ⟨⟨r.1.val, lt_of_lt_of_le r.2 hX⟩, r.2⟩
  have fc' : {c : Fin b // c0 + Y ≤ c.val} → {c : Fin b' // Y ≤ c.val} :=
    fun c => ⟨⟨c.1.val - c0, lt_of_le_of_lt (Nat.sub_le c.1.val c0) c.1.isLt⟩,
      (Nat.add_le_add_left c.2 c0).trans_eq hb⟩
  have hSB : (B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
        (fun c : {c : Fin b' // Y ≤ c.val} => c.1)
      = (C.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // c0 + Y ≤ c.val} => c.1)).submatrix fr fc) := by
    ext r c
    simp only [Matrix.submatrix_apply]
    exact hCB r.1 c.1
  have hSC : ((C.submatrix (fun r : {r : Fin a // r.val < X} => r.1)
        (fun c : {c : Fin b // c0 + Y ≤ c.val} => c.1))
      = (B.submatrix (fun r : {r : Fin a' // r.val < X} => r.1)
        (fun c : {c : Fin b' // Y ≤ c.val} => c.1)).submatrix fr' fc') := by
    ext r c
    simp only [Matrix.submatrix_apply]
    rw [← hCB (⟨r.1.val, lt_of_lt_of_le r.2 hX⟩ : Fin a')
      (⟨c.1.val - c0, lt_of_le_of_lt (Nat.sub_le c.1.val c0) c.1.isLt⟩ : Fin b')]
    congr 1
    · rfl
    · exact congrArg Fin.val (Fin.ext (by have := c.2; omega))
  exact le_antisymm
    (by rw [hSC]; exact Matrix.rank_submatrix_le _ _)
    (by rw [hSB]; exact Matrix.rank_submatrix_le _ _)

/-- **`isPiv_block` (ported from nb_data_edge_solution.lean:227-238)**: a pivot of the
top-left block `B` is a pivot of `C` at the shifted column. -/
lemma n7_isPiv_block {a b a' b' c0 : ℕ} (C : Matrix (Fin a) (Fin b) ℚ)
    (B : Matrix (Fin a') (Fin b') ℚ) (ha : a' ≤ a) (hb : c0 + b' = b)
    (hCB : ∀ (i : Fin a') (j : Fin b'),
      B i j = C (⟨i.val, by omega⟩ : Fin a) (⟨c0 + j.val, by omega⟩ : Fin b))
    {i j : ℕ} (hi : i < a') (h : IsPiv B i j) : IsPiv C i (c0 + j) := by
  unfold IsPiv at h ⊢
  rw [show c0 + j + 1 = c0 + (j + 1) from by omega,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB,
    n7_rk_block C B ha hb (by omega) hCB]
  exact h

end StaircasePort.Stair
'''
open(cd_path, 'w').write(cd[:cut] + transfer)
print("transfer v3 written")
