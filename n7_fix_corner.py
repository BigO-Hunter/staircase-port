cd_path = '/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/Corner.lean'
cd = open(cd_path).read()

# (a) remove the duplicate stairRunA/stairRunB defs (they live in CornerData)
dup_defs = '''/-- The two-term column coefficients (Nat-indexed to match the extracted data). -/
def stairRunA (r : ℕ) : ℚ := ((stairAZL.getD r 0 : ℤ) : ℚ)
def stairRunB (r : ℕ) : ℚ := ((stairBZL.getD r 0 : ℤ) : ℚ)

'''
assert dup_defs in cd
cd = cd.replace(dup_defs, '', 1)

# (b) delete the dead M1/M2 index defs (rank-form hypotheses don't use them)
dead_start = cd.index('/-! #### the M1/M2 minor index functions -/')
dead_end = cd.index('/-- run-1 hBlo minor rows')
cd = cd[:dead_start] + cd[dead_end:]

# fix n7M1row-style proof bug in remaining defs (n7R2/n7C2/n7R1/n7C1 keep their by-omega)
cd = cd.replace('''/-- run-1 hBlo minor rows: `0` and `l`. -/''', '''/-- run-1 hBlo minor rows: `0` and `l`. -/''', 1)

# (c) fix the two membership-pin ranges
old_c1 = '''lemma n7_mem_C1 : ∀ l : ℕ, 2 ≤ l → l ≤ 21 → (l - 1, 23 + l, 1, 1) ∈ stairNEBlocks := by
  intro l _ _; interval_cases l <;> decide'''
new_c1 = '''lemma n7_mem_C1 : ∀ l : ℕ, 2 ≤ l → l ≤ 20 → (l - 1, 23 + l, 1, 1) ∈ stairNEBlocks := by
  intro l _ _; interval_cases l <;> decide'''
assert old_c1 in cd
cd = cd.replace(old_c1, new_c1, 1)

old_b2 = '''lemma n7_mem_B2 : ∀ t : ℕ, 1 ≤ t → t ≤ 17 → (25 + t, 2 + t, 26, 26) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide'''
new_b2 = '''lemma n7_mem_B2 : ∀ t : ℕ, 1 ≤ t → t ≤ 16 → (25 + t, 2 + t, 26, 26) ∈ stairNEBlocks := by
  intro t _ _; interval_cases t <;> decide'''
assert old_b2 in cd
cd = cd.replace(old_b2, new_b2, 1)

# (d1) run1's hC case-split: l=1 height; 2<=l<=20 table; l=21 width
old_hc = '''  · -- C ≤ 1
    rcases Nat.lt_or_ge l 2 with h | h
    · exact (rk_le_height _ l (23 + l)).trans (by omega)
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ l (23 + l) 1 1 (by omega) (n7_mem_C1 l h hl2)
      rwa [show l - 1 + 1 = l from by omega] at hb'''
new_hc = '''  · -- C ≤ 1
    rcases Nat.lt_or_ge l 2 with h | h
    · exact (rk_le_height _ l (23 + l)).trans (by omega)
    · rcases Nat.lt_or_ge l 21 with h' | h'
      · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ l (23 + l) 1 1 (by omega)
          (n7_mem_C1 l h (by omega))
        rwa [show l - 1 + 1 = l from by omega] at hb
      · exact (rk_le_width _ l (23 + l) (by omega)).trans (by omega)'''
assert old_hc in cd
cd = cd.replace(old_hc, new_hc, 1)

# (d2) run2's hB case-split: t=0 height; 1<=t<=16 table; t=17 width
old_hb2 = '''  · -- B ≤ 26
    rcases Nat.lt_or_ge t 1 with h | h
    · exact rk_le_height _ (26 + t) (2 + t)
    · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (26 + t) (2 + t) 26 26 (by omega)
        (n7_mem_B2 t h hle)
      rwa [show 26 + t - 1 = 25 + t from by omega] at hb'''
new_hb2 = '''  · -- B ≤ 26
    rcases Nat.lt_or_ge t 1 with h | h
    · exact rk_le_height _ (26 + t) (2 + t)
    · rcases Nat.lt_or_ge t 17 with h' | h'
      · have hb := rkQ_le_of_block_gen x₁ y₁ x₂ y₂ (26 + t) (2 + t) 26 26 (by omega)
          (n7_mem_B2 t h (by omega))
        rwa [show 26 + t - 1 = 25 + t from by omega] at hb
      · exact (rk_le_width _ (26 + t) (2 + t) (by omega)).trans (by omega)'''
assert old_hb2 in cd
cd = cd.replace(old_hb2, new_hb2, 1)

open(cd_path, 'w').write(cd)
print("Corner.lean fixes applied")
