import StaircasePort.Pivot

namespace StaircasePort.Stair

-- minimal probe of the hT witness statement
theorem n7_probe_hT : ∀ l : ℕ, 1 ≤ l → l ≤ 21 →
    stairRunA l * stairQX2 ⟨l, by omega⟩ * stairQY2 ⟨l + 1, by omega⟩
      + stairRunB l * stairQX1 ⟨l, by omega⟩ * stairQY1 ⟨l + 1, by omega⟩ ≠ 0 := by
  intro l h1 h2
  sorry

-- what are the types here?
#check fun (l : ℕ) => stairQX2 ⟨l, by omega⟩
#check fun (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ 21) => stairQX2 ⟨l, by omega⟩

end StaircasePort.Stair
