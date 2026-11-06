import StaircasePort.Pivot

namespace StaircasePort.Stair

def stairRunA2 (r : ℕ) : ℚ := ((stairAZL.getD r 0 : ℤ) : ℚ)

-- goal inspection for the Fin literal
example (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ 21) : True := by
  have := (⟨l, by omega⟩ : Fin 23)
  trivial

example (l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ 21) :
    stairRunA2 l * stairQX2 ⟨l, by omega⟩ ≠ 0 := by
  trivial

end StaircasePort.Stair
