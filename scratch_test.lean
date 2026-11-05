import Definitions.Def_IntMul_Kappa_R6_Defs4

open IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB

def stairCornerRunsT (n m : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(1, m - n + 1, n - 2), (n + 2, m - 2 * n + 3, n - 5)]
def stairDataRunsT (n m : ℕ) : List (ℕ × ℕ × ℕ) :=
  (2 * n - 1, 2 * n - 1, m - 2 * (2 * n - 1)) :: stairCornerRunsT n m
def stairSinglesT (m : ℕ) : List (ℕ × ℕ × ℕ) :=
  [(0, m - 1, 1), (22, m - 23, 1), (23, m - 24, 1), (24, m - 25, 1), (43, m - 44, 1),
   (44, m - 45, 1)]

example : ∀ ρ ∈ stairDataRunsT 23 529 ++ stairSinglesT 529, RunOK 529 ρ := by
  intro ρ hρ
  simp only [stairDataRunsT, stairCornerRunsT, stairSinglesT, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false] at hρ
  exact hρ
