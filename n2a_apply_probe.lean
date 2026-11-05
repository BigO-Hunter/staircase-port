/- N2a apply-probe: the EXACT term-mode shape N2b (stairNE_rk_le) consumes. All data is in
hypotheses here (no sorries); if this elaborates, rank_le_support_cut applies cleanly in term
mode at the 45x45 staircase corner. Cut sets R0/C0/T0 per block must come from regenerated
extracted data (NEBlocks.lean stores only cut VALUES). -/
import StaircasePort.Pivot

open StaircasePort.Stair
open Matrix Finset IntMul.Kappa.R6.Bit IntMul.Kappa.R6.Bit.NB

example (Mp : Matrix (Pr 23) (Pr 23) ℚ) (i j cut : ℕ)
    (R₀ : Finset (Fin 45)) (C₀ : Finset (Fin 45)) (T₀ : Finset (Fin 47))
    (Mt : Fin 47 → Matrix {r : Fin 45 // r.val < i + 1} {c : Fin 45 // j ≤ c.val} ℚ)
    (hsum : (stairCornerQOf Mp).submatrix (fun r : {r : Fin 45 // r.val < i + 1} => r.1)
        (fun c : {c : Fin 45 // j ≤ c.val} => c.1) = ∑ t, Mt t)
    (hcut : ∀ t ∉ T₀, (∀ r, r.1 ∉ R₀ → Mt t r = 0) ∨ (∀ c, c.1 ∉ C₀ → ∀ r, Mt t r c = 0))
    (hr1 : ∀ t ∈ T₀, (Mt t).rank ≤ 1)
    (hcard : R₀.card + C₀.card + T₀.card ≤ cut) :
    rk (stairCornerQOf Mp) (i + 1) j ≤ cut :=
  le_trans (rank_le_support_cut (stairCornerQOf Mp) (i + 1) j R₀ C₀ T₀ Mt hsum hcut hr1) hcard
