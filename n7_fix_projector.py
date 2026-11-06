prj_path = '/Users/dmitri.arkhipov/bigo-campaign/sp-corner/StaircasePort/Projector.lean'
prj = open(prj_path).read()
start = prj.index('/-! #### the projector-level clause (N7 rewire contract) -/')
end = prj.index('end StaircasePort.Stair')
section = '''/-! #### the projector-level clause (N7 rewire contract) -/

/-- **N7 — the NE-block rank transfer at corner positions**: for `X ≤ 45`, `Y ≤ 45` the
NE-block of the staircase projector at `(X, 484 + Y)` IS the NE-block of the corner
(the rows `< X ≤ 45` and the cols `≥ 484 + Y` are corner rows/cols, and the entries
match by `qMStair_corner`). -/
lemma n7_rk_qm (M : Matrix (Pr 23) (Pr 23) ℚ) (X Y : ℕ) (hX : X ≤ 45) (hY : Y ≤ 45) :
    rk (qMStair M) X (484 + Y) = rk (stairCornerQOf M) X Y := by
  rw [rk, rk]
  have hE : ((qMStair M).submatrix (fun r : {r : Fin 529 // r.val < X} => r.1)
        (fun c : {c : Fin 529 // 484 + Y ≤ c.val} => c.1)
      = (stairCornerQOf M).submatrix (fun r : {r : Fin 45 // r.val < X} => r.1)
        (fun c : {c : Fin 45 // Y ≤ c.val} => c.1)).submatrix
        (fun i => (⟨⟨i.1.val, by omega⟩, by omega⟩ :
          {r : Fin 45 // r.val < X}))
        (fun c => (⟨⟨c.1.val - 484, by omega⟩, by omega⟩ :
          {c : Fin 45 // Y ≤ c.val})) := by
    ext i j
    simp only [Matrix.submatrix_apply, stairCornerQOf, Matrix.of_apply]
    rw [show (↑j.1 : ℕ) = 529 - 45 + (j.1.val - 484) from by have := j.2; omega,
      qMStair_corner M (↑i.1) (j.1.val - 484) (by have := i.2; omega)
        (by have := j.1.isLt; omega)]
  have hE' : ((stairCornerQOf M).submatrix (fun r : {r : Fin 45 // r.val < X} => r.1)
        (fun c : {c : Fin 45 // Y ≤ c.val} => c.1)
      = (qMStair M).submatrix (fun r : {r : Fin 529 // r.val < X} => r.1)
        (fun c : {c : Fin 529 // 484 + Y ≤ c.val} => c.1)).submatrix
        (fun r => (⟨⟨r.1.val, by omega⟩, by omega⟩ :
          {r : Fin 529 // r.val < X}))
        (fun c => (⟨⟨484 + c.1.val, by omega⟩, by omega⟩ :
          {c : Fin 529 // 484 + Y ≤ c.val})) := by
    ext i j
    simp only [Matrix.submatrix_apply, stairCornerQOf, Matrix.of_apply]
    rw [show (484 + ↑c.1 : ℕ) = 529 - 45 + c.1.val from by omega,
      qMStair_corner M (↑r.1.val) c.1.val (by have := r.2; omega) (by have := c.1.isLt; omega)]
  exact le_antisymm
    (by rw [hE]; exact Matrix.rank_submatrix_le _ _ _)
    (by rw [hE']; exact Matrix.rank_submatrix_le _ _ _)

/-- **N7 — the pivot transfer**: a corner pivot is a projector pivot at the shifted
column (the four NE-block ranks transfer by `n7_rk_qm`). -/
theorem n7_isPiv_transfer (M : Matrix (Pr 23) (Pr 23) ℚ) (i j : ℕ) (hi : i < 45)
    (hj : j < 45) (h : IsPiv (stairCornerQOf M) i j) :
    IsPiv (qMStair M) i (484 + j) := by
  unfold IsPiv at h ⊢
  rw [n7_rk_qm M (i + 1) j (by omega) (by omega),
    n7_rk_qm M i j (by omega) (by omega),
    n7_rk_qm M (i + 1) (j + 1) (by omega) (by omega),
    n7_rk_qm M i (j + 1) (by omega) (by omega)]
  exact h

/-- **N7 — `isPiv_stairCorner`: the 39-position CORNER CLAUSE on the staircase
projector** (the statement the N7 rewire consumes; global coordinates, corner runs
(1,507,21) and (25,486,18) of `stairDataRuns 23 529`).

Hypotheses (all dischargeable at the extracted witness — see
`isPiv_stairCorner_witness`): `hu`, `hv`, the 21 run-1 diagonal deviations `hT`,
`hM1` (top 25 corner rows independent on cols ≥ 20; witness: N2c cert 1), and `hM2`
(row `25+t` independent on cols ≥ `2+t` for `t < 18`; witness: N2c's 26-certs).
Note: `h₁`/`h₂` (`y·x = 1`) and `hdet` are NOT needed here — they are the middle-run's
fuel (`isPiv_stairMid`). -/
theorem isPiv_stairCorner (x₁ y₁ x₂ y₂ : Fin 23 → ℚ)
    (hu : x₁ ⟨0, by omega⟩ * x₂ ⟨0, by omega⟩ ≠ 0)
    (hv : y₁ ⟨22, by omega⟩ * y₂ ⟨22, by omega⟩ ≠ 0)
    (hT : ∀ l, 1 ≤ l → l ≤ 21 →
      stairRunA l * x₂ (n7Fin l) * y₂ (n7Fin (l + 1))
        + stairRunB l * x₁ (n7Fin l) * y₁ (n7Fin (l + 1)) ≠ 0)
    (hM1 : 25 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) 25 20)
    (hM2 : ∀ t : ℕ, t < 18 →
      26 ≤ rk (stairCornerQOf (stairPairM x₁ y₁ x₂ y₂)) (26 + t) (2 + t)) :
    ∀ p ∈ runPairs [(1, 507, 21), (25, 486, 18)],
      IsPiv (qMStair (stairPairM x₁ y₁ x₂ y₂)) p.1 p.2 := by
  intro p hp
  rw [runPairs, List.mem_flatMap] at hp
  obtain ⟨ρ, hρ, hp2⟩ := hp
  obtain ⟨i, j, r⟩ := ρ
  rw [List.mem_cons, List.mem_cons, List.mem_nil] at hρ
  rcases hρ with rfl | rfl | hr
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    rw [show 507 + k = 484 + (23 + k) from by omega]
    exact n7_isPiv_transfer _ _ _ (by omega)
      (n7_run1 x₁ y₁ x₂ y₂ hu hv hT (1 + k) (by omega) (by omega))
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp2
    rw [show 486 + k = 484 + (2 + k) from by omega]
    exact n7_isPiv_transfer _ _ _ (by omega)
      (n7_run2 x₁ y₁ x₂ y₂ hM1 hM2 k hk)
  · exact absurd hr (by simp)

/-- **The 39 corner positions at the witness through the symbolic clause** — every
hypothesis discharged; the integration check for the N7 rewire. -/
theorem isPiv_stairCorner_witness :
    ∀ p ∈ runPairs [(1, 507, 21), (25, 486, 18)],
      IsPiv (qMStair (stairPairM stairQX1 stairQY1 stairQX2 stairQY2)) p.1 p.2 :=
  isPiv_stairCorner stairQX1 stairQY1 stairQX2 stairQY2 stair_hu stair_hv n7_hT_witness
    n7_hM1_witness n7_hM2_witness

'''
open(prj_path, 'w').write(prj[:start] + section + prj[end:].replace('end StaircasePort.Stair', '', 1).rstrip() + '\n\nend StaircasePort.Stair\n')
print("Projector section rewritten")
