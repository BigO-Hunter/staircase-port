/-! ## PLATFORM STUBS (wave-3 follow-up: replace each by an import at submission)

The ported `flag_gen` body consumes three generic Proved platform children whose statements are
verbatim below, specialized to h = 19 (ids + fetched bodies committed in ref/):

| stub | platform theorem | id | fetched body |
|---|---|---|---|
| `aux_edge_of` | IntMul.Kappa.R6.Bit.NB.aux_edge_of | c973e50d-124a-489e-b0fd-ac3804a68d0b | ref/nb_aux_edge_of_solution.lean:561 |
| `side_edge_of` | IntMul.Kappa.R6.Bit.NB.side_edge_of | f2e5b569-5d59-4157-8761-498f52b51299 | ref/nb_side_edge_of_solution.lean:196 |
| `idem_similar` | IntMul.Kappa.R6.Bit.NB.idem_similar | be86910c-e063-49cb-8700-1d314cebf2de | ref/nb_idem_similar_solution.lean:52 |

Porting them is mechanical but pulls a further generic chain (`edge_exact`,
`isPiv_diag_of_lower`, `isPiv_block`, `isPiv_mid` — the last already a `Platform` stub in
Pivot.lean); the bodies are in ref/ so no re-fetch is needed.

`aux_edge_of`: the aux-class edge at a generic pair matrix `M` with the Bruhat corner shape. -/
theorem aux_edge_of (M : Matrix (Pr (19 + 4)) (Pr (19 + 4)) ℚ) (hM : M * M = M)
    (htr : M.trace = ((19 + 4) * (19 + 3) : ℕ))
    (hlow : ∀ β γ : ℕ, β < γ → γ < 19 + 4 → cor M β (19 + 3 + γ) = 0)
    (hdiag : ∀ β : ℕ, β < 19 + 4 → cor M β (19 + 3 + β) ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM M) ∧
      e.runs = [(0, (19 + 4) * (19 + 4) - (19 + 4), 19 + 4),
        (19 + 4, 19 + 4, (19 + 4) * (19 + 4) - 2 * (19 + 4))] := by
  sorry

/-- `side_edge_of`: the side-class edge of rank `r` at a factorized pair matrix `C * A * R`. -/
theorem side_edge_of (C : Matrix (Pr (19 + 4)) (Fin (19 + 4)) ℚ)
    (A : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) (R : Matrix (Fin (19 + 4)) (Pr (19 + 4)) ℚ)
    (hB : ∀ i j : Fin (19 + 4), i < j →
      (Te (h := 19) * C) ⟨i.val, by have := two_k_le (h := 19); omega⟩ j = 0)
    (hBd : ∀ i : Fin (19 + 4),
      (Te (h := 19) * C) ⟨i.val, by have := two_k_le (h := 19); omega⟩ i ≠ 0)
    (hA : ∀ i j : Fin (19 + 4), i < j → (R * Te' (h := 19)) i
      ⟨(19 + 4) * (19 + 4) - (19 + 4) + j.val, by have := two_k_le (h := 19); omega⟩ = 0)
    (hAd : ∀ i : Fin (19 + 4), (R * Te' (h := 19)) i
      ⟨(19 + 4) * (19 + 4) - (19 + 4) + i.val, by have := two_k_le (h := 19); omega⟩ ≠ 0)
    (hM : C * A * R * (C * A * R) = C * A * R) (hAA : A * A = A) (r : ℕ) (hr : A.rank = r)
    (hrM : (qM (C * A * R)).rank = r)
    (hcor : 19 + 4 < 2 * r →
      (A.submatrix (fun l : Fin (19 + 4 - r) => (⟨l.val, by omega⟩ : Fin (19 + 4)))
        (fun c : Fin (19 + 4 - r) => (⟨19 + 4 - (19 + 4 - r) + c.val, by omega⟩ :
          Fin (19 + 4)))).det ≠ 0) :
    ∃ e : Edge ((19 + 4) * (19 + 4)), EdgeQ e (qM (C * A * R)) ∧ ∃ rs',
      e.runs = sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r ++ rs' ∧ (∀ ρ ∈ rs', ρ.2.2 = 1) ∧
      (runPairs (sideRuns (19 + 4) ((19 + 4) * (19 + 4)) r)).length + rs'.length = r := by
  sorry

/-- `idem_similar`: idempotents of equal rank are similar — PORTED verbatim from the platform
body (ref/nb_idem_similar_solution.lean, submission 92d6f177 of
IntMul.Kappa.R6.Bit.NB.idem_similar, Proved be86910c-e063-49cb-8700-1d314cebf2de); so this
platform child needs NO stub. -/
theorem h50i_conj {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (f g : E →ₗ[ℚ] E) (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (hr : Module.finrank ℚ (LinearMap.range f) = Module.finrank ℚ (LinearMap.range g)) :
    ∃ φ : E ≃ₗ[ℚ] E, φ.toLinearMap ∘ₗ f = g ∘ₗ φ.toLinearMap := by
  have hk : Module.finrank ℚ (LinearMap.ker f) = Module.finrank ℚ (LinearMap.ker g) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 := LinearMap.finrank_range_add_finrank_ker g
    omega
  let e1 := LinearEquiv.ofFinrankEq _ _ hr
  let e2 := LinearEquiv.ofFinrankEq _ _ hk
  have cf := LinearMap.IsIdempotentElem.isCompl hf
  have cg := LinearMap.IsIdempotentElem.isCompl hg
  let PA := (LinearMap.range f).prodEquivOfIsCompl (LinearMap.ker f) cf
  let PB := (LinearMap.range g).prodEquivOfIsCompl (LinearMap.ker g) cg
  let φ : E ≃ₗ[ℚ] E := (PA.symm.trans (e1.prodCongr e2)).trans PB
  refine ⟨φ, ?_⟩
  have hfr : ∀ y : LinearMap.range f, f y = y := fun y => (LinearMap.IsIdempotentElem.mem_range_iff hf).mp y.2
  have hgr : ∀ y : LinearMap.range g, g y = y := fun y => (LinearMap.IsIdempotentElem.mem_range_iff hg).mp y.2
  have key : ∀ p : LinearMap.range f × LinearMap.ker f, φ (f (PA p)) = g (φ (PA p)) := by
    rintro ⟨r, k⟩
    have h1 : PA (r, k) = (r : E) + (k : E) := Submodule.coe_prodEquivOfIsCompl' _ _ cf _
    have h2 : f (PA (r, k)) = PA (r, 0) := by
      rw [h1, map_add, LinearMap.mem_ker.mp k.2, add_zero, hfr]
      rw [Submodule.coe_prodEquivOfIsCompl' _ _ cf]; simp
    have h3 : ∀ q, φ (PA q) = PB ((e1.prodCongr e2) q) := by
      intro q; simp [φ]
    rw [h2, h3, h3]
    simp only [LinearEquiv.prodCongr_apply, map_zero]
    simp only [PB, Submodule.coe_prodEquivOfIsCompl', Submodule.coe_zero, add_zero, map_add,
      LinearMap.mem_ker.mp (e2 k).2, hgr]
  ext x
  have := key (PA.symm x)
  simpa using this

variable {n : ℕ}

theorem idem_similar (A B : Matrix (Fin n) (Fin n) ℚ) (hA : A * A = A) (hB : B * B = B)
    (hr : A.rank = B.rank) : ∃ Q : Matrix (Fin n) (Fin n) ℚ, IsUnit Q.det ∧ Q * A = B * Q := by
  have hfA : IsIdempotentElem A.mulVecLin := by
    show A.mulVecLin * A.mulVecLin = A.mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hA]
  have hfB : IsIdempotentElem B.mulVecLin := by
    show B.mulVecLin * B.mulVecLin = B.mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hB]
  obtain ⟨φ, hφ⟩ := h50i_conj A.mulVecLin B.mulVecLin hfA hfB hr
  refine ⟨LinearMap.toMatrix' φ.toLinearMap, ?_, ?_⟩
  · refine Matrix.isUnit_det_of_right_inverse (B := LinearMap.toMatrix' φ.symm.toLinearMap) ?_
    rw [← LinearMap.toMatrix'_comp]
    simp
  · have := congrArg LinearMap.toMatrix' hφ
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp] at this
    have eA : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
    have eB : LinearMap.toMatrix' B.mulVecLin = B := LinearMap.toMatrix'_toLin' B
    rw [eA, eB] at this
    exact this

/-! ## The staircase-frame corner factor (`pDatStair`) -/

