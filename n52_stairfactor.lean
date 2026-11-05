/-- **The staircase-frame corner factor** — `pDat` (Defs4:1497) with the corner functional
`cor` (r6/Defs4 frame) replaced by the staircase frame `corStairR` (which at `R = ℚ` is
Cert.lean's `corStairQ`). This is the N5-2 substitution forced by the frame discovery: at the
staircase witness the r6-frame 45x45 corner is SINGULAR (det = 0, rank 44 — the r6 witness
reproduces Defs4's `certRows` exactly, so the implementation is validated; see
scratch_corner_check2.py), while the staircase-frame corner is invertible there (N3's
`stair_data_cert`, Cert.lean:213). Consumed by the Pall product below in place of `pDat`. -/
noncomputable def pDatStair (P₁ P₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ) : Rp (19 + 4) :=
  (Matrix.of fun i j : Fin (2 * 19 + 7) => corStairR (kM P₁ P₂) i.val j.val).det

/-- Ported from `eval_pDat_of` (nb_flag_gen_solution.lean:823-844) with `cor` -> `corStairQ`
and the scalar pull-out done entrywise by `corStairR_smul` (Signature.lean) rather than through
the `Te`/`Te'` frame product. -/
lemma eval_pDatStair_of (f : Vr (19 + 4) → ℚ) (P₁ P₂ W₁ W₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (h1 : sconj (Uf f) P₁ = (Uf f).det • W₁) (h2 : sconj (Vf f) P₂ = (Vf f).det • W₂) :
    eval f (pDatStair P₁ P₂) = ((Uf f).det * (Vf f).det) ^ (2 * 19 + 7) *
      (Matrix.of fun i j : Fin (2 * 19 + 7) =>
        corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val).det := by
  have key : (kM P₁ P₂).map (eval f) = ((Uf f).det * (Vf f).det) • ((1 - W₁) ⊗ₖ (1 - W₂)) := by
    rw [map_kM, h1, h2, ← smul_sub, ← smul_sub, smul_kronecker, kronecker_smul, smul_smul]
  rw [pDatStair, eval_det]
  have hmat : (Matrix.of fun i j : Fin (2 * 19 + 7) =>
      corStairR (kM P₁ P₂) i.val j.val).map (eval f) =
      ((Uf f).det * (Vf f).det) •
        (Matrix.of fun i j : Fin (2 * 19 + 7) =>
          corStairR ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [eval_corStairR f (kM P₁ P₂) i.val j.val, key, corStairR_smul]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  have hdet_eq : (Matrix.of fun i j : Fin (2 * 19 + 7) =>
      corStairR ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val) =
      (Matrix.of fun i j : Fin (2 * 19 + 7) =>
        corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val) := by
    ext i j
    simp only [Matrix.of_apply, corStairR_rat]
  rw [hmat, det_smul, Fintype.card_fin, hdet_eq]

/-- Ported from `pDat_ne` (nb_flag_gen_solution.lean:846-857). The witness nonvanishing it
consumes is `hc`, in the staircase frame — instantiated by `stair_data_cert` (N3). -/
lemma pDatStair_ne (P₁ P₂ W₁ W₂ : Matrix (Fin (19 + 4)) (Fin (19 + 4)) ℚ)
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂) (k₁ : W₁ * W₁ = W₁) (k₂ : W₂ * W₂ = W₂)
    (t₁ : P₁.trace = W₁.trace) (t₂ : P₂.trace = W₂.trace)
    (hc : (Matrix.of fun i j : Fin (2 * 19 + 7) =>
      corStairQ ((1 - W₁) ⊗ₖ (1 - W₂)) i.val j.val).det ≠ 0) :
    pDatStair P₁ P₂ ≠ 0 := by
  obtain ⟨U, hU, e1⟩ := conj_wit P₁ W₁ h₁ k₁ t₁
  obtain ⟨V, hV, e2⟩ := conj_wit P₂ W₂ h₂ k₂ t₂
  intro h0
  have := congrArg (eval (ptUV U V)) h0
  rw [eval_pDatStair_of (ptUV U V) P₁ P₂ W₁ W₂ (by rw [Uf_pt]; exact e1)
    (by rw [Vf_pt]; exact e2), Uf_pt, Vf_pt, map_zero] at this
  exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hU hV)) hc this

