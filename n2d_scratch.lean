import StaircasePort.Pivot

/-!
# N2d scratch — where the two frames diverge, and the witness delta
-/

namespace StaircasePort.Stair

open Matrix IntMul.Kappa.R6.Bit.NB

set_option maxHeartbeats 1000000

/-- Mirror entry formula for the staircase witness pair matrix. -/
lemma stairMQ_entry (a b c e : Fin 23) :
    stairMQ (a, b) (c, e) =
      ((if a = c then (1 : ℚ) else 0) - stairQX1 a * stairQY1 c) *
        ((if b = e then (1 : ℚ) else 0) - stairQX2 b * stairQY2 e) := by
  simp only [stairMQ, kronecker_apply, Matrix.sub_apply, vecMulVec_apply, Matrix.one_apply]

/-! ## The two frames read different matrix entries at (0,0) — label-free -/

lemma Lterms_0 : Lterms (h := 19) 0 = [(1, ((0 : Fin 23), (0 : Fin 23)))] := by
  simp [Lterms]

lemma Rterms_0 : Rterms (h := 19) 0 = [(1, ((1 : Fin 23), (0 : Fin 23)))] := by
  simp [Rterms]

lemma LtermsStair_0 : LtermsStair 0 = [(1, ((0 : Fin 23), (0 : Fin 23)))] := by
  simp [LtermsStair, LtermsZStair]

lemma RtermsStair_0 : RtermsStair 0 = [(1, ((1 : Fin 23), (3 : Fin 23)))] := by
  simp [RtermsStair, RtermsZStair]

/-- The r6/Defs4 corner at (0,0) reads `M (0,0) (1,0)`. -/
lemma cor_00 (M : Matrix (Pr 23) (Pr 23) ℚ) :
    cor (h := 19) M 0 0 = M ((0 : Fin 23), (0 : Fin 23)) ((1 : Fin 23), (0 : Fin 23)) := by
  simp [cor, Lterms_0, Rterms_0]

/-- The staircase corner at (0,0) reads `M (0,0) (1,3)`. -/
lemma corStairQ_00 (M : Matrix (Pr 23) (Pr 23) ℚ) :
    corStairQ M 0 0 = M ((0 : Fin 23), (0 : Fin 23)) ((1 : Fin 23), (3 : Fin 23)) := by
  simp [corStairQ, LtermsStair_0, RtermsStair_0]

/-- **The frame delta at the staircase witness.** The two frames' (0,0) entries differ
(the r6 frame reads the `(1,0)` matrix entry, the staircase frame the `(1,3)` one). -/
theorem n2d_frame_delta :
    cor (h := 19) stairMQ 0 0 ≠ corStairQ stairMQ 0 0 := by
  rw [cor_00, corStairQ_00, stairMQ_entry, stairMQ_entry]
  norm_num [stairQX1, stairQY1, stairQX2, stairQY2, stairWX1L, stairWY1L, stairWX2L, stairWY2L,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, Fin.isValue, ↓reduceIte,
    Fin.mk.injEq]

end StaircasePort.Stair
