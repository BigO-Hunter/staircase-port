import StaircasePort.Pivot

namespace StaircasePort.Stair

open Matrix IntMul.Kappa.R6.Bit.NB

set_option maxHeartbeats 1000000

lemma stairMQ_entry (a b c e : Fin 23) :
    stairMQ (a, b) (c, e) =
      ((if a = c then (1 : ℚ) else 0) - stairQX1 a * stairQY1 c) *
        ((if b = e then (1 : ℚ) else 0) - stairQX2 b * stairQY2 e) := by
  simp only [stairMQ, kronecker_apply, Matrix.sub_apply, vecMulVec_apply, Matrix.one_apply]

-- probe 1: rw on a bare application with explicit Fin args
example : stairMQ ((0 : Fin 23), (0 : Fin 23)) ((1 : Fin 23), (0 : Fin 23))
    = ((if (0 : Fin 23) = 1 then (1 : ℚ) else 0) - stairQX1 0 * stairQY1 1) *
      ((if (0 : Fin 23) = 0 then (1 : ℚ) else 0) - stairQX2 0 * stairQY2 0) := by
  rw [stairMQ_entry]

-- probe 2: is the entry value reachable by norm_num after the rewrite?
example : stairMQ ((0 : Fin 23), (0 : Fin 23)) ((1 : Fin 23), (0 : Fin 23))
    = 653217308241796875 := by
  rw [stairMQ_entry]
  norm_num [stairQX1, stairQY1, stairQX2, stairQY2, stairWX1L, stairWY1L, stairWX2L, stairWY2L,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, Fin.isValue, ↓reduceIte]

end StaircasePort.Stair
