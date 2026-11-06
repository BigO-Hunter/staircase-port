import StaircasePort.Pivot

namespace StaircasePort.Stair

-- parse probe for the anonymous-ctor + by-have pattern
example (a a' X : ℕ) (hX : X ≤ a') (r : {r : Fin a' // r.val < X}) :
    ({r : Fin a' // r.val < X} → {r : Fin a // r.val < X}) :=
  fun r => (⟨⟨r.1.val, by have := r.2; omega⟩, by have := r.2; omega⟩ :
    {r : Fin a // r.val < X})

example (a a' X : ℕ) (hX : X ≤ a') (r : {r : Fin a' // r.val < X}) :
    ({r : Fin a' // r.val < X} → {r : Fin a // r.val < X}) :=
  fun r => Subtype.mk (Fin.mk r.1.val (by omega)) r.2

end StaircasePort.Stair
