/- N2a name probe: pin exact Mathlib lemma signatures before writing the proof. -/
import Mathlib

open Matrix Finset Submodule

variable {K : Type*} [Field K] {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq τ]
variable {a b : ℕ}

-- rank toolkit (Matrix)
#check @Matrix.rank_le_card_of_support_subset
#check @Matrix.rank_le_card_height
#check @Matrix.rank_transpose
#check @Matrix.rank_zero
#check @Matrix.rank_eq_finrank_span_row
#check @Matrix.rank_vecMulVec_le
#check @Matrix.rank_mul_le_left
#check @Matrix.rank_mul_le_right
#check @Matrix.row_apply
#check @Matrix.add_row
#check @Matrix.transpose_apply

-- submodule / dimension
#check @Function.support_subset_iff'
#check @Submodule.add_mem_sup
#check @Submodule.finrank_mono
#check @Submodule.finrank_add_le_finrank_add_finrank
#check @Submodule.span_le
#check @Submodule.subset_span
example (f : ι → (κ → K)) : FiniteDimensional K (Submodule.span K (Set.range f)) := inferInstance

-- finset / big operators
#check @Finset.card_le_card_of_injOn
#check @Finset.sum_union
#check @Finset.sum_le_sum
#check @Finset.sum_const_one
#check @Finset.sum_apply
#check @Finset.sum_eq_zero
#check @Finset.sum_add_distrib
#check @Finset.union_subset_iff
#check @Finset.sdiff_subset
#check @Finset.filter_subset
#check @Finset.disjoint_left
#check @Finset.induction_on
#check @Set.MapsTo
#check @Set.InjOn

-- notation + statement shapes used in the proof
example (M : τ → Matrix ι κ K) : Matrix ι κ K := ∑ t, M t

example (A : Matrix ι κ K) : A.rank = finrank K (Submodule.span K (Set.range A.row)) :=
  Matrix.rank_eq_finrank_span_row A

example (A B : Matrix ι κ K) : (A + B).row = A.row + B.row := rfl

-- rank_le_card_of_support_subset applied at our concrete shapes
example (P : Matrix ι κ K) (s : Finset ι) (hz : Function.support P.row ⊆ s) : P.rank ≤ s.card :=
  Matrix.rank_le_card_of_support_subset P s hz

-- card_le_card_of_injOn at the subtype-embedding shape
example (X : ℕ) (R₀ : Finset (Fin a)) :
    ((Finset.univ : Finset {r : Fin a // r.val < X}).filter fun r => (r : Fin a) ∈ R₀).card ≤ R₀.card :=
  Finset.card_le_card_of_injOn Subtype.val
    (fun r hr => (Finset.mem_filter.mp hr).2)
    (fun r _ r' _ h => Subtype.eq h)
