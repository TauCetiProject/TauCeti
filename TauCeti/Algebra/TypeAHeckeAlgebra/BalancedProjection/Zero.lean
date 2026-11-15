/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import TauCeti.Algebra.Star.Projection.Commute

/-!
# Balanced projections at the endpoint `τ = 0`

For `τ = 0` the balanced relation between adjacent generators of
`TauCeti.BalancedProjectionAlgebra R 0` reads `e i * e (i + 1) * e i = e (i + 1) * e i * e (i + 1)`.
For two star projections in a ring with a proper star this forces them to commute
(`IsStarProjection.commute_of_mul_mul_eq`), and distant generators commute by definition. Hence
every representation of the balanced projection algebra by projections in such a ring (for
instance a C⋆-algebra) has commutative image.

## Main results

* `TauCeti.BalancedProjectionAlgebra.commute_map_e_of_zero`: the images of any two generators
  commute.
* `TauCeti.BalancedProjectionAlgebra.commute_map_of_zero`: the image is commutative.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, for
  the projection generators of the Hecke algebra.
-/

public section

namespace TauCeti

namespace BalancedProjectionAlgebra

variable {R A F : Type*} [CommRing R] [Ring A] [StarRing A] [IsProperStar A] [Algebra R A]
  [FunLike F (BalancedProjectionAlgebra R (0 : R)) A]
  [AlgHomClass F R (BalancedProjectionAlgebra R (0 : R)) A] (φ : F)

/-- For `τ = 0`, the images of any two generators under a representation by projections in a ring
with a proper star commute. -/
theorem commute_map_e_of_zero (hφ : ∀ i, IsStarProjection (φ (e 0 i))) (i j : ℕ) :
    Commute (φ (e 0 i)) (φ (e 0 j)) := by
  have hadj (i : ℕ) : Commute (φ (e 0 i)) (φ (e 0 (i + 1))) := by
    refine (hφ i).commute_of_mul_mul_eq (hφ (i + 1)) ?_
    simpa only [map_sub, map_mul, map_smul, zero_smul, sub_zero] using
      congr_arg φ (e_balanced (τ := (0 : R)) i)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
    rcases k with _ | k
    · exact hadj i
    · exact (commute_e (by omega)).map φ
  · exact Commute.refl _
  · rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
    rcases k with _ | k
    · exact (hadj j).symm
    · exact (commute_e (by omega)).map φ

/-- For `τ = 0`, a representation by projections in a ring with a proper star has commutative
image. -/
theorem commute_map_of_zero (hφ : ∀ i, IsStarProjection (φ (e 0 i)))
    (x y : BalancedProjectionAlgebra R (0 : R)) : Commute (φ x) (φ y) := by
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (map_mem_adjoin_range φ y) ?_
  rintro _ ⟨j, rfl⟩
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (map_mem_adjoin_range φ x) ?_).symm
  rintro _ ⟨i, rfl⟩
  exact commute_map_e_of_zero φ hφ j i

end BalancedProjectionAlgebra

end TauCeti
