/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Parabolic.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent

/-!
# Tangent Lie algebras of weight parabolics

The Lie algebra of the general-linear parabolic attached to integer coordinate weights
consists of matrices preserving the decreasing weight filtration: the `(i,j)` entry
vanishes whenever `w i < w j`. The tangent equivalence identifies the differential of
the closed-subgroup inclusion with the inclusion of these block-triangular matrices.
It works over arbitrary commutative base rings and coefficient algebras, including at
rank zero and in positive characteristic.

The inverse-image criterion also computes the Lie algebra of the intersection of any
represented subgroup of `GL_N` with this parabolic. In particular, self-dual coordinate
weights give the tangent equations of symplectic flag stabilizers. These equations are
used to test which root vectors lie in the chosen Borel.

The construction uses `GeneralLinear.tangentLieEquivMatrix`,
`HopfIdeal.quotientLieEquiv`, and Mathlib's `Matrix.blockTriangularSubalgebra` rather
than constructing a second block-triangular matrix Lie algebra. It follows the restriction
construction of `SpecialLinear.UpperTriangular.tangentLieEquiv`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§10.a and 13 (tangents and parabolics).
* B. Conrad, *Reductive Group Schemes* (2014), §5.1 (root spaces and pinnings).
-/

public section

namespace TauCeti.GeneralLinear

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {N : ℕ}

/-- A tangent vector lies in the weight parabolic exactly when its matrix preserves the
weight filtration. This is an explicit rewriting rule; the general Hopf-ideal membership
lemma determines the `simp` normal form. -/
theorem mem_lieSubalgebra_weightParabolicDefiningHopfIdeal_iff (w : Fin N → ℤ)
    (d : Derivation R (coordinateHopfAlgebra R N)
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R N) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (weightParabolicDefiningHopfIdeal R w) ↔
      (tangentMatrix N d).BlockTriangular (OrderDual.toDual ∘ w) := by
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _
    (weightParabolicDefiningHopfIdeal_toIdeal R w)]
  constructor
  · intro hd i j hij
    rw [tangentMatrix_apply, hd _ (X_mem_weightParabolicRelationSet R w hij), map_zero]
  · intro hd x hx
    obtain ⟨i, j, hij, rfl⟩ := (mem_weightParabolicRelationSet_iff R w x).mp hx
    apply (Bialgebra.CounitAlgebra.algEquivSelf R (coordinateHopfAlgebra R N) B).injective
    rw [map_zero, ← tangentMatrix_apply]
    exact hd hij

/-- The general-linear tangent equivalence carries the weight-parabolic tangent image
onto Mathlib's block-triangular matrix Lie algebra. -/
theorem map_lieSubalgebra_weightParabolicDefiningHopfIdeal (w : Fin N → ℤ) :
    (HopfIdeal.lieSubalgebra (B := B) (weightParabolicDefiningHopfIdeal R w)).map
        (tangentLieEquivMatrix (R := R) (B := B) N).toLieHom =
      lieSubalgebraOfSubalgebra B (Matrix (Fin N) (Fin N) B)
        (Matrix.blockTriangularSubalgebra B B (OrderDual.toDual ∘ w)) := by
  ext X
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    -- The associative-to-Lie construction retains exactly the subalgebra's carrier.
    change (tangentLieEquivMatrix N d).BlockTriangular (OrderDual.toDual ∘ w)
    rw [tangentLieEquivMatrix_apply]
    exact (mem_lieSubalgebra_weightParabolicDefiningHopfIdeal_iff w d).mp hd
  · intro hX
    refine ⟨(tangentLieEquivMatrix (R := R) (B := B) N).symm X, ?_,
      (tangentLieEquivMatrix (R := R) (B := B) N).apply_symm_apply X⟩
    rw [mem_lieSubalgebra_weightParabolicDefiningHopfIdeal_iff,
      ← tangentLieEquivMatrix_apply, LieEquiv.apply_symm_apply]
    exact hX

/-- The Lie algebra of the represented weight parabolic is the block-triangular matrix
Lie algebra for its decreasing weight filtration. -/
noncomputable def weightParabolicTangentLieEquiv (w : Fin N → ℤ) :
    Derivation R (weightParabolicCoordinateHopfAlgebra R w)
        (Bialgebra.CounitAlgebra R (weightParabolicCoordinateHopfAlgebra R w) B) ≃ₗ⁅B⁆
      lieSubalgebraOfSubalgebra B (Matrix (Fin N) (Fin N) B)
        (Matrix.blockTriangularSubalgebra B B (OrderDual.toDual ∘ w)) :=
  (HopfIdeal.quotientLieEquiv (B := B) (weightParabolicDefiningHopfIdeal R w)).trans
    ((tangentLieEquivMatrix (R := R) (B := B) N).ofSubalgebras _ _
      (map_lieSubalgebra_weightParabolicDefiningHopfIdeal w))

/-- The tangent equivalence sends the closed-subgroup differential to its tangent matrix.
The rule runs before simplification of the quotient-indexed coefficient algebra. -/
@[simp↓]
theorem weightParabolicTangentLieEquiv_apply_coe (w : Fin N → ℤ)
    (d : Derivation R (weightParabolicCoordinateHopfAlgebra R w)
      (Bialgebra.CounitAlgebra R (weightParabolicCoordinateHopfAlgebra R w) B)) :
    (weightParabolicTangentLieEquiv (B := B) w d : Matrix (Fin N) (Fin N) B) =
      tangentMatrix N (HopfIdeal.quotientLieHom (weightParabolicDefiningHopfIdeal R w) d) := by
  simp only [weightParabolicTangentLieEquiv, LieEquiv.trans_apply,
    LieEquiv.ofSubalgebras_apply, HopfIdeal.quotientLieEquiv_apply_coe]
  exact tangentLieEquivMatrix_apply N _

/-- Descending a filtration-preserving matrix and differentiating its inclusion recovers
that matrix. The rule runs before simplification of the quotient-indexed coefficient algebra. -/
@[simp↓]
theorem tangentMatrix_quotientLieHom_weightParabolicTangentLieEquiv_symm
    (w : Fin N → ℤ)
    (X : lieSubalgebraOfSubalgebra B (Matrix (Fin N) (Fin N) B)
      (Matrix.blockTriangularSubalgebra B B (OrderDual.toDual ∘ w))) :
    tangentMatrix N (HopfIdeal.quotientLieHom (weightParabolicDefiningHopfIdeal R w)
      ((weightParabolicTangentLieEquiv (R := R) (B := B) w).symm X)) = X := by
  rw [← weightParabolicTangentLieEquiv_apply_coe, LieEquiv.apply_symm_apply]

/-- The tangent Lie algebra of the inverse image of a weight parabolic under a group
homomorphism is cut out by the same forbidden entries of the differential. -/
theorem mem_lieSubalgebra_map_weightParabolicDefiningHopfIdeal_iff
    {H : Type*} [CommRing H] [HopfAlgebra R H]
    (w : Fin N → ℤ) (f : coordinateHopfAlgebra R N →ₐc[R] H)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) ((weightParabolicDefiningHopfIdeal R w).map f) ↔
      (tangentMatrix N (derivationCompLieHom (B := B) f d)).BlockTriangular
        (OrderDual.toDual ∘ w) := by
  rw [HopfIdeal.lieSubalgebra_map, LieSubalgebra.mem_comap]
  exact mem_lieSubalgebra_weightParabolicDefiningHopfIdeal_iff w _

end TauCeti.GeneralLinear
