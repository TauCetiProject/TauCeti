/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import TauCeti.AlgebraicGeometry.Pullback.SpecMap

/-!
# Integral models of affine semigroup schemes

The spectrum of `AddMonoidAlgebra ℤ S` is an integral model for the affine semigroup
scheme with exponent monoid `S`. Its base change to any commutative ring `R` is
`Spec (AddMonoidAlgebra R S)`, including nonreduced coefficient rings.

The comparison uses Mathlib's `AddMonoidAlgebra.scalarTensorEquiv` and the affine
pullback comparison `pullbackSpecIsoOfAlgEquiv`. It is an isomorphism over the new
coefficient ring, and its other projection is the coefficient map on monoid algebras.
No finite-generation, cancellation or saturation hypothesis is needed for this base change.

## References

W. Fulton, *Introduction to Toric Varieties*, §1.2, for affine schemes of semigroup
algebras. The algebraic base-change construction is Mathlib's
`AddMonoidAlgebra.scalarTensorEquiv`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct AlgebraMonoidAlgebra

namespace TauCeti.AlgebraicGeometry

universe u

/-- The integral affine semigroup model, with its native additive monoid algebra carrier. -/
noncomputable def addMonoidAlgebraIntegralModel (S : Type u) [AddCommMonoid S] : Scheme :=
  Spec (.of (AddMonoidAlgebra ℤ S))

/-- The integral model is the spectrum of the integral semigroup algebra. -/
theorem addMonoidAlgebraIntegralModel_def (S : Type u) [AddCommMonoid S] :
    addMonoidAlgebraIntegralModel S = Spec (.of (AddMonoidAlgebra ℤ S)) :=
  (rfl)

instance (S : Type u) [AddCommMonoid S] : IsAffine (addMonoidAlgebraIntegralModel S) := by
  rw [addMonoidAlgebraIntegralModel_def]
  infer_instance

/-- Extending coefficients in an additive monoid algebra is the affine scheme base change,
as an isomorphism over the new coefficient ring. Taking `K = ℤ` gives the base changes
of `addMonoidAlgebraIntegralModel`. -/
noncomputable def addMonoidAlgebraSpecBaseChangeIso (K R S : Type u)
    [CommRing K] [CommRing R] [Algebra K R] [AddCommMonoid S] :
    Over.mk (pullback.snd (Spec.algebraMap K (AddMonoidAlgebra K S))
      (Spec.algebraMap K R)) ≅
        Over.mk (Spec.algebraMap R (AddMonoidAlgebra R S)) :=
  pullbackSpecIsoOfAlgEquiv K (AddMonoidAlgebra K S) R (AddMonoidAlgebra R S)
    (AddMonoidAlgebra.scalarTensorEquiv K R)

/-- The base-change comparison commutes with projection to the original semigroup scheme. -/
@[reassoc (attr := simp)]
theorem addMonoidAlgebraSpecBaseChangeIso_hom_fst (K R S : Type u)
    [CommRing K] [CommRing R] [Algebra K R] [AddCommMonoid S] :
    (addMonoidAlgebraSpecBaseChangeIso K R S).hom.left ≫
        Spec.algebraMap (AddMonoidAlgebra K S) (AddMonoidAlgebra R S) =
      pullback.fst (Spec.algebraMap K (AddMonoidAlgebra K S)) (Spec.algebraMap K R) := by
  rw [addMonoidAlgebraSpecBaseChangeIso, pullbackSpecIsoOfAlgEquiv_hom_left]
  have h : (AddMonoidAlgebra.scalarTensorEquiv K R (M := S)).symm.toRingHom.comp
      (algebraMap (AddMonoidAlgebra K S) (AddMonoidAlgebra R S)) =
        Algebra.TensorProduct.includeRight.toRingHom := by
    apply RingHom.ext
    intro p
    apply (AddMonoidAlgebra.scalarTensorEquiv K R (M := S)).injective
    ext s
    simp [AddMonoidAlgebra.algebraMap_def, RingHom.coe_coe]
  simp only [Spec.algebraMap]
  rw [Category.assoc, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h]
  simp

/-- The native coefficient square is cartesian. This is the scheme form of
`AddMonoidAlgebra.instIsPushout`, with no flatness assumption on the coefficient map. -/
theorem isPullback_addMonoidAlgebraSpec (K R S : Type u)
    [CommRing K] [CommRing R] [Algebra K R] [AddCommMonoid S] :
    IsPullback
      (Spec.algebraMap (AddMonoidAlgebra K S) (AddMonoidAlgebra R S))
      (Spec.algebraMap R (AddMonoidAlgebra R S))
      (Spec.algebraMap K (AddMonoidAlgebra K S)) (Spec.algebraMap K R) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout K (AddMonoidAlgebra K S) R
      (AddMonoidAlgebra R S))

end TauCeti.AlgebraicGeometry
