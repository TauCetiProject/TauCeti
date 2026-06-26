/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Product

/-!
# Naturality of product points

`TauCeti.AffineGroup.Product.pointsMulEquiv` identifies the convolution points of the tensor
product bialgebra `H₁ ⊗[R] H₂` with pairs of convolution points of `H₁` and `H₂`. This file
records that the identification is natural in the value algebra: post-composing a point by an
`R`-algebra homomorphism commutes with restricting it to the two factors, and with assembling a
point from a pair of factor points.

This is bookkeeping for the ReductiveGroups roadmap Layer 0 functor-of-points dictionary. The
roadmap asks that affine group schemes, Hopf algebras, and group-valued functors remain
synchronized; product identifications in the points functor need these naturality lemmas to be
usable as functorial isomorphisms.

## Main results

* `TauCeti.AffineGroup.Product.restrictHom_mapValue`: restriction to the two tensor factors
  commutes with post-composition in the value algebra.
* `TauCeti.AffineGroup.Product.pointsMulEquiv_mapValue`: the product-points equivalence is
  natural in the value algebra.
* `TauCeti.AffineGroup.Product.mapValue_pointsMulEquiv_symm_apply`: the inverse product map
  is natural in the value algebra.

## References

This builds directly on Tau Ceti's product-points calculation
`TauCeti.AffineGroup.Product.pointsMulEquiv` and functoriality API `TauCeti.AlgHom.mapValue`,
which in turn use Mathlib's convolution monoid on algebra homomorphisms and tensor-product
universal property.
-/

public section

open TensorProduct WithConv

namespace TauCeti

namespace AffineGroup.Product

open Bialgebra.TensorProduct

variable {R H₁ H₂ A B : Type*} [CommSemiring R]
variable [CommSemiring H₁] [CommSemiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

/-- Restricting a product point to the two factors commutes with post-composition in the value
algebra. This is the naturality square for the restriction homomorphism underlying
`pointsMulEquiv`. -/
theorem restrictHom_mapValue (φ : A →ₐ[R] B)
    (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    restrictHom (AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ f) =
      (AlgHom.mapValue (H := H₁) φ (restrictHom f).1,
        AlgHom.mapValue (H := H₂) φ (restrictHom f).2) := by
  rw [restrictHom_apply, restrictHom_apply]
  exact Prod.ext
    (DFunLike.congr_fun
      (AlgHom.mapValue_mapDomain (H₁ := H₁) (H₂ := H₁ ⊗[R] H₂) includeLeft φ) f)
    (DFunLike.congr_fun
      (AlgHom.mapValue_mapDomain (H₁ := H₂) (H₂ := H₁ ⊗[R] H₂) includeRight φ) f)

/-- The product-points equivalence is natural in the value algebra.

Post-composing an `A`-valued point of `Spec (H₁ ⊗[R] H₂)` by `φ : A →ₐ[R] B`, then splitting
it into its two factor points, gives the same pair as first splitting and then post-composing
each factor point by `φ`. -/
@[simp]
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    pointsMulEquiv (A := B) (AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ f) =
      (AlgHom.mapValue (H := H₁) φ (pointsMulEquiv f).1,
        AlgHom.mapValue (H := H₂) φ (pointsMulEquiv f).2) :=
  restrictHom_mapValue φ f

/-- First-component form of `pointsMulEquiv_mapValue`. -/
@[simp]
theorem pointsMulEquiv_mapValue_fst (φ : A →ₐ[R] B)
    (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    (pointsMulEquiv (A := B) (AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ f)).1 =
      AlgHom.mapValue (H := H₁) φ (pointsMulEquiv f).1 := by
  rw [pointsMulEquiv_mapValue]

/-- Second-component form of `pointsMulEquiv_mapValue`. -/
@[simp]
theorem pointsMulEquiv_mapValue_snd (φ : A →ₐ[R] B)
    (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    (pointsMulEquiv (A := B) (AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ f)).2 =
      AlgHom.mapValue (H := H₂) φ (pointsMulEquiv f).2 := by
  rw [pointsMulEquiv_mapValue]

/-- The inverse product-points map is natural in the value algebra.

Assembling an `A`-valued product point from a pair of factor points and then post-composing by
`φ : A →ₐ[R] B` is the same as post-composing both factor points by `φ` and then assembling the
resulting `B`-valued product point. -/
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B)
    (p : WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A)) :
    AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ
        ((pointsMulEquiv (R := R) (H₁ := H₁) (H₂ := H₂) (A := A)).symm p) =
      (pointsMulEquiv (R := R) (H₁ := H₁) (H₂ := H₂) (A := B)).symm
        (AlgHom.mapValue (H := H₁) φ p.1, AlgHom.mapValue (H := H₂) φ p.2) := by
  apply (pointsMulEquiv (R := R) (H₁ := H₁) (H₂ := H₂) (A := B)).injective
  rw [pointsMulEquiv_mapValue]
  simp

/-- On pure tensors, naturality of the inverse product-points map says that post-composition
by `φ` evaluates as applying `φ` to the product of the two factor values. -/
@[simp]
theorem mapValue_pointsMulEquiv_symm_apply_tmul (φ : A →ₐ[R] B)
    (p : WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A)) (x : H₁) (y : H₂) :
    (AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ
        ((pointsMulEquiv (R := R) (H₁ := H₁) (H₂ := H₂) (A := A)).symm p)).ofConv
        (x ⊗ₜ[R] y) =
      φ (p.1.ofConv x * p.2.ofConv y) := by
  rw [mapValue_pointsMulEquiv_symm_apply, pointsMulEquiv_symm_apply]
  simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    Algebra.TensorProduct.productMap_apply_tmul, map_mul]

/-- On pure tensors, assembling after post-composing both factor points multiplies the two
post-composed factor values. -/
@[simp]
theorem pointsMulEquiv_symm_mapValue_apply_tmul (φ : A →ₐ[R] B)
    (p : WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A)) (x : H₁) (y : H₂) :
    ((pointsMulEquiv (R := R) (H₁ := H₁) (H₂ := H₂) (A := B)).symm
        (AlgHom.mapValue (H := H₁) φ p.1, AlgHom.mapValue (H := H₂) φ p.2)).ofConv
        (x ⊗ₜ[R] y) =
      φ (p.1.ofConv x) * φ (p.2.ofConv y) := by
  rw [pointsMulEquiv_symm_apply]
  simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    Algebra.TensorProduct.productMap_apply_tmul]

end AffineGroup.Product

end TauCeti
