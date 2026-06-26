/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfMap
public import TauCeti.Algebra.Bialgebra.TensorProduct

/-!
# The direct product of affine group schemes on points

For two commutative bialgebras `H₁` and `H₂` over `R`, the tensor product `H₁ ⊗[R] H₂` is the
coordinate bialgebra of the direct product of the affine group schemes `Spec H₁` and
`Spec H₂`. This file proves that this is reflected on the functor of points: for every
commutative `R`-algebra `A`, the convolution monoid of `R`-algebra homomorphisms
`(H₁ ⊗[R] H₂) →ₐ[R] A` is multiplicatively equivalent to the product of the convolution
monoids `H₁ →ₐ[R] A` and `H₂ →ₐ[R] A` (`pointsMulEquiv`). When `H₁` and `H₂` are Hopf
algebras these convolution monoids are the convolution groups of points, so this is
automatically an isomorphism of groups: the points of the product group scheme are the
product of the points.

The equivalence sends a point `f : (H₁ ⊗[R] H₂) →ₐ[R] A` to its two restrictions
`f ∘ (· ⊗ₜ 1)` and `f ∘ (1 ⊗ₜ ·)`; its inverse is Mathlib's tensor-product product map,
`Algebra.TensorProduct.productMap f₁ f₂ : x ⊗ₜ y ↦ f₁ x * f₂ y`. Both restrictions are
instances of pre-composition with the bialgebra morphisms from
`TauCeti.Algebra.Bialgebra.TensorProduct`, so the restriction map is a monoid homomorphism by
`TauCeti.AlgHom.mapDomain`; Mathlib's product map is its inverse by the universal property.

## Main definitions

* `TauCeti.Bialgebra.TensorProduct.includeLeft` and
  `TauCeti.Bialgebra.TensorProduct.includeRight`: the inclusions `x ↦ x ⊗ₜ 1` and
  `y ↦ 1 ⊗ₜ y` packaged as bialgebra morphisms.
* `TauCeti.AffineGroup.Product.pointsMulEquiv`: the convolution monoid isomorphism between
  `(H₁ ⊗[R] H₂) →ₐ[R] A` and the product `(H₁ →ₐ[R] A) × (H₂ →ₐ[R] A)`. When `H₁` and `H₂` are
  Hopf algebras these are convolution groups, so this is automatically a group isomorphism.
* `TauCeti.AffineGroup.Product.pointsMulEquiv_mapValue`: the product-points equivalence is
  natural in the value algebra.

## References

This realizes the "products of affine group schemes" computation on the functor of points, in
the spirit of the worked examples of the Tau Ceti ReductiveGroups roadmap
(`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 0 "R-points as a group" and the three
synchronized models). The tensor-product bialgebra structure and its unit and identity
isomorphisms are from Mathlib's `Mathlib.RingTheory.Bialgebra.TensorProduct`; the universal
property `Algebra.TensorProduct.lift` is from Mathlib's
`Mathlib.RingTheory.TensorProduct.Maps`. The convolution monoid and its contravariant
functoriality `TauCeti.AlgHom.mapDomain` are Tau Ceti's existing functor-of-points
infrastructure, built on the Mathlib convolution monoid of Yaël Dillies, Michał Mrugała and
Yunzhou Xie.
-/

public section

open TensorProduct WithConv

namespace TauCeti

namespace Algebra.TensorProduct

variable {R H₁ H₂ A B : Type*} [CommSemiring R]
variable [Semiring H₁] [Semiring H₂] [CommSemiring A] [CommSemiring B]
variable [Algebra R H₁] [Algebra R H₂] [Algebra R A] [Algebra R B]

private theorem comp_productMap (φ : A →ₐ[R] B) (f₁ : H₁ →ₐ[R] A) (f₂ : H₂ →ₐ[R] A) :
    φ.comp (_root_.Algebra.TensorProduct.productMap f₁ f₂) =
      _root_.Algebra.TensorProduct.productMap (φ.comp f₁) (φ.comp f₂) := by
  apply _root_.Algebra.TensorProduct.ext'
  intro x y
  simp [_root_.Algebra.TensorProduct.productMap_apply_tmul, map_mul]

end Algebra.TensorProduct

namespace AffineGroup.Product

open Bialgebra.TensorProduct

variable {R H₁ H₂ A : Type*} [CommSemiring R]
variable [CommSemiring H₁] [CommSemiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A]

/-- A point of `Spec (H₁ ⊗[R] H₂)` is recovered from its two restrictions by Mathlib's
`Algebra.TensorProduct.productMap`. -/
@[simp]
theorem productMap_restrict (g : (H₁ ⊗[R] H₂) →ₐ[R] A) :
    Algebra.TensorProduct.productMap (g.comp Algebra.TensorProduct.includeLeft)
        (g.comp Algebra.TensorProduct.includeRight) =
      g := by
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply, AlgHom.comp_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- Restriction of a point of `Spec (H₁ ⊗[R] H₂)` to its two factors, as a monoid homomorphism
of convolution monoids: it pre-composes with the two inclusions `includeLeft` and
`includeRight`. Each component is `TauCeti.AlgHom.mapDomain` of a bialgebra morphism, hence a
monoid homomorphism, so their pairing is too. -/
@[expose] noncomputable def restrictHom :
    WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A) →*
      WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A) :=
  (AlgHom.mapDomain includeLeft).prod (AlgHom.mapDomain includeRight)

@[simp]
theorem restrictHom_apply (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    restrictHom f = (AlgHom.mapDomain includeLeft f, AlgHom.mapDomain includeRight f) := rfl

/-- The convolution monoid of `R`-algebra homomorphisms out of a tensor product of commutative
bialgebras `H₁ ⊗[R] H₂` is the product of the convolution monoids out of `H₁` and `H₂`.

On the functor of points this is the direct product of the affine group schemes `Spec H₁` and
`Spec H₂`: Mathlib's product map sends `x ⊗ₜ y` to `f₁ x * f₂ y`, and convolution is computed
componentwise. When `H₁` and `H₂` are Hopf algebras these convolution monoids are groups
(`TauCeti.AlgHom.instGroup`), so this is automatically an isomorphism of groups. -/
@[expose] noncomputable def pointsMulEquiv :
    WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A) ≃* WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A) where
  toFun := restrictHom
  invFun p := toConv (Algebra.TensorProduct.productMap p.1.ofConv p.2.ofConv)
  left_inv f := by
    apply WithConv.ofConv_injective
    simp only [restrictHom_apply, AlgHom.mapDomain_apply, ofConv_toConv,
      includeLeft_toAlgHom, includeRight_toAlgHom, productMap_restrict]
  right_inv p := by
    obtain ⟨f₁, f₂⟩ := p
    simp only [restrictHom_apply, AlgHom.mapDomain_apply,
      includeLeft_toAlgHom, includeRight_toAlgHom, Algebra.TensorProduct.productMap_left,
      Algebra.TensorProduct.productMap_right,
      toConv_ofConv]
  map_mul' := restrictHom.map_mul

@[simp]
theorem pointsMulEquiv_apply (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    pointsMulEquiv f =
      (AlgHom.mapDomain includeLeft f, AlgHom.mapDomain includeRight f) := rfl

@[simp]
theorem pointsMulEquiv_symm_apply
    (p : WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A)) :
    pointsMulEquiv.symm p = toConv (Algebra.TensorProduct.productMap p.1.ofConv p.2.ofConv) :=
  rfl

variable {B : Type*} [CommSemiring B] [Algebra R B]

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
@[simp]
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B)
    (p : WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A)) :
    AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ
        ((pointsMulEquiv (R := R) (H₁ := H₁) (H₂ := H₂) (A := A)).symm p) =
      (pointsMulEquiv (R := R) (H₁ := H₁) (H₂ := H₂) (A := B)).symm
        (AlgHom.mapValue (H := H₁) φ p.1, AlgHom.mapValue (H := H₂) φ p.2) := by
  rw [pointsMulEquiv_symm_apply, AlgHom.mapValue_apply, pointsMulEquiv_symm_apply]
  congr 1
  exact Algebra.TensorProduct.comp_productMap φ p.1.ofConv p.2.ofConv

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
