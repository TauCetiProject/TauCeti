/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.Bialgebra.TensorProduct
public import TauCeti.Algebra.TensorProduct.Maps

/-!
# Products of convolution monoids of algebra maps

For two bialgebras `H₁` and `H₂` over `R` and every commutative `R`-algebra `A`, the
convolution monoid of algebra maps `(H₁ ⊗[R] H₂) →ₐ[R] A` is multiplicatively equivalent to
the product of the convolution monoids `H₁ →ₐ[R] A` and `H₂ →ₐ[R] A` (`pointsMulEquiv`).
The bialgebras need not be commutative. When they are Hopf algebras these convolution monoids
are groups, so the equivalence is automatically a group isomorphism.

For commutative Hopf algebras, `H₁ ⊗[R] H₂` is the coordinate algebra of the direct product
of the affine group schemes `Spec H₁` and `Spec H₂`. The equivalence identifies the points
of this product group scheme with the product of the points of the two factors.

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
* `TauCeti.AffineGroup.Product.mapDomain_projectLeft` and `mapDomain_projectRight`: precomposition
  with a tensor-product projection inserts a point into the corresponding product factor.
* `TauCeti.AffineGroup.Product.pointsMulEquiv_mapValue`: the product-points equivalence is
  natural in the value algebra.

## References

The tensor-product bialgebra structure and its unit and identity
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

namespace AffineGroup.Product

open _root_.TauCeti.Bialgebra.TensorProduct

variable {R H₁ H₂ A : Type*} [CommSemiring R]
variable [Semiring H₁] [Semiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A]

/-- Restriction of an algebra map out of `H₁ ⊗[R] H₂` to its two factors, as a monoid
homomorphism of convolution monoids. Its components are pre-composition with the bialgebra
inclusions `includeLeft` and `includeRight`. -/
noncomputable def restrictHom :
    WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A) →*
      WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A) :=
  (AlgHom.mapDomain includeLeft).prod (AlgHom.mapDomain includeRight)

@[simp]
theorem restrictHom_apply (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    restrictHom f = (AlgHom.mapDomain includeLeft f, AlgHom.mapDomain includeRight f) := (rfl)

/-- The convolution monoid of `R`-algebra homomorphisms out of a tensor product of
bialgebras `H₁ ⊗[R] H₂` is the product of the convolution monoids out of `H₁` and `H₂`.

For commutative bialgebras, this computes the functor of points of the direct product of
`Spec H₁` and `Spec H₂`: Mathlib's product map sends `x ⊗ₜ y` to `f₁ x * f₂ y`, and
convolution is computed componentwise. When `H₁` and `H₂` are Hopf algebras these convolution
monoids are groups (`TauCeti.AlgHom.instGroup`), so this is automatically a group isomorphism. -/
noncomputable def pointsMulEquiv :
    WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A) ≃* WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A) where
  toFun := restrictHom
  invFun p := toConv (Algebra.TensorProduct.productMap p.1.ofConv p.2.ofConv)
  left_inv f := by
    apply WithConv.ofConv_injective
    simp only [restrictHom_apply, AlgHom.mapDomain_apply, ofConv_toConv,
      includeLeft_toAlgHom, includeRight_toAlgHom,
      _root_.AlgHom.productMap_comp_includeLeft_includeRight]
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
      (AlgHom.mapDomain includeLeft f, AlgHom.mapDomain includeRight f) := (rfl)

@[simp]
theorem pointsMulEquiv_symm_apply
    (p : WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A)) :
    pointsMulEquiv.symm p = toConv (Algebra.TensorProduct.productMap p.1.ofConv p.2.ofConv) :=
  (rfl)

/-- Precomposition with the left tensor-product projection inserts a point as the left factor of
the product, with the identity in the right factor. -/
@[simp]
theorem mapDomain_projectLeft (g : WithConv (H₁ →ₐ[R] A)) :
    toConv (g.ofConv.comp (Bialgebra.TensorProduct.projectLeft
      (R := R) (H₁ := H₁) (H₂ := H₂)).toAlgHom) =
      pointsMulEquiv.symm (g, 1) := by
  apply WithConv.ofConv_injective
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [AlgHom.convOne_apply, Algebra.smul_def, mul_comm]

/-- Precomposition with the right tensor-product projection inserts a point as the right factor of
the product, with the identity in the left factor. -/
@[simp]
theorem mapDomain_projectRight (g : WithConv (H₂ →ₐ[R] A)) :
    toConv (g.ofConv.comp (Bialgebra.TensorProduct.projectRight
      (R := R) (H₁ := H₁) (H₂ := H₂)).toAlgHom) =
      pointsMulEquiv.symm ((1 : WithConv (H₁ →ₐ[R] A)), g) := by
  apply WithConv.ofConv_injective
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [AlgHom.convOne_apply, Algebra.smul_def]

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

Post-composing an algebra map `(H₁ ⊗[R] H₂) →ₐ[R] A` by `φ : A →ₐ[R] B`, then restricting
to its two factors, gives the same pair as first restricting and then post-composing each
factor map by `φ`. -/
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B)
    (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    pointsMulEquiv (A := B) (AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ f) =
      (AlgHom.mapValue (H := H₁) φ (pointsMulEquiv f).1,
        AlgHom.mapValue (H := H₂) φ (pointsMulEquiv f).2) :=
  restrictHom_mapValue φ f

/-- First-component form of `pointsMulEquiv_mapValue`. -/
theorem pointsMulEquiv_mapValue_fst (φ : A →ₐ[R] B)
    (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    (pointsMulEquiv (A := B) (AlgHom.mapValue (H := H₁ ⊗[R] H₂) φ f)).1 =
      AlgHom.mapValue (H := H₁) φ (pointsMulEquiv f).1 := by
  rw [pointsMulEquiv_mapValue]

/-- Second-component form of `pointsMulEquiv_mapValue`. -/
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
  simp only [pointsMulEquiv_symm_apply, AlgHom.mapValue_apply]
  rw [_root_.AlgHom.comp_productMap]

end AffineGroup.Product

end TauCeti
