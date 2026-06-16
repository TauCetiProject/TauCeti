/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.AlgebraicGroup.HopfMap
import TauCeti.Algebra.Bialgebra.TensorProduct

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

## References

This realizes the "products of affine group schemes" computation on the functor of points, in
the spirit of the worked examples of the Tau Ceti ReductiveGroups roadmap
(`TauCetiRoadmap/ReductiveGroups/README.md`, Layer 0 "R-points as a group" and the three
synchronized models). The tensor-product bialgebra structure and its unit and identity
isomorphisms are from Mathlib's `Mathlib.RingTheory.Bialgebra.TensorProduct`; the universal
property `Algebra.TensorProduct.lift` is from Mathlib's
`Mathlib.RingTheory.TensorProduct.Maps`. The convolution monoid and its contravariant
functoriality `TauCeti.AlgHom.mapDomain` are Tau Ceti's existing functor-of-points
infrastructure, built on the Mathlib convolution monoid of Yaël Dillies, Michał Mrugała and
Yunzhou Xie.
-/

open TensorProduct WithConv

namespace TauCeti

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
private noncomputable def restrictHom :
    WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A) →*
      WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A) :=
  (AlgHom.mapDomain includeLeft).prod (AlgHom.mapDomain includeRight)

@[simp]
private theorem restrictHom_apply (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    restrictHom f = (AlgHom.mapDomain includeLeft f, AlgHom.mapDomain includeRight f) := rfl

/-- The convolution monoid of `R`-algebra homomorphisms out of a tensor product of commutative
bialgebras `H₁ ⊗[R] H₂` is the product of the convolution monoids out of `H₁` and `H₂`.

On the functor of points this is the direct product of the affine group schemes `Spec H₁` and
`Spec H₂`: Mathlib's product map sends `x ⊗ₜ y` to `f₁ x * f₂ y`, and convolution is computed
componentwise. When `H₁` and `H₂` are Hopf algebras these convolution monoids are groups
(`TauCeti.AlgHom.instGroup`), so this is automatically an isomorphism of groups. -/
noncomputable def pointsMulEquiv :
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

end AffineGroup.Product

end TauCeti
