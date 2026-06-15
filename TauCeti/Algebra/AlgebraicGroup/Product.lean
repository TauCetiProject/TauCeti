/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Bialgebra.TensorProduct
import TauCeti.Algebra.AlgebraicGroup.HopfMap

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
`f ∘ (· ⊗ₜ 1)` and `f ∘ (1 ⊗ₜ ·)`; its inverse glues a pair `(f₁, f₂)` back together via the
universal property of the tensor product, `f₁ ⊗ f₂ : x ⊗ₜ y ↦ f₁ x * f₂ y`. Both restrictions
are instances of pre-composition with a bialgebra morphism, so the restriction map is a monoid
homomorphism by `TauCeti.AlgHom.mapDomain`; gluing is its inverse by the universal property.

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

namespace Bialgebra.TensorProduct

variable {R H₁ H₂ : Type*} [CommSemiring R]
variable [Semiring H₁] [Semiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]

/-- The left inclusion `x ↦ x ⊗ₜ 1` of a bialgebra into a tensor product of bialgebras,
packaged as a bialgebra morphism. It is the unit `R →ₐc[R] H₂` tensored on the right with `H₁`,
precomposed with the right-unit isomorphism `H₁ ≃ₐc[R] H₁ ⊗[R] R`. -/
noncomputable def includeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.map (BialgHom.id R H₁) (_root_.Bialgebra.unitBialgHom R H₂)).comp
    (_root_.Bialgebra.TensorProduct.rid R R H₁).symm.toBialgHom

/-- The right inclusion `y ↦ 1 ⊗ₜ y` of a bialgebra into a tensor product of bialgebras,
packaged as a bialgebra morphism. It is the unit `R →ₐc[R] H₁` tensored on the left with `H₂`,
precomposed with the left-unit isomorphism `H₂ ≃ₐc[R] R ⊗[R] H₂`. -/
noncomputable def includeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.map (_root_.Bialgebra.unitBialgHom R H₁) (BialgHom.id R H₂)).comp
    (_root_.Bialgebra.TensorProduct.lid R H₂).symm.toBialgHom

@[simp]
theorem includeLeft_apply (x : H₁) : includeLeft (H₂ := H₂) x = x ⊗ₜ[R] (1 : H₂) := by
  simp [includeLeft, _root_.Bialgebra.unitBialgHom, Algebra.ofId_apply]

@[simp]
theorem includeRight_apply (y : H₂) : includeRight (H₁ := H₁) y = (1 : H₁) ⊗ₜ[R] y := by
  simp [includeRight, _root_.Bialgebra.unitBialgHom, Algebra.ofId_apply]

@[simp]
theorem toAlgHom_includeLeft :
    (includeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂).toAlgHom = Algebra.TensorProduct.includeLeft := by
  ext x
  simp only [BialgHom.coe_toAlgHom, includeLeft_apply, Algebra.TensorProduct.includeLeft_apply]

@[simp]
theorem toAlgHom_includeRight :
    (includeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂).toAlgHom = Algebra.TensorProduct.includeRight := by
  ext y
  simp only [BialgHom.coe_toAlgHom, includeRight_apply, Algebra.TensorProduct.includeRight_apply]

end Bialgebra.TensorProduct

namespace AffineGroup.Product

open Bialgebra.TensorProduct

variable {R H₁ H₂ A : Type*} [CommSemiring R]
variable [CommSemiring H₁] [CommSemiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A]

/-- The point of `Spec (H₁ ⊗[R] H₂)` glued from a pair of points of `Spec H₁` and `Spec H₂`,
via the universal property of the tensor product: `x ⊗ₜ y ↦ f₁ x * f₂ y`. -/
noncomputable def glue (f₁ : H₁ →ₐ[R] A) (f₂ : H₂ →ₐ[R] A) : (H₁ ⊗[R] H₂) →ₐ[R] A :=
  Algebra.TensorProduct.lift f₁ f₂ fun _ _ => .all _ _

@[simp]
theorem glue_tmul (f₁ : H₁ →ₐ[R] A) (f₂ : H₂ →ₐ[R] A) (x : H₁) (y : H₂) :
    glue f₁ f₂ (x ⊗ₜ[R] y) = f₁ x * f₂ y := rfl

@[simp]
theorem glue_comp_includeLeft (f₁ : H₁ →ₐ[R] A) (f₂ : H₂ →ₐ[R] A) :
    (glue f₁ f₂).comp Algebra.TensorProduct.includeLeft = f₁ :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _

@[simp]
theorem glue_comp_includeRight (f₁ : H₁ →ₐ[R] A) (f₂ : H₂ →ₐ[R] A) :
    (glue f₁ f₂).comp Algebra.TensorProduct.includeRight = f₂ :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _

/-- A point of `Spec (H₁ ⊗[R] H₂)` is recovered by gluing its two restrictions. -/
@[simp]
theorem glue_restrict (g : (H₁ ⊗[R] H₂) →ₐ[R] A) :
    glue (g.comp Algebra.TensorProduct.includeLeft) (g.comp Algebra.TensorProduct.includeRight) =
      g := by
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [glue_tmul, AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]

/-- Restriction of a point of `Spec (H₁ ⊗[R] H₂)` to its two factors, as a monoid homomorphism
of convolution monoids: it pre-composes with the two inclusions `includeLeft` and
`includeRight`. Each component is `TauCeti.AlgHom.mapDomain` of a bialgebra morphism, hence a
monoid homomorphism, so their pairing is too. -/
noncomputable def restrictHom :
    WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A) →*
      WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A) :=
  (AlgHom.mapDomain includeLeft).prod (AlgHom.mapDomain includeRight)

@[simp]
theorem restrictHom_apply (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    restrictHom f = (AlgHom.mapDomain includeLeft f, AlgHom.mapDomain includeRight f) := rfl

/-- The convolution monoid of `R`-algebra homomorphisms out of a tensor product of commutative
bialgebras `H₁ ⊗[R] H₂` is the product of the convolution monoids out of `H₁` and `H₂`.

On the functor of points this is the direct product of the affine group schemes `Spec H₁` and
`Spec H₂`: a point of the product sends `x ⊗ₜ y` to `f₁ x * f₂ y`, and convolution is computed
componentwise. When `H₁` and `H₂` are Hopf algebras these convolution monoids are groups
(`TauCeti.AlgHom.instGroup`), so this is automatically an isomorphism of groups. -/
noncomputable def pointsMulEquiv :
    WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A) ≃* WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A) where
  toFun := restrictHom
  invFun p := toConv (glue p.1.ofConv p.2.ofConv)
  left_inv f := by
    apply WithConv.ofConv_injective
    simp only [restrictHom_apply, AlgHom.mapDomain_apply, ofConv_toConv,
      toAlgHom_includeLeft, toAlgHom_includeRight, glue_restrict]
  right_inv p := by
    obtain ⟨f₁, f₂⟩ := p
    simp only [restrictHom_apply, AlgHom.mapDomain_apply,
      toAlgHom_includeLeft, toAlgHom_includeRight, glue_comp_includeLeft, glue_comp_includeRight,
      toConv_ofConv]
  map_mul' := restrictHom.map_mul

@[simp]
theorem pointsMulEquiv_apply (f : WithConv ((H₁ ⊗[R] H₂) →ₐ[R] A)) :
    pointsMulEquiv f =
      (AlgHom.mapDomain includeLeft f, AlgHom.mapDomain includeRight f) := rfl

@[simp]
theorem pointsMulEquiv_symm_apply
    (p : WithConv (H₁ →ₐ[R] A) × WithConv (H₂ →ₐ[R] A)) :
    pointsMulEquiv.symm p = toConv (glue p.1.ofConv p.2.ofConv) := rfl

end AffineGroup.Product

end TauCeti
