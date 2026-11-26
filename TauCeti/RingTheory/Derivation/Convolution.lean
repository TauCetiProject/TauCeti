/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Derivation.Basic
public import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Derivations of convolution products

Let `C` be a coalgebra over `R` and `A` a commutative `R`-algebra. Linear maps `C → A` form a
ring under convolution, `(f ⋆ g) c = ∑ f c₁ * g c₂`. A derivation `D` of the coefficient algebra
`A` acts on them by postcomposition, and it differentiates convolution products by the Leibniz
rule. This is the rule used to differentiate points of an affine group scheme, which are
convolution-invertible algebra maps out of its coordinate Hopf algebra.

Dually, the derivative `D ∘ g` of an algebra map `g` into `A` is a derivation at `g`: composed
with multiplication it is `g ⊠ (D ∘ g) + (D ∘ g) ⊠ g`, in the exterior convolution product
`WithConv.mulTensor`. This is the Leibniz counterpart of
`AlgHom.toConv_toLinearMap_comp_mul'`.

## Main results

* `Derivation.toConv_comp_convMul`: the Leibniz rule for convolution products.
* `Derivation.toConv_comp_toLinearMap_comp_mul'`: the derivative of an algebra map is a
  derivation at that map.
-/

public section

open WithConv

namespace Derivation

variable {R C A : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [CoalgebraStruct R C]
  [CommSemiring A] [Algebra R A]

/-- **The Leibniz rule for convolution**: a derivation `D` of the coefficient algebra
differentiates a convolution product factor by factor,
`D ∘ (f ⋆ g) = (D ∘ f) ⋆ g + f ⋆ (D ∘ g)`. -/
theorem toConv_comp_convMul (D : Derivation R A A) (f g : WithConv (C →ₗ[R] A)) :
    toConv ((D : A →ₗ[R] A) ∘ₗ (f * g).ofConv) =
      toConv ((D : A →ₗ[R] A) ∘ₗ f.ofConv) * g + f * toConv ((D : A →ₗ[R] A) ∘ₗ g.ofConv) := by
  refine ofConv_injective (LinearMap.ext fun c => ?_)
  simp [(Coalgebra.Repr.arbitrary R c).convMul_apply, Finset.sum_add_distrib, D.leibniz,
    mul_comm, add_comm]

/-- The derivative `D ∘ g` of an algebra map `g : S → A` is a derivation at `g`: composed with
the multiplication of `S` it is `g ⊠ (D ∘ g) + (D ∘ g) ⊠ g`. This is the Leibniz counterpart of
`AlgHom.toConv_toLinearMap_comp_mul'`. -/
theorem toConv_comp_toLinearMap_comp_mul' {S : Type*} [Semiring S] [Algebra R S]
    (D : Derivation R A A) (g : S →ₐ[R] A) :
    toConv ((D : A →ₗ[R] A) ∘ₗ g.toLinearMap ∘ₗ LinearMap.mul' R S) =
      mulTensor (toConv g.toLinearMap) (toConv ((D : A →ₗ[R] A) ∘ₗ g.toLinearMap)) +
        mulTensor (toConv ((D : A →ₗ[R] A) ∘ₗ g.toLinearMap)) (toConv g.toLinearMap) := by
  refine ofConv_injective (TensorProduct.ext' fun x y => ?_)
  simp [D.leibniz, mul_comm]

end Derivation
