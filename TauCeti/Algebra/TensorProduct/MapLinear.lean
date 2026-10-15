/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor products of algebra maps as linear maps

The tensor product `Algebra.TensorProduct.map f g` of two algebra maps is, as a function, the
tensor product `TensorProduct.map` of their underlying linear maps. This file records that
identity pointwise, and its consequence for a tensor product of linear maps applied after a tensor
product of algebra maps: the result is the tensor product of the two composites. These are the
forms needed to evaluate linear functionals on one tensor factor after an algebra map has been
applied to the other.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R A B C D : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
  [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-- The tensor product of two algebra maps acts as the tensor product of their underlying linear
maps. -/
theorem map_apply_eq_map (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    map f g z = _root_.TensorProduct.map f.toLinearMap g.toLinearMap z := by
  rw [← AlgHom.toLinearMap_apply, toLinearMap_map, TensorProduct.AlgebraTensorModule.map_eq]

variable {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- A tensor product of linear maps applied after a tensor product of algebra maps is the tensor
product of the two composites. -/
theorem _root_.TensorProduct.map_algebraTensorProduct_map (f₂ : C →ₗ[R] M) (g₂ : D →ₗ[R] N)
    (f₁ : A →ₐ[R] C) (g₁ : B →ₐ[R] D) (z : A ⊗[R] B) :
    _root_.TensorProduct.map f₂ g₂ (map f₁ g₁ z) =
      _root_.TensorProduct.map (f₂ ∘ₗ f₁.toLinearMap) (g₂ ∘ₗ g₁.toLinearMap) z := by
  rw [map_apply_eq_map, ← LinearMap.comp_apply, ← _root_.TensorProduct.map_comp]

end Algebra.TensorProduct
