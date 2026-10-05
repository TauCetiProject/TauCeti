/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Scalar-composition identities under tensoring

Tensoring preserves a composite of linear maps that equals scalar multiplication. This identity
is used to invert maps after extending scalars to a ring in which the scalar is a unit.
-/

public section

namespace TauCeti

open scoped TensorProduct

/-- Tensoring a composite equal to scalar multiplication preserves that identity. -/
theorem lTensor_comp_apply_of_comp_eq_smul {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (f : M →ₗ[R] N) (f' : N →ₗ[R] M) (s : R) (h : ∀ m, f' (f m) = s • m)
    (x : P ⊗[R] M) : f'.lTensor P (f.lTensor P x) = s • x := by
  have hcomp : f'.comp f = s • LinearMap.id := LinearMap.ext h
  rw [← LinearMap.lTensor_comp_apply, hcomp]
  simp

end TauCeti
