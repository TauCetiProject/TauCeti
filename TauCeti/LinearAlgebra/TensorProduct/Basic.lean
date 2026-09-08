/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor-product contractions

This file defines contraction of a tensor product against a linear functional on its right factor,
and records its behavior on pure tensors and under tensor-product maps.

## Main declarations

* `TauCeti.LinearMap.tensorComponent`: contraction against the right factor of a tensor product.
* `TauCeti.LinearMap.tensorComponent_map`: naturality of contraction under `TensorProduct.map`.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace TauCeti.LinearMap

universe u v w x y

variable {R : Type u} {M : Type v} {N : Type w}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]

/-- Apply a linear functional to the right factor of a tensor. -/
noncomputable def tensorComponent (phi : N →ₗ[R] R) : M ⊗[R] N →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ phi.lTensor M

/-- A right tensor component sends a pure tensor to the corresponding scalar multiple. -/
@[simp]
theorem tensorComponent_tmul (phi : N →ₗ[R] R) (m : M) (n : N) :
    tensorComponent (R := R) (M := M) phi (m ⊗ₜ[R] n) = phi n • m := by
  simp [tensorComponent]

/-- Taking a right tensor component commutes with a map on both tensor factors. -/
@[simp]
theorem tensorComponent_map {M' : Type x} {N' : Type y}
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (phi : N' →ₗ[R] R) (f : M →ₗ[R] M') (g : N →ₗ[R] N') (t : M ⊗[R] N) :
    tensorComponent phi (TensorProduct.map f g t) =
      f (tensorComponent (phi.comp g) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp

/-- Contraction by the zero functional is the zero linear map. -/
@[simp]
theorem tensorComponent_zero :
    tensorComponent (R := R) (M := M) (0 : N →ₗ[R] R) = 0 := by
  refine TensorProduct.ext' fun m n => ?_
  simp

end TauCeti.LinearMap
