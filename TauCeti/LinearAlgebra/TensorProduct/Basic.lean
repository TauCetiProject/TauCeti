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
Such contractions extract coordinates and test tensor identities, supporting componentwise
arguments about coactions and weight spaces.

## Main declarations

* `LinearMap.tensorComponent`: contraction against the right factor of a tensor product.
* `LinearMap.tensorComponent_map`: naturality of contraction under `TensorProduct.map`.
* `TauCeti.LinearMap.tensorComponent_assoc_symm`: contraction commutes with reassociation.
* `TauCeti.LinearMap.comp_tensorComponent`: contraction commutes with a functional on the left.
* `TauCeti.tensorProduct_rid_rTensor_apply`: naturality of the right tensor unitor.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace LinearMap

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
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m n => simp

/-- Contraction by the zero functional is the zero linear map. -/
@[simp]
theorem tensorComponent_zero :
    tensorComponent (R := R) (M := M) (0 : N →ₗ[R] R) = 0 := by
  refine TensorProduct.ext' fun m n => ?_
  simp

end LinearMap

namespace TauCeti

namespace LinearMap

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Contraction of the last tensor factor commutes with reassociation. -/
theorem tensorComponent_assoc_symm (phi : P →ₗ[R] R) (u : M ⊗[R] (N ⊗[R] P)) :
    _root_.LinearMap.tensorComponent phi ((TensorProduct.assoc R M N P).symm u) =
      (_root_.LinearMap.tensorComponent phi).lTensor M u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul m v =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
    | tmul n p =>
      simp only [TensorProduct.assoc_symm_tmul, _root_.LinearMap.tensorComponent_tmul,
        _root_.LinearMap.lTensor_tmul, TensorProduct.tmul_smul]

/-- Applying functionals to both factors is independent of the order of contraction. -/
theorem comp_tensorComponent (psi : M →ₗ[R] R) (phi : N →ₗ[R] R) :
    psi ∘ₗ _root_.LinearMap.tensorComponent phi =
      phi ∘ₗ (TensorProduct.lid R N).toLinearMap ∘ₗ psi.rTensor N := by
  refine TensorProduct.ext' fun m n ↦ ?_
  simp only [_root_.LinearMap.comp_apply, _root_.LinearMap.tensorComponent_tmul, map_smul,
    smul_eq_mul, _root_.LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    mul_comm]

end LinearMap

variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The right tensor unitor is natural with respect to a linear map in its left factor. -/
@[simp]
theorem tensorProduct_rid_rTensor_apply (f : M →ₗ[R] N) (t : M ⊗[R] R) :
    TensorProduct.rid R N (LinearMap.rTensor R f t) = f (TensorProduct.rid R M t) := by
  induction t using TensorProduct.inductionOn with
  | tmul m r => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

end TauCeti
