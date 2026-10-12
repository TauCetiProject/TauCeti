/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Separating tensors by linear functionals

Separating families of linear functionals detect zero tensors by contraction, first in one
factor and then in both, over a commutative semiring with a projective right factor.
These lemmas supply the shared separation step for rational-point separation and reducedness
of tensor products of algebras. Over a field, every module is projective.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Contracting against a separating family in the left factor detects zero tensors when the
right factor is projective. -/
theorem tensor_eq_zero_of_forall_lid_rTensor_eq_zero
    {R M N ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.Projective R N]
    (f : ι → M →ₗ[R] R) (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (x : M ⊗[R] N)
    (hx : ∀ i, TensorProduct.lid R N ((f i).rTensor N x) = 0) :
    x = 0 := by
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  simp only [map_zero]
  apply hf
  intro i
  exact (DFunLike.congr_fun ((f i).comp_tensorComponent φ) x).trans
    (by simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx i, map_zero])

/-- Products of separating families of linear functionals detect zero tensors when the
right factor is projective. -/
theorem tensor_eq_zero_of_forall_lid_map_eq_zero
    {R M N ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.Projective R N]
    (f : ι → M →ₗ[R] R) (g : κ → N →ₗ[R] R)
    (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (hg : ∀ n, (∀ j, g j n = 0) → n = 0)
    (x : M ⊗[R] N)
    (hx : ∀ i j, TensorProduct.lid R R (TensorProduct.map (f i) (g j) x) = 0) :
    x = 0 := by
  apply tensor_eq_zero_of_forall_lid_rTensor_eq_zero f hf x
  intro i
  apply hg
  intro j
  have hcomp : (g j).comp ((TensorProduct.lid R N).toLinearMap.comp
      (TensorProduct.map (f i) LinearMap.id)) =
      (TensorProduct.lid R R).toLinearMap.comp (TensorProduct.map (f i) (g j)) := by
    ext m n
    simp
  exact (DFunLike.congr_fun hcomp x).trans (hx i j)

end TauCeti
