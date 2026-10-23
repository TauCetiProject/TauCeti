/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Separating tensors by linear maps

Families of linear maps detecting zero in the left factor also detect zero after tensoring
with a projective right factor over a commutative semiring. Products of separating families
of linear functionals likewise detect zero tensors by contraction in both factors.
These lemmas supply the shared separation step for rational-point separation and reducedness
of tensor products of algebras. Over a field, every module is projective.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Tensoring a family of linear maps detecting zero with a projective module preserves
zero detection. The maps may take values in any module. -/
theorem tensor_eq_zero_of_forall_rTensor_eq_zero
    {R M N P ι : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [Module.Projective R N]
    [AddCommMonoid P] [Module R P]
    (f : ι → M →ₗ[R] P) (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (x : M ⊗[R] N) (hx : ∀ i, (f i).rTensor N x = 0) :
    x = 0 := by
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  simp only [map_zero]
  apply hf
  intro i
  simpa only [← LinearMap.rTensor_def, hx i, map_zero, LinearMap.comp_id] using
    (LinearMap.tensorComponent_map φ (f i) LinearMap.id x).symm

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
  apply tensor_eq_zero_of_forall_rTensor_eq_zero f hf x
  intro i
  apply (TensorProduct.lid R N).injective
  simp only [map_zero]
  apply hg
  intro j
  have hcomp : (g j).comp ((TensorProduct.lid R N).toLinearMap.comp
      (TensorProduct.map (f i) LinearMap.id)) =
      (TensorProduct.lid R R).toLinearMap.comp (TensorProduct.map (f i) (g j)) := by
    ext m n
    simp
  exact (DFunLike.congr_fun hcomp x).trans (hx i j)

end TauCeti
