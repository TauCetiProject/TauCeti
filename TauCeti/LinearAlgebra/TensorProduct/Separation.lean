/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Separating tensors by linear functionals

Separating families of linear functionals detect zero tensors by contraction, first in one
factor and then in both. These lemmas supply the shared separation step for rational-point
separation and reducedness of tensor products of algebras. The proof reuses
`TensorProduct.tensor_eq_of_forall_tensorComponent_eq` and
`LinearMap.tensorComponent_map` from the existing contraction API.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-- Contracting against a separating family in the left factor detects zero tensors. -/
theorem tensor_eq_zero_of_forall_lid_rTensor_eq_zero
    {k M N ι : Type*} [Field k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (f : ι → M →ₗ[k] k) (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (x : M ⊗[k] N)
    (hx : ∀ i, TensorProduct.lid k N ((f i).rTensor N x) = 0) :
    x = 0 := by
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  simp only [map_zero]
  apply hf
  intro i
  have hz : TensorProduct.map (f i) LinearMap.id x = 0 :=
    (TensorProduct.lid k N).injective (by simpa only [LinearMap.rTensor_def, map_zero] using hx i)
  simpa [hz] using (LinearMap.tensorComponent_map φ (f i) LinearMap.id x).symm

/-- Products of separating families of linear functionals detect zero tensors. -/
theorem tensor_eq_zero_of_forall_lid_map_eq_zero
    {k M N ι κ : Type*} [Field k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N]
    (f : ι → M →ₗ[k] k) (g : κ → N →ₗ[k] k)
    (hf : ∀ m, (∀ i, f i m = 0) → m = 0)
    (hg : ∀ n, (∀ j, g j n = 0) → n = 0)
    (x : M ⊗[k] N)
    (hx : ∀ i j, TensorProduct.lid k k (TensorProduct.map (f i) (g j) x) = 0) :
    x = 0 := by
  apply tensor_eq_zero_of_forall_lid_rTensor_eq_zero f hf x
  intro i
  apply hg
  intro j
  have hcomp : (g j).comp ((TensorProduct.lid k N).toLinearMap.comp
      (TensorProduct.map (f i) LinearMap.id)) =
      (TensorProduct.lid k k).toLinearMap.comp (TensorProduct.map (f i) (g j)) := by
    ext m n
    simp
  exact (DFunLike.congr_fun hcomp x).trans (hx i j)

end TauCeti
