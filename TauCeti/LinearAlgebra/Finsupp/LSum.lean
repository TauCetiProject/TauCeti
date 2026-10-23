/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Linear maps out of free modules in terms of their values on the basis

A linear map out of the free module `ι →₀ A` is determined by its values on the basis vectors
`Finsupp.single i 1`. This file records the resulting expansion of `f z` as a finite sum, and its
coordinatewise form for maps between free modules, where the values `f (Finsupp.single i 1) j`
are the matrix coefficients of `f`.

## Main results

* `LinearMap.apply_eq_finsuppSum_smul`: `f z = z.sum fun i a ↦ a • f (Finsupp.single i 1)`.
* `LinearMap.apply_apply_eq_finsuppSum_mul`: the `j`-th coordinate of `f z` is
  `z.sum fun i a ↦ a * f (Finsupp.single i 1) j`.
-/

public section

namespace LinearMap

variable {A M ι κ : Type*} [Semiring A] [AddCommMonoid M] [Module A M]

/-- A linear map out of a free module is the finite sum of its values on the basis vectors,
weighted by the coordinates. -/
theorem apply_eq_finsuppSum_smul (f : (ι →₀ A) →ₗ[A] M) (z : ι →₀ A) :
    f z = z.sum fun i a ↦ a • f (Finsupp.single i 1) := by
  conv_lhs => rw [← z.sum_single]
  rw [map_finsuppSum]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [← Finsupp.smul_single_one, map_smul]

/-- A linear map between free modules is determined by its matrix coefficients: the `j`-th
coordinate of `f z` is `∑ i, z i * (f (Finsupp.single i 1)) j`. -/
theorem apply_apply_eq_finsuppSum_mul (f : (ι →₀ A) →ₗ[A] (κ →₀ A)) (z : ι →₀ A) (j : κ) :
    f z j = z.sum fun i a ↦ a * f (Finsupp.single i 1) j := by
  rw [f.apply_eq_finsuppSum_smul, Finsupp.sum_apply]
  rfl

end LinearMap
