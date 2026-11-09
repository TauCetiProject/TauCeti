/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Linear maps out of free modules in terms of their values on the basis

A semilinear map `f : (ι →₀ R) →ₛₗ[σ] M` out of the free module `ι →₀ R` is determined by its
values on the basis vectors `Finsupp.single i 1`. This file records the resulting expansion of
`f z` as a finite sum, and its coordinatewise form for maps between free modules, where the
values `f (Finsupp.single i 1) j` are the matrix coefficients of `f`. For a linear map,
`σ = RingHom.id R` and `RingHom.id_apply` removes the twist.

## Main results

* `LinearMap.apply_eq_finsuppSum_smul`:
  `f z = z.sum fun i a ↦ σ a • f (Finsupp.single i 1)`.
* `LinearMap.apply_apply_eq_finsuppSum_mul`: the `j`-th coordinate of `f z` is
  `z.sum fun i a ↦ σ a * f (Finsupp.single i 1) j`.
-/

public section

namespace LinearMap

variable {R S M ι κ : Type*} [Semiring R] [Semiring S] {σ : R →+* S} [AddCommMonoid M]
  [Module S M]

/-- A semilinear map out of a free module is the finite sum of its values on the basis vectors,
weighted by the images under `σ` of the coordinates. -/
theorem apply_eq_finsuppSum_smul (f : (ι →₀ R) →ₛₗ[σ] M) (z : ι →₀ R) :
    f z = z.sum fun i a ↦ σ a • f (Finsupp.single i 1) := by
  simp [← map_smulₛₗ, ← map_finsuppSum]

/-- A semilinear map between free modules is determined by its matrix coefficients: the `j`-th
coordinate of `f z` is `∑ i, σ (z i) * (f (Finsupp.single i 1)) j`. -/
theorem apply_apply_eq_finsuppSum_mul (f : (ι →₀ R) →ₛₗ[σ] (κ →₀ S)) (z : ι →₀ R) (j : κ) :
    f z j = z.sum fun i a ↦ σ a * f (Finsupp.single i 1) j := by
  simp [f.apply_eq_finsuppSum_smul z, Finsupp.sum_apply]

end LinearMap
