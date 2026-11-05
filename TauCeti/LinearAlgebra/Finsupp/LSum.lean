/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Linear maps out of free modules in terms of their values on the basis

A linear map out of the free module `ι →₀ A` is determined by its values on the basis vectors
`Finsupp.single i 1`. This file records the resulting expansion of `f z` as a finite sum, and its
coordinatewise form for maps between free modules, where the values `f (Finsupp.single i 1) j`
are the matrix coefficients of `f`.

Over a linearly ordered field, a linear functional on `ι →₀ 𝕜` that is bounded below on the
nonnegative functions is nonnegative on them, since the nonnegative functions form a cone.

## Main results

* `LinearMap.apply_eq_finsuppSum_smul`: `f z = z.sum fun i a ↦ a • f (Finsupp.single i 1)`.
* `LinearMap.apply_apply_eq_finsuppSum_mul`: the `j`-th coordinate of `f z` is
  `z.sum fun i a ↦ a * f (Finsupp.single i 1) j`.
* `LinearMap.apply_nonneg_of_forall_le`: a linear functional bounded below on the
  nonnegative functions is nonnegative on them.
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

/-- A linear functional on `ι →₀ 𝕜` that is bounded below on the nonnegative functions is
nonnegative on them. -/
theorem apply_nonneg_of_forall_le {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (ψ : (ι →₀ 𝕜) →ₗ[𝕜] 𝕜) {u : 𝕜} (hψ : ∀ w : ι →₀ 𝕜, 0 ≤ w → u ≤ ψ w)
    {w : ι →₀ 𝕜} (hw : 0 ≤ w) : 0 ≤ ψ w := by
  have hu : u ≤ 0 := (hψ 0 le_rfl).trans_eq (map_zero ψ)
  -- `t • w` is nonnegative, so `u ≤ t ψ w`, for every `t ≥ 0`.
  by_contra! hneg
  have ht : 0 ≤ u / ψ w := div_nonneg_of_nonpos hu hneg.le
  have hle := hψ ((u / ψ w + 1) • w) (smul_nonneg (by linarith) hw)
  rw [map_smul, smul_eq_mul] at hle
  have hcancel : (u / ψ w + 1) * ψ w = u + ψ w := by
    field_simp [hneg.ne]
  linarith

end LinearMap
