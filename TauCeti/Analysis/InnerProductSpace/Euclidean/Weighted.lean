/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Weighted Euclidean realizations of integer-valued families

An integer-valued family `x : α → ℤ` with nonnegative weights `w : α → ℝ` maps `ℤ`-linearly
into `EuclideanSpace ℝ α` via `TauCeti.weightedToLp w x`, multiplying coordinate `a` by
`Real.sqrt (w a)` so that the Euclidean inner product equals `∑ a, w a * x a * y a`. When every
weight is strictly positive, this map is injective (`TauCeti.weightedToLp_injective`).

## Main results

* `TauCeti.weightedToLp`: bundled `ℤ`-linear weighted Euclidean realization
  `(α → ℤ) →ₗ[ℤ] EuclideanSpace ℝ α`.
* `TauCeti.weightedToLp_injective`: injectivity when every weight is strictly positive.
* `TauCeti.inner_weightedToLp`, `TauCeti.norm_sq_weightedToLp`: inner product and squared norm of
  `TauCeti.weightedToLp`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

/-- Weighted Euclidean realization `(α → ℤ) →ₗ[ℤ] EuclideanSpace ℝ α`, scaling coordinate `a` by
`Real.sqrt (w a)`. -/
noncomputable def weightedToLp {α : Type*} (w : α → ℝ) : (α → ℤ) →ₗ[ℤ] EuclideanSpace ℝ α where
  toFun x := WithLp.toLp 2 fun a ↦ Real.sqrt (w a) * (x a : ℝ)
  map_add' x y := by
    ext a
    simp [mul_add]
  map_smul' c x := by
    ext a
    simp [zsmul_eq_mul]
    ring

/-- Coordinate evaluation of `TauCeti.weightedToLp`. -/
@[simp]
theorem weightedToLp_ofLp {α : Type*} (w : α → ℝ) (x : α → ℤ) (a : α) :
    (weightedToLp w x).ofLp a = Real.sqrt (w a) * (x a : ℝ) := by
  rfl

/-- `TauCeti.weightedToLp w` is injective when every weight `w a` is strictly positive. -/
theorem weightedToLp_injective {α : Type*} {w : α → ℝ} (hw : ∀ a, 0 < w a) :
    Function.Injective (weightedToLp w) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  ext a
  have ha := congrArg (fun v : EuclideanSpace ℝ α ↦ v.ofLp a) hx
  simp only [weightedToLp_ofLp, WithLp.ofLp_zero, Pi.zero_apply, mul_eq_zero,
    Real.sqrt_eq_zero (hw a).le, (hw a).ne', false_or, Int.cast_eq_zero] at ha
  exact ha

/-- Inner product of two weighted Euclidean realizations when the weights `w` are nonnegative. -/
theorem inner_weightedToLp {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (x y : α → ℤ) :
    ⟪weightedToLp w x, weightedToLp w y⟫_ℝ = ∑ a : α, w a * (x a : ℝ) * (y a : ℝ) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [weightedToLp_ofLp, RCLike.inner_apply, conj_trivial]
  linear_combination (x a : ℝ) * (y a : ℝ) * Real.mul_self_sqrt (hw a)

/-- Squared norm of a weighted Euclidean realization when the weights `w` are nonnegative. -/
theorem norm_sq_weightedToLp {α : Type*} [Fintype α] {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (x : α → ℤ) :
    ‖weightedToLp w x‖ ^ 2 = ∑ a : α, w a * (x a : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_weightedToLp hw]
  refine Finset.sum_congr rfl fun a _ ↦ by ring

end TauCeti
