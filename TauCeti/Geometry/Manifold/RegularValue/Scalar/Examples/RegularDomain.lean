/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Defining functions of regular domains: regular and critical values

A regular domain `{ρ ≥ 0}` in a boundaryless manifold is built from a function `ρ` with `0` as a
regular value (RiemannianManifoldsWithConvexBoundary §3.1). This file checks that hypothesis on
functions on a real inner product space `E`, where it reads: at every zero of `ρ` the derivative
of `ρ` is nonzero.

* **A positive multiplier.** For a unit vector `e`, `ρ(x) = e^{⟪e, x⟫} (1 - ‖x‖²)` has `0` as a
  regular value (`TauCeti.isRegularValue_exp_inner_mul_one_sub_norm_sq`), and `{ρ ≥ 0}` is the
  closed unit ball (`TauCeti.setOf_nonneg_exp_inner_mul_one_sub_norm_sq`): the multiplier
  `e^{⟪e, x⟫}` is positive everywhere.
* **A multiplier positive only on the ball.** For a unit vector `e`,
  `ρ(x) = (2 + ⟪e, x⟫) (1 - ‖x‖²)` is positive inside the ball, but `ρ(-3e) = 8`
  (`TauCeti.two_add_inner_mul_one_sub_norm_sq_neg_three_smul`). The set `{ρ ≥ 0}` is the ball
  together with the half-space `{⟪e, x⟫ ≤ -2}`
  (`TauCeti.setOf_nonneg_two_add_inner_mul_one_sub_norm_sq`), and `0` is a regular value of `ρ`
  (`TauCeti.isRegularValue_two_add_inner_mul_one_sub_norm_sq`): on the hyperplane
  `{⟪e, x⟫ = -2}`, `dρ(e) = 1 - ‖x‖² ≤ -3`, and on the sphere `dρ(x) = -2 (2 + ⟪e, x⟫) < 0`. So
  `ρ` defines a different regular domain from the ball.
* **A critical value.** For `E ≠ 0`, `ρ(x) = (1 - ‖x‖²)³` has `0` as a critical value: its
  derivative vanishes on the unit sphere (`TauCeti.not_isRegularValue_one_sub_norm_sq_pow_three`),
  although `{ρ ≥ 0}` is the closed unit ball (`TauCeti.setOf_nonneg_one_sub_norm_sq_pow_three`).
* **A cone.** On `ℝ × ℝ`, `ρ(x₀, x₁) = x₀² - x₁²` has a critical point at the origin, which lies
  in `{ρ = 0}` (`TauCeti.not_isRegularValue_sq_sub_sq`).
-/

public section

open Metric Set
open scoped Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point at which some derivative of a scalar function is nonzero is a regular point. -/
private theorem isRegularPoint_of_hasFDerivAt {ρ : E → ℝ} {D : E →L[ℝ] ℝ} {x : E}
    (hD : HasFDerivAt ρ D x) {v : E} (hv : D v ≠ 0) : IsRegularPoint 𝓘(ℝ, E) 𝓘(ℝ) ρ x := by
  rw [isRegularPoint_iff_surjective_fderiv, hD.fderiv, ContinuousLinearMap.surjective_iff_ne_zero]
  rintro rfl
  exact hv rfl

/-- A point at which the derivative of a scalar function vanishes is not a regular point. -/
private theorem not_isRegularPoint_of_hasFDerivAt_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ρ : F → ℝ} {x : F} (hD : HasFDerivAt ρ (0 : F →L[ℝ] ℝ) x) :
    ¬ IsRegularPoint 𝓘(ℝ, F) 𝓘(ℝ) ρ x := by
  rw [isRegularPoint_iff_surjective_fderiv, hD.fderiv, ContinuousLinearMap.surjective_iff_ne_zero]
  exact fun h ↦ h rfl

/-- The derivative of `x ↦ 1 - ‖x‖²` is `v ↦ -2 ⟪x, v⟫`. -/
private theorem hasFDerivAt_one_sub_norm_sq (x : E) :
    HasFDerivAt (fun y : E ↦ 1 - ‖y‖ ^ 2) (-(2 • innerSL ℝ x)) x :=
  (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_sub 1

/-! ### A positive multiplier -/

/-- **A positive multiplier defines the same set.** For a unit vector `e`,
`{x | e^{⟪e, x⟫} (1 - ‖x‖²) ≥ 0}` is the closed unit ball. -/
theorem setOf_nonneg_exp_inner_mul_one_sub_norm_sq (e : E) :
    {x : E | 0 ≤ Real.exp ⟪e, x⟫ * (1 - ‖x‖ ^ 2)} = closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_closedBall_zero_iff, mul_nonneg_iff_of_pos_left (Real.exp_pos _),
    sub_nonneg]
  exact pow_le_one_iff_of_nonneg (norm_nonneg x) two_ne_zero

/-- **`0` is a regular value of `e^{⟪e, x⟫} (1 - ‖x‖²)`**: on the unit sphere the derivative in
the direction `x` is `-2 e^{⟪e, x⟫} ≠ 0`. -/
theorem isRegularValue_exp_inner_mul_one_sub_norm_sq (e : E) :
    IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x : E ↦ Real.exp ⟪e, x⟫ * (1 - ‖x‖ ^ 2)) 0 := by
  refine isRegularValue_iff.2 fun x hx ↦ ?_
  have hx1 : 1 - ‖x‖ ^ 2 = 0 :=
    (mul_eq_zero.1 hx).resolve_left (Real.exp_pos _).ne'
  have hA : HasFDerivAt (fun y : E ↦ Real.exp ⟪e, y⟫)
      (Real.exp ⟪e, x⟫ • innerSL ℝ e) x :=
    ((innerSL ℝ e).hasFDerivAt (x := x)).exp
  refine isRegularPoint_of_hasFDerivAt (hA.mul (hasFDerivAt_one_sub_norm_sq x)) (v := x) ?_
  have hn : ‖x‖ ^ 2 = 1 := by linarith
  simp [hn, (Real.exp_pos _).ne']

/-! ### A multiplier positive only on the ball -/

/-- The multiplier `2 + ⟪e, x⟫` takes the value `-1` at `-3e` for a unit vector `e`, and
`(2 + ⟪e, x⟫) (1 - ‖x‖²) = (-1)(-8) = 8` there. -/
theorem two_add_inner_mul_one_sub_norm_sq_neg_three_smul {e : E} (he : ‖e‖ = 1) :
    (2 + ⟪e, (-3 : ℝ) • e⟫) * (1 - ‖(-3 : ℝ) • e‖ ^ 2) = 8 := by
  rw [inner_smul_right, real_inner_self_eq_norm_sq, norm_smul, he]
  norm_num

/-- **The set defined by `(2 + ⟪e, x⟫) (1 - ‖x‖²)`.** For a unit vector `e`,
`{x | (2 + ⟪e, x⟫) (1 - ‖x‖²) ≥ 0}` is the closed unit ball together with the half-space
`{⟪e, x⟫ ≤ -2}`. -/
theorem setOf_nonneg_two_add_inner_mul_one_sub_norm_sq {e : E} (he : ‖e‖ = 1) :
    {x : E | 0 ≤ (2 + ⟪e, x⟫) * (1 - ‖x‖ ^ 2)} = closedBall 0 1 ∪ {x | ⟪e, x⟫ ≤ -2} := by
  ext x
  have hex : |⟪e, x⟫| ≤ ‖x‖ := by
    simpa [he] using abs_real_inner_le_norm e x
  have hn := norm_nonneg x
  simp only [mem_ofPred_eq, mem_union, mem_closedBall_zero_iff, mul_nonneg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · left
      nlinarith
    · right
      linarith
  · rintro (h | h)
    · left
      constructor
      · linarith [neg_abs_le ⟪e, x⟫]
      · nlinarith
    · right
      constructor
      · linarith
      · nlinarith [neg_abs_le ⟪e, x⟫]

/-- **`0` is a regular value of `(2 + ⟪e, x⟫) (1 - ‖x‖²)`** for a unit vector `e`: on the
hyperplane `{⟪e, x⟫ = -2}` the derivative in the direction `e` is `1 - ‖x‖² ≤ -3`, and on the
unit sphere the derivative in the direction `x` is `-2 (2 + ⟪e, x⟫) ≤ -2`. -/
theorem isRegularValue_two_add_inner_mul_one_sub_norm_sq {e : E} (he : ‖e‖ = 1) :
    IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x : E ↦ (2 + ⟪e, x⟫) * (1 - ‖x‖ ^ 2)) 0 := by
  refine isRegularValue_iff.2 fun x hx ↦ ?_
  have hex : |⟪e, x⟫| ≤ ‖x‖ := by
    simpa [he] using abs_real_inner_le_norm e x
  have hA : HasFDerivAt (fun y : E ↦ 2 + ⟪e, y⟫) (innerSL ℝ e) x :=
    ((innerSL ℝ e).hasFDerivAt (x := x)).const_add 2
  have hD := hA.mul (hasFDerivAt_one_sub_norm_sq x)
  rcases mul_eq_zero.1 hx with h | h
  · refine isRegularPoint_of_hasFDerivAt hD (v := e) ?_
    have hx2 : 2 ≤ ‖x‖ := by linarith [neg_abs_le ⟪e, x⟫]
    have : 1 - ‖x‖ ^ 2 < 0 := by nlinarith
    simp [h, he, this.ne]
  · refine isRegularPoint_of_hasFDerivAt hD (v := x) ?_
    have hn : ‖x‖ ^ 2 = 1 := by linarith
    have hx1 : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x]
    have : 0 < 2 + ⟪e, x⟫ := by linarith [neg_abs_le ⟪e, x⟫]
    simp [hn, this.ne']

/-! ### A critical value -/

omit [InnerProductSpace ℝ E] in
/-- **The set `{(1 - ‖x‖²)³ ≥ 0}` is the closed unit ball.** -/
theorem setOf_nonneg_one_sub_norm_sq_pow_three :
    {x : E | 0 ≤ (1 - ‖x‖ ^ 2) ^ 3} = closedBall 0 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_closedBall_zero_iff, Odd.pow_nonneg_iff (by decide : Odd 3),
    sub_nonneg]
  exact pow_le_one_iff_of_nonneg (norm_nonneg x) two_ne_zero

/-- **`0` is a critical value of `(1 - ‖x‖²)³`** on a nonzero inner product space: the
derivative `3 (1 - ‖x‖²)² · (-2 ⟪x, ·⟫)` vanishes on the unit sphere, where the function
vanishes. -/
theorem not_isRegularValue_one_sub_norm_sq_pow_three [Nontrivial E] :
    ¬ IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) (fun x : E ↦ (1 - ‖x‖ ^ 2) ^ 3) 0 := by
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  have h0 : 1 - ‖x‖ ^ 2 = 0 := by simp [hx]
  have hD : HasFDerivAt (fun y : E ↦ (1 - ‖y‖ ^ 2) ^ 3) (0 : E →L[ℝ] ℝ) x :=
    ((hasFDerivAt_one_sub_norm_sq x).pow 3).congr_fderiv (by simp [h0])
  exact fun h ↦ not_isRegularPoint_of_hasFDerivAt_zero hD
    (isRegularValue_iff.1 h x (by simp [h0]))

/-! ### A cone -/

/-- **`0` is a critical value of `x₀² - x₁²`** on `ℝ × ℝ`: its derivative vanishes at the origin,
which lies in the zero set, where `{x₀² - x₁² ≥ 0}` is a double cone. -/
theorem not_isRegularValue_sq_sub_sq :
    ¬ IsRegularValue 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) (fun p : ℝ × ℝ ↦ p.1 ^ 2 - p.2 ^ 2) 0 := by
  have hD : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 ^ 2 - p.2 ^ 2) (0 : ℝ × ℝ →L[ℝ] ℝ) 0 := by
    have h1 : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) 0 :=
      hasFDerivAt_fst
    have h2 : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) 0 :=
      hasFDerivAt_snd
    exact ((h1.pow 2).sub (h2.pow 2)).congr_fderiv (by simp)
  exact fun h ↦ not_isRegularPoint_of_hasFDerivAt_zero hD
    (isRegularValue_iff.1 h 0 (by simp))

end TauCeti
