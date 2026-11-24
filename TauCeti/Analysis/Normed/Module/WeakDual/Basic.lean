/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuous functions on weak-star dual balls

When the scalar field `𝕜` is proper (for example `ℝ` or `ℂ`), Banach–Alaoglu makes every
closed dual ball compact in the weak-star topology.
Over any `𝕜`, the norm of evaluation, raised to a nonnegative exponent, is a continuous
real-valued function on such a ball, `WeakDual.evalRpow`. This bundled function supplies the
integrand in Pietsch domination.

Evaluation at a vector is itself a continuous function on such a ball. For proper `𝕜`,
`WeakDual.evalClosedBall` bundles `x ↦ (φ ↦ φ x)` as a bounded operator from `E` into the
space of continuous functions on the (compact) ball of radius `r`, with the sup norm.
Its norm is at most `max r 0`, so at most `r` when `0 ≤ r`, and it is `0` when `r ≤ 0`. On the
unit ball it is the canonical map of `E` into `C(B, 𝕜)` through which Pietsch factorization
passes to `Lᵖ`.
-/

public section

open scoped ENNReal

namespace WeakDual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For a proper scalar field `𝕜` (for example `ℝ` or `ℂ`), a closed dual ball, with its
weak-star topology, is compact by Banach–Alaoglu. -/
instance [ProperSpace 𝕜] (f : StrongDual 𝕜 E) (r : ℝ) :
    CompactSpace (toStrongDual ⁻¹' Metric.closedBall f r : Set (WeakDual 𝕜 E)) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall f r)

/-- The continuous function `φ ↦ ‖φ x‖ ^ p.toReal` on the weak-star closed ball of radius `r`.
For `p = 0` and `p = ∞` the exponent is `0`, so this is the constant function `1`
(`evalRpow_zero`, `evalRpow_top`). -/
noncomputable def evalRpow (r : ℝ) (p : ℝ≥0∞) (x : E) :
    C(toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r, ℝ) where
  toFun φ := ‖(φ : WeakDual 𝕜 E) x‖ ^ p.toReal
  continuous_toFun :=
    ((eval_continuous x).comp continuous_subtypeVal).norm.rpow_const
      fun _ ↦ Or.inr ENNReal.toReal_nonneg

@[simp]
theorem evalRpow_apply (r : ℝ) (p : ℝ≥0∞) (x : E)
    (φ : toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) :
    evalRpow r p x φ = ‖(φ : WeakDual 𝕜 E) x‖ ^ p.toReal := by
  simp [evalRpow]

/-- For `p = 0` the exponent `p.toReal` is `0`, so `evalRpow r 0 x` is the constant `1`. -/
@[simp]
theorem evalRpow_zero (r : ℝ) (x : E) : evalRpow (𝕜 := 𝕜) r 0 x = 1 := by
  ext
  simp

/-- For `p = ∞` the exponent `p.toReal` is `0`, so `evalRpow r ∞ x` is the constant `1`. -/
@[simp]
theorem evalRpow_top (r : ℝ) (x : E) : evalRpow (𝕜 := 𝕜) r ∞ x = 1 := by
  ext
  simp

variable [ProperSpace 𝕜]

/-- Evaluation `x ↦ (φ ↦ φ x)`, as a bounded operator from `E` into the continuous functions on
the weak-star closed dual ball of radius `r`. -/
noncomputable def evalClosedBall (r : ℝ) :
    E →L[𝕜] C(toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r, 𝕜) :=
  LinearMap.mkContinuous
    { toFun x := ⟨fun φ ↦ (φ : WeakDual 𝕜 E) x, (eval_continuous x).comp continuous_subtypeVal⟩
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp }
    (max r 0) fun x ↦ (ContinuousMap.norm_le _ (by positivity)).2 fun φ ↦
      ((toStrongDual (φ : WeakDual 𝕜 E)).le_opNorm x).trans <| by
        gcongr
        exact (mem_closedBall_zero_iff.1 φ.property).trans (le_max_left r 0)

@[simp]
theorem evalClosedBall_apply_apply (r : ℝ) (x : E)
    (φ : toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) :
    evalClosedBall r x φ = (φ : WeakDual 𝕜 E) x := by
  simp [evalClosedBall]

/-- Evaluation on the dual ball of radius `r` has operator norm at most `max r 0`, so at most `r`
when `0 ≤ r`; for `r ≤ 0` the operator is `0` (`evalClosedBall_eq_zero_of_nonpos`). -/
theorem norm_evalClosedBall_le (r : ℝ) :
    ‖evalClosedBall (𝕜 := 𝕜) (E := E) r‖ ≤ max r 0 := by
  rw [evalClosedBall]
  exact LinearMap.mkContinuous_norm_le _ (le_max_right r 0) _

/-- For `r ≤ 0` the dual ball of radius `r` is empty or `{0}`, so evaluation on it is `0`. -/
@[simp]
theorem evalClosedBall_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    evalClosedBall (𝕜 := 𝕜) (E := E) r = 0 := by
  ext x φ
  have h := ((toStrongDual (φ : WeakDual 𝕜 E)).le_opNorm x).trans <|
    mul_le_mul_of_nonneg_right ((mem_closedBall_zero_iff.1 φ.property).trans hr) (norm_nonneg x)
  simpa using h

end WeakDual
