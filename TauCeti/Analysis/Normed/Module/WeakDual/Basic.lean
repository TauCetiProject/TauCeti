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

Banach–Alaoglu makes every closed dual ball compact in the weak-star topology.
The norm of evaluation, raised to a nonnegative exponent, is a continuous real-valued
function on such a ball. This bundled function supplies the integrand in Pietsch domination.

Evaluation at a vector is itself a continuous function on such a ball, and
`WeakDual.evalClosedBall` bundles `x ↦ (φ ↦ φ x)` as a bounded operator from `E` into the
continuous functions on the ball of radius `r`, of norm at most `r`. On the unit ball it is the
canonical map of `E` into `C(B, 𝕜)` through which Pietsch factorization passes to `Lᵖ`.
-/

public section

open scoped ENNReal

namespace WeakDual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A closed dual ball, with its weak-star topology, is compact by Banach–Alaoglu. -/
instance [ProperSpace 𝕜] (f : StrongDual 𝕜 E) (r : ℝ) :
    CompactSpace (toStrongDual ⁻¹' Metric.closedBall f r : Set (WeakDual 𝕜 E)) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall f r)

/-- The continuous function `φ ↦ ‖φ x‖ ^ p` on the weak-star closed ball of radius `r`. -/
noncomputable def evalRpow (r : ℝ) (p : ℝ≥0∞) (x : E) :
    C(toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r, ℝ) where
  toFun φ := ‖(φ : WeakDual 𝕜 E) x‖ ^ p.toReal
  continuous_toFun :=
    ((eval_continuous x).comp continuous_subtype_val).norm.rpow_const
      fun _ ↦ Or.inr ENNReal.toReal_nonneg

@[simp]
theorem evalRpow_apply (r : ℝ) (p : ℝ≥0∞) (x : E)
    (φ : toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) :
    evalRpow r p x φ = ‖(φ : WeakDual 𝕜 E) x‖ ^ p.toReal := by
  simp [evalRpow]

variable [ProperSpace 𝕜]

/-- Evaluation `x ↦ (φ ↦ φ x)`, as a bounded operator from `E` into the continuous functions on
the weak-star closed dual ball of radius `r`. -/
noncomputable def evalClosedBall (r : ℝ) :
    E →L[𝕜] C(toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r, 𝕜) :=
  LinearMap.mkContinuous
    { toFun x := ⟨fun φ ↦ (φ : WeakDual 𝕜 E) x, (eval_continuous x).comp continuous_subtype_val⟩
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp }
    (max r 0) fun x ↦ (ContinuousMap.norm_le _ (by positivity)).2 fun φ ↦
      ((toStrongDual (φ : WeakDual 𝕜 E)).le_opNorm x).trans <| by
        gcongr
        exact (mem_closedBall_zero_iff.1 φ.2).trans (le_max_left r 0)

@[simp]
theorem evalClosedBall_apply_apply (r : ℝ) (x : E)
    (φ : toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) :
    evalClosedBall r x φ = (φ : WeakDual 𝕜 E) x := by
  simp [evalClosedBall]

/-- Evaluation on the dual ball of radius `r ≥ 0` has operator norm at most `r`. -/
theorem norm_evalClosedBall_le {r : ℝ} (hr : 0 ≤ r) :
    ‖(evalClosedBall r : E →L[𝕜] C(toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r,
      𝕜))‖ ≤ r := by
  rw [evalClosedBall]
  exact (LinearMap.mkContinuous_norm_le _ (le_max_right r 0) _).trans_eq (max_eq_left hr)

end WeakDual
