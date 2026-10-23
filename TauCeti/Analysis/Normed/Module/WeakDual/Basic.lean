/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuous functions on weak-star dual balls

Banach–Alaoglu makes every closed dual ball compact in the weak-star topology.
The norm of evaluation, raised to a nonnegative exponent, is a continuous real-valued
function on such a ball. This bundled function supplies the integrand in Pietsch domination.
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

end WeakDual
