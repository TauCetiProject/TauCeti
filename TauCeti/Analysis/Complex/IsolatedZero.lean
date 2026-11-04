/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Analytic.IsolatedZeros

/-!
# Estimates and null sets for isolated zeros

Two facts about the zeros of a function on a circle. A continuous function with no zero on a
sphere is bounded below there by a positive constant: this is the standing hypothesis of every
Rouché comparison on a disc, the margin a competitor has to beat, used by both
`TauCeti.Analysis.Complex.Conformal.LocalDegree` and `TauCeti.Analysis.Complex.Conformal.Hurwitz`.
And a nonzero analytic function vanishes on an interior circle only at a null set of angles.

The finiteness of the analytic order at an isolated zero, the other standing hypothesis of such a
comparison, is field-generic and lives in `TauCeti.Analysis.Analytic.Order`
(`TauCeti.analyticOrderAt_ne_top_of_forall_ne_zero`).

## Main results

* `TauCeti.exists_pos_le_norm_of_mem_sphere`: a continuous function with no zero on a sphere is
  bounded below there by a positive constant.
* `AnalyticOnNhd.volume_setOf_circleMap_eq_zero`: the angles where a nonzero analytic function
  vanishes on an interior circle form a null set.
-/

public section

open Metric MeasureTheory

namespace TauCeti

/-- A continuous zero-free function on a sphere is bounded below there by a positive constant.

No hypothesis on the radius. At `ρ = 0` the sphere is the set of points at zero distance from
`a` — the single point `a` when `E` is a metric space, but not in general, since the domain is
only assumed pseudometric. For `ρ < 0` it is empty, nothing is attained, and the bound holds
vacuously. -/
theorem exists_pos_le_norm_of_mem_sphere {E F : Type*} [PseudoMetricSpace E] [ProperSpace E]
    [NormedAddGroup F] {f : E → F} {a : E} {ρ : ℝ}
    (hcont : ContinuousOn f (sphere a ρ)) (hne : ∀ z ∈ sphere a ρ, f z ≠ 0) :
    ∃ δ > 0, ∀ z ∈ sphere a ρ, δ ≤ ‖f z‖ :=
  (isCompact_sphere a ρ).exists_forall_le' hcont.norm fun z hz => norm_pos_iff.mpr (hne z hz)

end TauCeti

/-- If `f` is analytic on `ball c R` and nonzero somewhere there, the angles at which it vanishes on
a circle about `c` of radius `r ∈ (0, R)` form a null set. -/
theorem AnalyticOnNhd.volume_setOf_circleMap_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} {r R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball c R)) {w : ℂ}
    (hw : w ∈ ball c R) (hfw : f w ≠ 0) (hr : 0 < r) (hrR : r < R) :
    volume {θ | f (circleMap c r θ) = 0} = 0 := by
  refine Set.Countable.measure_zero (((hf.finite_setOf_mem_and_eq_zero_of_isCompact
    (convex_ball c R).isPreconnected hw hfw (isCompact_sphere c r)
    (sphere_subset_ball hrR)).countable.preimage_circleMap c hr.ne').mono ?_) _
  exact fun θ hθ ↦ ⟨circleMap_mem_sphere c hr.le θ, hθ⟩
