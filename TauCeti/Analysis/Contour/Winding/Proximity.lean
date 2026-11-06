/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import Mathlib.Analysis.Convex.Segment
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Proximity
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Proximity invariance of the winding number

Two closed curves that stay closer to each other than the first one stays to `w` have the same
winding number about `w`. This is the "dog on a leash" principle: the leash from `γ₀ t` to `γ₁ t`
is too short to reach `w`, so the two walks encircle `w` the same number of times.

Continuous curves with integrable derivatives and countably many differentiability exceptions
are absolutely continuous. Their proximity invariance follows from the absolutely continuous
winding-number theorem.

The application is homotopy invariance of the winding number off the curve.
`TauCeti.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment` and
`TauCeti.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment_of_eq_endpoints` deduce invariance along
the straight-line homotopy `s ↦ (1 - s) • γ₀ + s • γ₁` from the geometric hypothesis that the
segment `[γ₀ t, γ₁ t]` misses `w` for every parameter `t`, by delegating to the absolutely
continuous counterparts in `TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Proximity`.

## Main results

* `Contour.windingNumber_eq_of_dist_lt_dist` — the raw-hypothesis form: closed curves that are
  continuous, differentiable off a countable set, and have interval-integrable derivatives, with
  `dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w` throughout, have equal winding numbers about `w`.
* `TauCeti.IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist` — the same for closed piecewise-`C¹`
  curves, whose regularity supplies the raw hypotheses on its own.
* `TauCeti.IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints` — the common-endpoint
  version for paths that need not be closed.
* `TauCeti.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment` and
  `TauCeti.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment_of_eq_endpoints` — invariance along
  the straight-line homotopy when `w ∉ [γ₀ t, γ₁ t]` for every `t`.

## Provenance

The comparison-quotient argument is the standard proof of the "dog on a leash" lemma (equivalently,
the homotopy form of Rouché's theorem); see L. Ahlfors, *Complex Analysis*, Ch. 4.
No formal source is vendored.
-/

public section

noncomputable section

open Bornology MeasureTheory Set

namespace TauCeti.Contour

variable {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- **Proximity invariance of the winding number** (the "dog on a leash" lemma). Let `γ₀` and `γ₁`
be closed curves on the oriented interval with endpoints `a`, `b`, each continuous on
`Set.uIcc a b`, differentiable off a common countable set `P`, and with interval-integrable
derivative. If at every parameter the two curves are closer to each other than `γ₀` is to `w`,
then they have the same winding number about `w`. -/
theorem windingNumber_eq_of_dist_lt_dist {P : Set ℝ} (hP : P.Countable)
    (h₀closed : γ₀ a = γ₀ b) (h₁closed : γ₁ a = γ₁ b)
    (h₀cont : ContinuousOn γ₀ (uIcc a b)) (h₁cont : ContinuousOn γ₁ (uIcc a b))
    (h₀diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ₀ t)
    (h₁diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ₁ t)
    (h₀int : IntervalIntegrable (fun t => deriv γ₀ t) volume a b)
    (h₁int : IntervalIntegrable (fun t => deriv γ₁ t) volume a b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  exact (h₀cont.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hP
    (fun t ht ↦ (h₀diff t ht).hasDerivAt) h₀int).windingNumber_eq_of_dist_lt_dist
    (h₁cont.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable hP
      (fun t ht ↦ (h₁diff t ht).hasDerivAt) h₁int) h₀closed h₁closed hlt

/-- **Proximity invariance for closed piecewise-`C¹` curves.** If two closed piecewise-`C¹` curves
stay closer to each other than the first stays to `w`, they have the same winding number about `w`.
Piecewise-`C¹` regularity supplies the continuity, differentiability and integrability hypotheses
of `windingNumber_eq_of_dist_lt_dist`. -/
theorem _root_.TauCeti.IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist
    (h₀ : IsPiecewiseC1On γ₀ a b) (h₁ : IsPiecewiseC1On γ₁ a b) (h₀closed : γ₀ a = γ₀ b)
    (h₁closed : γ₁ a = γ₁ b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  exact h₀.absolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist
    h₁.absolutelyContinuousOnInterval h₀closed h₁closed hlt

/-- **Proximity invariance for paths with common endpoints.** If two piecewise-`C¹` paths agree at
both endpoints and stay closer to each other than the first stays to `w`, then they have the same
winding number about `w`. Unlike `IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist`, the paths need
not be closed; their common endpoints make the comparison quotient a closed curve. -/
theorem _root_.TauCeti.IsPiecewiseC1On.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints
    (h₀ : IsPiecewiseC1On γ₀ a b) (h₁ : IsPiecewiseC1On γ₁ a b)
    (ha : γ₀ a = γ₁ a) (hb : γ₀ b = γ₁ b)
    (hlt : ∀ t ∈ uIcc a b, dist (γ₁ t) (γ₀ t) < dist (γ₀ t) w) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w := by
  exact h₀.absolutelyContinuousOnInterval.windingNumber_eq_of_dist_lt_dist_of_eq_endpoints
    h₁.absolutelyContinuousOnInterval ha hb hlt

/-- **Invariance of the winding number along a straight-line homotopy.** If for every parameter `t`
the segment from `γ₀ t` to `γ₁ t` misses `w`, then the two closed piecewise-`C¹` curves have the
same winding number about `w`. -/
theorem _root_.TauCeti.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment
    (h₀ : IsPiecewiseC1On γ₀ a b) (h₁ : IsPiecewiseC1On γ₁ a b) (h₀closed : γ₀ a = γ₀ b)
    (h₁closed : γ₁ a = γ₁ b)
    (hseg : ∀ t ∈ uIcc a b, w ∉ segment ℝ (γ₀ t) (γ₁ t)) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w :=
  h₀.absolutelyContinuousOnInterval.windingNumber_eq_of_notMem_segment
    h₁.absolutelyContinuousOnInterval h₀closed h₁closed hseg

/-- **Invariance along a straight-line homotopy for piecewise-`C¹` paths with common endpoints.** -/
theorem _root_.TauCeti.IsPiecewiseC1On.windingNumber_eq_of_notMem_segment_of_eq_endpoints
    (h₀ : IsPiecewiseC1On γ₀ a b) (h₁ : IsPiecewiseC1On γ₁ a b)
    (ha : γ₀ a = γ₁ a) (hb : γ₀ b = γ₁ b)
    (hseg : ∀ t ∈ uIcc a b, w ∉ segment ℝ (γ₀ t) (γ₁ t)) :
    windingNumber γ₁ a b w = windingNumber γ₀ a b w :=
  h₀.absolutelyContinuousOnInterval.windingNumber_eq_of_notMem_segment_of_eq_endpoints
    h₁.absolutelyContinuousOnInterval ha hb hseg

end TauCeti.Contour

end

end
