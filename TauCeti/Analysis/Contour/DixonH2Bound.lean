/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.DixonDef
import TauCeti.Analysis.Contour.CurveIntegralBound

/-!
# Norm bound and decay at infinity of Dixon's `dixonH2`

For `w` outside a ball containing the curve, Dixon's Cauchy-type integral
`dixonH2 f γ a b w = ∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t` is small: rewriting the integrand
as `(γ t - w)⁻¹ * (f (γ t) * deriv γ t)`, the distance lower bound `‖w‖ - R ≤ ‖γ t - w‖` gives
`‖dixonH2 f γ a b w‖ ≤ (∫ ‖f (γ ·) * deriv γ‖) / (‖w‖ - R)`, which tends to `0` as `‖w‖ → ∞`.
Bounding by the `L¹` norm of the weight `f (γ ·) * deriv γ` rather than a uniform bound keeps the
estimate applicable to raw curves whose derivative is only interval-integrable.

## Main results

* `TauCeti.Contour.dixonH2_norm_le` — the decay bound `‖dixonH2 f γ a b w‖ ≤
  (∫ ‖f (γ ·) * deriv γ‖) / (‖w‖ - R)` for `R < ‖w‖`.
* `TauCeti.Contour.dixonH2_tendsto_zero` — `dixonH2 f γ a b` tends to `0` along `cocompact ℂ`.

The decay of `dixonH2` (hence of Dixon's glued function, which agrees with it far out) is the input
to the Liouville step of Dixon's proof of the homology form of Cauchy's theorem
(`homologyCauchyTheorem`, `TauCetiRoadmap/ContourIntegration/Suggested.lean`). It shares the
underlying Cauchy-integral decay estimate `norm_integral_inv_sub_mul_le` with the vanishing at
infinity of the generalized winding number.

## Provenance

Adapted from `dixonH2_norm_le` and `dixonH2_tendsto_zero` in `DixonTheorem.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval. The original
uses a uniform bound on the integrand (valid for its `C¹`, `[0, 1]`-parametrised curve); the
raw-`γ` port bounds by the `L¹` norm `∫ ‖f (γ ·) * deriv γ‖`, shedding the boundedness hypothesis.
-/

public section

open Complex MeasureTheory Set Filter

open scoped Real Interval Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}

/-- **Norm bound for `dixonH2`.** When `‖w‖ > R`, `R` bounds `‖γ‖` on `uIcc a b`, and the weight
`f (γ ·) * deriv γ` is interval-integrable, the Cauchy-type integral is bounded by its `L¹` norm
divided by `‖w‖ - R`: rewrite the integrand as `(γ t - w)⁻¹ * (f (γ t) * deriv γ t)` and apply the
shared decay estimate `norm_integral_inv_sub_mul_le`. -/
theorem dixonH2_norm_le {R : ℝ} (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R)
    (hg : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b) {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ a b w‖ ≤ (∫ t in Ι a b, ‖f (γ t) * deriv γ t‖) / (‖w‖ - R) := by
  have hcongr : (∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t)
      = ∫ t in a..b, (γ t - w)⁻¹ * (f (γ t) * deriv γ t) :=
    intervalIntegral.integral_congr fun t _ ↦ by ring
  rw [dixonH2_def, hcongr]
  exact norm_integral_inv_sub_mul_le hg hR hw

/-- **`dixonH2 f γ a b` tends to `0` along `cocompact ℂ`.** For `‖w‖` large the norm bound
`(∫ ‖f (γ ·) * deriv γ‖) / (‖w‖ - R)` is below any `ε > 0`. -/
theorem dixonH2_tendsto_zero {R : ℝ} (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R)
    (hg : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b) :
    Tendsto (dixonH2 f γ a b) (cocompact ℂ) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  simp only [dist_zero_right]
  set D := ∫ t in Ι a b, ‖f (γ t) * deriv γ t‖
  filter_upwards [(isCompact_closedBall (0 : ℂ)
      (max R (R + D / ε))).compl_mem_cocompact] with w hw
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
  have hRw : R < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
  have hpos : 0 < ‖w‖ - R := by linarith
  calc ‖dixonH2 f γ a b w‖
      ≤ D / (‖w‖ - R) := dixonH2_norm_le hR hg hRw
    _ < ε := by
        rw [div_lt_iff₀ hpos]
        have h2 : D / ε < ‖w‖ - R := by
          linarith [lt_of_le_of_lt (le_max_right _ _) hw]
        rw [div_lt_iff₀ hε] at h2
        linarith [mul_comm ε (‖w‖ - R)]

end TauCeti.Contour
