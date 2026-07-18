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
`dixonH2 f γ a b w = ∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t` is small and tends to `0` as
`‖w‖ → ∞`. The distance lower bound `‖w‖ - R ≤ ‖γ t - w‖` (for `‖γ‖ ≤ R < ‖w‖`) controls the Cauchy
kernel; the numerator `f (γ ·) * deriv γ` is then bounded either uniformly or in `L¹`:

* with a uniform bound `M` on the integrand, `‖dixonH2 f γ a b w‖ ≤ M / (‖w‖ - R) · |b - a|`;
* using only interval-integrability of the weight (rewrite the integrand as
  `(γ t - w)⁻¹ * (f (γ t) * deriv γ t)`),
  `‖dixonH2 f γ a b w‖ ≤ (∫ ‖f (γ ·) * deriv γ‖) / (‖w‖ - R)`.

The two hypotheses are incomparable — the uniform bound needs no integrability, the `L¹` bound needs
no uniform bound — so both are kept. The `L¹` form is what applies to raw curves whose derivative is
only interval-integrable.

## Main results

* `TauCeti.Contour.dixonH2_norm_le` / `dixonH2_tendsto_zero` — the uniform-bound norm estimate and
  its decay at infinity.
* `TauCeti.Contour.dixonH2_norm_le_of_integrable` / `dixonH2_tendsto_zero_of_integrable` — the `L¹`
  versions, via the shared estimate `norm_integral_inv_sub_mul_le`.

The decay of `dixonH2` (hence of Dixon's glued function, which agrees with it far out) is the input
to the Liouville step of Dixon's proof of the homology form of Cauchy's theorem
(`homologyCauchyTheorem`, `TauCetiRoadmap/ContourIntegration/Suggested.lean`).

## Provenance

Adapted from `dixonH2_norm_le` and `dixonH2_tendsto_zero` in `DixonTheorem.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval (the
`|b - a|` factor is the interval length, invisible in the `[0, 1]`-parametrised original). The `L¹`
variants additionally shed the boundedness hypothesis, bounding by `∫ ‖f (γ ·) * deriv γ‖` instead.
-/

public section

open Complex MeasureTheory Set Filter

open scoped Real Interval Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}

/-- **Norm bound for `dixonH2`.** When `‖w‖ > R`, `R` bounds `‖γ‖`, and `M` bounds the numerator
product `‖f (γ ·) * deriv γ‖` on `uIcc a b`, the Cauchy-type integral is bounded by
`M / (‖w‖ - R) · |b - a|`. -/
theorem dixonH2_norm_le {R M : ℝ}
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hM : ∀ t ∈ uIcc a b, ‖f (γ t) * deriv γ t‖ ≤ M)
    {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ a b w‖ ≤ M / (‖w‖ - R) * |b - a| := by
  rw [dixonH2_def]
  have hM_nn : 0 ≤ M := (norm_nonneg _).trans (hM a Set.left_mem_uIcc)
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_ptwise : ∀ t ∈ Set.uIoc a b,
      ‖f (γ t) / (γ t - w) * deriv γ t‖ ≤ M / (‖w‖ - R) := by
    intro t ht_ui
    have ht : t ∈ uIcc a b := Set.uIoc_subset_uIcc ht_ui
    have h_dist_lb : ‖w‖ - R ≤ ‖γ t - w‖ := by
      linarith [norm_sub_norm_le w (γ t), norm_sub_rev w (γ t), hR t ht]
    rw [show f (γ t) / (γ t - w) * deriv γ t = f (γ t) * deriv γ t / (γ t - w) by ring, norm_div]
    gcongr
    exact hM t ht
  exact intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise

/-- **A `C / (‖w‖ - R)` bound forces decay along `cocompact`.** If `‖F w‖ ≤ C / (‖w‖ - R)` for every
`w` with `R < ‖w‖`, then `F` tends to `0` along `cocompact ℂ`: outside a large closed ball the bound
drops below any `ε > 0`. Shared scaffolding for the uniform and `L¹` decay lemmas below. -/
private theorem tendsto_zero_cocompact_of_norm_le_div {F : ℂ → ℂ} {R C : ℝ}
    (hbound : ∀ w : ℂ, R < ‖w‖ → ‖F w‖ ≤ C / (‖w‖ - R)) :
    Tendsto F (cocompact ℂ) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  simp only [dist_zero_right]
  filter_upwards [(isCompact_closedBall (0 : ℂ)
      (max R (R + C / ε))).compl_mem_cocompact] with w hw
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
  have hRw : R < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
  have hpos : 0 < ‖w‖ - R := by linarith
  calc ‖F w‖ ≤ C / (‖w‖ - R) := hbound w hRw
    _ < ε := by
        rw [div_lt_iff₀ hpos]
        have h2 : C / ε < ‖w‖ - R := by
          linarith [lt_of_le_of_lt (le_max_right _ _) hw]
        rw [div_lt_iff₀ hε] at h2
        linarith [mul_comm ε (‖w‖ - R)]

/-- **`dixonH2 f γ a b` tends to `0` along `cocompact ℂ`.** The norm bound `dixonH2_norm_le` has the
form `C / (‖w‖ - R)` with `C = M * |b - a|`, so `tendsto_zero_cocompact_of_norm_le_div` applies. -/
theorem dixonH2_tendsto_zero {R M : ℝ}
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hM : ∀ t ∈ uIcc a b, ‖f (γ t) * deriv γ t‖ ≤ M) :
    Tendsto (dixonH2 f γ a b) (cocompact ℂ) (nhds 0) := by
  refine tendsto_zero_cocompact_of_norm_le_div (R := R) (C := M * |b - a|) fun w hw ↦ ?_
  rw [← div_mul_eq_mul_div]
  exact dixonH2_norm_le hR hM hw

/-- **`L¹` norm bound for `dixonH2`.** When `‖w‖ > R`, `R` bounds `‖γ‖` on `Ι a b`, and the weight
`f (γ ·) * deriv γ` is interval-integrable, `dixonH2` is bounded by that weight's `L¹` norm divided
by `‖w‖ - R`. Unlike `dixonH2_norm_le` this needs no uniform bound on the integrand, so it applies
to raw curves whose derivative is only interval-integrable: rewrite the integrand as
`(γ t - w)⁻¹ * (f (γ t) * deriv γ t)` and apply `norm_integral_inv_sub_mul_le`. Only the bound on
the half-open interval `Ι a b` is needed. -/
theorem dixonH2_norm_le_of_integrable {R : ℝ} (hR : ∀ t ∈ Ι a b, ‖γ t‖ ≤ R)
    (hg : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b) {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ a b w‖ ≤ (∫ t in Ι a b, ‖f (γ t) * deriv γ t‖) / (‖w‖ - R) := by
  have hcongr : (∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t)
      = ∫ t in a..b, (γ t - w)⁻¹ * (f (γ t) * deriv γ t) :=
    intervalIntegral.integral_congr fun t _ ↦ by ring
  rw [dixonH2_def, hcongr]
  exact norm_integral_inv_sub_mul_le hg hR hw

/-- **`dixonH2 f γ a b` tends to `0` along `cocompact ℂ` (`L¹` form).** The `L¹` norm bound
`dixonH2_norm_le_of_integrable` is already of the form `C / (‖w‖ - R)`, so
`tendsto_zero_cocompact_of_norm_le_div` applies; the interval-integrable weight replaces the uniform
bound of `dixonH2_tendsto_zero`. -/
theorem dixonH2_tendsto_zero_of_integrable {R : ℝ} (hR : ∀ t ∈ Ι a b, ‖γ t‖ ≤ R)
    (hg : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b) :
    Tendsto (dixonH2 f γ a b) (cocompact ℂ) (nhds 0) :=
  tendsto_zero_cocompact_of_norm_le_div fun _ hw ↦ dixonH2_norm_le_of_integrable hR hg hw

end TauCeti.Contour
