/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.DixonDef

/-!
# Norm bound and decay at infinity of Dixon's `dixonH2`

For `w` outside a ball containing the curve, Dixon's Cauchy-type integral
`dixonH2 f γ a b w = ∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t` is small: its integrand is
bounded by `M / (‖w‖ - R)`, where `M` bounds the numerator product `‖f (γ ·) * deriv γ‖`, so the
integral is bounded by `M · |b - a| / (‖w‖ - R)`, which tends to `0` as `‖w‖ → ∞`.

## Main results

* `TauCeti.Contour.dixonH2_norm_le` — the quantitative bound `‖dixonH2 f γ a b w‖ ≤
  M / (‖w‖ - R) · |b - a|` for `R < ‖w‖`.
* `TauCeti.Contour.dixonH2_tendsto_zero` — `dixonH2 f γ a b` tends to `0` along `cocompact ℂ`.

The decay of `dixonH2` (hence of Dixon's glued function, which agrees with it far out) is the input
to the Liouville step of Dixon's proof of the homology form of Cauchy's theorem
(`homologyCauchyTheorem`, `TauCetiRoadmap/ContourIntegration/Suggested.lean`).

## Provenance

Adapted from `dixonH2_norm_le` and `dixonH2_tendsto_zero` in `DixonTheorem.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval. The
`|b - a|` factor is the length of that interval (invisible in the `[0, 1]`-parametrised original).
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

/-- **`dixonH2 f γ a b` tends to `0` along `cocompact ℂ`.** For `‖w‖` large the norm bound
`M · |b - a| / (‖w‖ - R)` is below any `ε > 0`. -/
theorem dixonH2_tendsto_zero {R M : ℝ}
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hM : ∀ t ∈ uIcc a b, ‖f (γ t) * deriv γ t‖ ≤ M) :
    Tendsto (dixonH2 f γ a b) (cocompact ℂ) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  simp only [dist_zero_right]
  filter_upwards [(isCompact_closedBall (0 : ℂ)
      (max R (R + M * |b - a| / ε))).compl_mem_cocompact] with w hw
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hw
  have hRw : R < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
  have hpos : 0 < ‖w‖ - R := by linarith
  calc ‖dixonH2 f γ a b w‖
      ≤ M / (‖w‖ - R) * |b - a| := dixonH2_norm_le hR hM hRw
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
        have h2 : M * |b - a| / ε < ‖w‖ - R := by
          linarith [lt_of_le_of_lt (le_max_right _ _) hw]
        rw [div_lt_iff₀ hε] at h2
        linarith [mul_comm ε (‖w‖ - R)]

end TauCeti.Contour
