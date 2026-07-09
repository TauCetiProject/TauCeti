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
bounded by `M_f · M_d / (‖w‖ - R)`, so the integral is bounded by `M_f · M_d · |b - a| / (‖w‖ - R)`,
which tends to `0` as `‖w‖ → ∞`.

## Main results

* `TauCeti.Contour.dixonH2_norm_le` — the quantitative bound `‖dixonH2 f γ a b w‖ ≤
  M_f · M_d / (‖w‖ - R) · |b - a|` for `R < ‖w‖`.
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

/-- The exterior `{w | R < ‖w‖}` of a closed ball is a cocompact neighbourhood of infinity. -/
private lemma setOf_norm_gt_mem_cocompact (R : ℝ) : {w : ℂ | R < ‖w‖} ∈ cocompact ℂ :=
  mem_cocompact.mpr
    ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, fun _ hw ↦ by simpa using hw⟩

/-- **Norm bound for `dixonH2`.** When `‖w‖ > R` and `R` bounds `‖γ‖`, `M_f` bounds `‖f ∘ γ‖`, and
`M_d` bounds `‖deriv γ‖` on `uIcc a b`, the Cauchy-type integral is bounded by
`M_f · M_d / (‖w‖ - R) · |b - a|`. -/
theorem dixonH2_norm_le {R M_f M_d : ℝ}
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hM_f : ∀ t ∈ uIcc a b, ‖f (γ t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ uIcc a b, ‖deriv γ t‖ ≤ M_d) {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ a b w‖ ≤ M_f * M_d / (‖w‖ - R) * |b - a| := by
  rw [dixonH2_def]
  have hM_f_nn : 0 ≤ M_f := (norm_nonneg (f (γ a))).trans (hM_f a Set.left_mem_uIcc)
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_ptwise : ∀ t ∈ Set.uIoc a b,
      ‖f (γ t) / (γ t - w) * deriv γ t‖ ≤ M_f * M_d / (‖w‖ - R) := by
    intro t ht_ui
    have ht : t ∈ uIcc a b := Set.uIoc_subset_uIcc ht_ui
    rw [norm_mul, norm_div]
    have h_dist_lb : ‖w‖ - R ≤ ‖γ t - w‖ := by
      linarith [norm_sub_norm_le w (γ t), norm_sub_rev w (γ t), hR t ht]
    calc ‖f (γ t)‖ / ‖γ t - w‖ * ‖deriv γ t‖
        ≤ M_f / (‖w‖ - R) * M_d := by gcongr; exacts [hM_f t ht, hM_d t ht]
      _ = M_f * M_d / (‖w‖ - R) := by ring
  exact intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise

/-- **`dixonH2 f γ a b` tends to `0` along `cocompact ℂ`.** For `‖w‖` large the norm bound
`M_f · M_d · |b - a| / (‖w‖ - R)` is below any `ε > 0`. -/
theorem dixonH2_tendsto_zero {R M_f M_d : ℝ}
    (hR : ∀ t ∈ uIcc a b, ‖γ t‖ ≤ R) (hM_f : ∀ t ∈ uIcc a b, ‖f (γ t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ uIcc a b, ‖deriv γ t‖ ≤ M_d) :
    Tendsto (dixonH2 f γ a b) (cocompact ℂ) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  simp only [dist_zero_right]
  filter_upwards [setOf_norm_gt_mem_cocompact (max R (R + M_f * M_d * |b - a| / ε))] with
    w (hw : max R (R + M_f * M_d * |b - a| / ε) < ‖w‖)
  have hRw : R < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) hw
  have hpos : 0 < ‖w‖ - R := by linarith
  calc ‖dixonH2 f γ a b w‖
      ≤ M_f * M_d / (‖w‖ - R) * |b - a| := dixonH2_norm_le hR hM_f hM_d hRw
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
        have h2 : M_f * M_d * |b - a| / ε < ‖w‖ - R := by
          linarith [lt_of_le_of_lt (le_max_right _ _) hw]
        rw [div_lt_iff₀ hε] at h2
        linarith [mul_comm ε (‖w‖ - R)]

end TauCeti.Contour
