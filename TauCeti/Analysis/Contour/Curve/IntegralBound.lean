/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A decay bound for `∫ (γ - w)⁻¹ • g` when `w` is far from the curve

For a curve `γ : ℝ → 𝕜` in a normed division ring with `‖γ t‖ ≤ R` on the integrating interval
and a point `w` with `R < ‖w‖`, the integral `∫ t in a..b, (γ t - w)⁻¹ • g t ∂μ` of an
interval-integrable weight `g : ℝ → E` (valued in a normed `𝕜`-module) is bounded by
`(∫ ‖g‖ ∂μ) / (‖w‖ - R)`: the distance lower bound `‖w‖ - R ≤ ‖γ t - w‖` gives
`‖(γ t - w)⁻¹‖ ≤ (‖w‖ - R)⁻¹` pointwise, so the estimate reduces to the `L¹` norm of `g`. For
`𝕜 = E = ℂ` and Lebesgue measure this is the common decay estimate behind the vanishing at infinity
of both the generalized winding number (weight `g = deriv γ`) and Dixon's `dixonH2` (weight
`g = f (γ ·) * deriv γ`); using the `L¹` norm rather than a uniform bound on `g` keeps it applicable
to raw curves whose derivative is only interval-integrable.

## Main results

* `TauCeti.Contour.norm_integral_inv_sub_smul_le` — the `(∫ ‖g‖ ∂μ) / (‖w‖ - R)` decay bound.

## Provenance

Factored from the far-field estimates in the AINTLIB `LeanModularForms` development —
`contourIntegral_inv_norm_le_of_far` in `NullHomologous.lean` (the winding case, weight `deriv γ`)
and `dixonH2_norm_le` in `DixonTheorem.lean` (the Dixon case) — restated for a raw curve on an
oriented interval with an arbitrary interval-integrable weight `g`, and bounding by the `L¹` norm of
`g` rather than a Lipschitz or uniform bound.
-/

public section

open MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- **Decay bound for a Cauchy-type integral far from the curve.** If `‖γ t‖ ≤ R` on `Ι a b`,
`g` is interval-integrable with respect to `μ`, and `R < ‖w‖`, then
`‖∫ t in a..b, (γ t - w)⁻¹ • g t ∂μ‖ ≤ (∫ t in Ι a b, ‖g t‖ ∂μ) / (‖w‖ - R)`. The bound on `γ` is
required only on the half-open interval `Ι a b`. -/
theorem norm_integral_inv_sub_smul_le {γ : ℝ → 𝕜} {g : ℝ → E} {μ : Measure ℝ} {a b R : ℝ} {w : 𝕜}
    (hg : IntervalIntegrable g μ a b) (hR : ∀ t ∈ Ι a b, ‖γ t‖ ≤ R) (hw : R < ‖w‖) :
    ‖∫ t in a..b, (γ t - w)⁻¹ • g t ∂μ‖ ≤ (∫ t in Ι a b, ‖g t‖ ∂μ) / (‖w‖ - R) := by
  rw [intervalIntegral.norm_integral_eq_norm_integral_uIoc, ← integral_div]
  refine norm_integral_le_of_norm_le (hg.norm.div_const _).def' <|
    ae_restrict_of_forall_mem measurableSet_uIoc fun t ht ↦ ?_
  rw [norm_smul, norm_inv, inv_mul_eq_div]
  gcongr
  linarith [hR t ht, norm_sub_norm_le w (γ t), norm_sub_rev w (γ t)]

end TauCeti.Contour
