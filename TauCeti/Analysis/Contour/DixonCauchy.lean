/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.DixonDef

/-!
# Dixon's Cauchy integral formula and the pointwise homology Cauchy theorem

From the vanishing of Dixon's `dixonH1` integral at a point, two classical consequences follow by
pure algebra:

* **Cauchy's integral formula**
  (`dixonH2_eq_windingNumber_mul_f_of_dixonH1_eq_zero`): if `dixonH1 f γ a b w = 0`, the `h₁`/`h₂`
  identity gives `dixonH2 f γ a b w = 2πi · n(γ, w) · f w`, so the Cauchy-type integral recovers
  `2πi` times the generalized winding number weighted by `f w`.
* **The pointwise homology Cauchy theorem**
  (`intervalIntegral_deriv_smul_eq_zero_of_dixonH1_eq_zero`): for the twist `g z = (z - w₀) · f z`,
  the difference quotient `dslope g w₀ (γ t)` equals `f (γ t)` off `w₀` (as `g w₀ = 0`), so the
  vanishing of `dixonH1 g γ a b w₀` is exactly `∫ t in a..b, deriv γ t • f (γ t) = 0`.

Both hypothesise only `dixonH1 … = 0`. For a null-homologous closed curve Dixon's Liouville step
`dixonFunction_eq_zero` gives `dixonFunction … = 0`, which `dixonFunction_eq_dixonH1` turns into
the `dixonH1` vanishing, yielding the roadmap target `homologyCauchyTheorem`
(`TauCetiRoadmap/ContourIntegration/Suggested.lean`, Layer 3).

## Main results

* `TauCeti.Contour.dixonH2_eq_windingNumber_mul_f_of_dixonH1_eq_zero`
* `TauCeti.Contour.intervalIntegral_deriv_smul_eq_zero_of_dixonH1_eq_zero`

## Provenance

Adapted from `cauchyIntegralFormula_nullHomologous_at` and
`contourIntegral_eq_zero_of_nullHomologous_at` in `DixonTheorem.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval and
generalised to hypothesise `dixonH1 … = 0` directly. See J. D. Dixon, *A brief proof of Cauchy's
integral theorem*, Proc. Amer. Math. Soc. 29 (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

/-- **Cauchy's integral formula from vanishing `dixonH1`.** If `dixonH1 f γ a b w = 0`, then for `γ`
continuous on `uIcc a b` and avoiding `w` with the Cauchy-type and index integrands
interval-integrable, the `h₁`/`h₂` identity collapses to
`dixonH2 f γ a b w = 2πi · n(γ, w) · f w`. For a null-homologous curve the vanishing is supplied by
`dixonFunction_eq_zero` through `dixonFunction_eq_dixonH1`, giving Cauchy's integral formula. -/
theorem dixonH2_eq_windingNumber_mul_f_of_dixonH1_eq_zero {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (h_cont : ContinuousOn γ (uIcc a b)) (hoff : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_zero_at : dixonH1 f γ a b w = 0)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b)
    (h_base_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    dixonH2 f γ a b w = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w := by
  have h_identity := dixonH1_eq_dixonH2_sub_windingNumber_mul_f h_cont hoff h_cauchy_int h_base_int
  rw [h_zero_at] at h_identity
  exact sub_eq_zero.mp h_identity.symm

/-- **The pointwise homology Cauchy theorem** `∮_γ f = 0`. For the twist `g z = (z - w₀) · f z`, the
difference quotient `dslope g w₀ (γ t)` equals `f (γ t)` off `w₀` (since `g w₀ = 0`), so
`dixonH1 g γ a b w₀ = ∫ t in a..b, deriv γ t • f (γ t)`. Its vanishing is therefore exactly
`∫ t in a..b, deriv γ t • f (γ t) = 0`; only that `γ` avoids `w₀` is needed. For a null-homologous
curve the vanishing is `dixonFunction_eq_zero` for `(· - w₀) * f`, via
`dixonFunction_eq_dixonH1`. -/
theorem intervalIntegral_deriv_smul_eq_zero_of_dixonH1_eq_zero {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    {w₀ : ℂ} (hw₀_off : ∀ t ∈ uIcc a b, γ t ≠ w₀)
    (h_zero_at : dixonH1 (fun z ↦ (z - w₀) * f z) γ a b w₀ = 0) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  rw [dixonH1_def] at h_zero_at
  rw [← h_zero_at]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  have hne : γ t - w₀ ≠ 0 := sub_ne_zero.mpr (hw₀_off t ht)
  have hg : dslope (fun z ↦ (z - w₀) * f z) w₀ (γ t) = f (γ t) := by
    rw [dslope_of_ne _ (hw₀_off t ht), slope_def_field]
    field_simp
    ring
  rw [hg, smul_eq_mul, mul_comm]

end TauCeti.Contour
