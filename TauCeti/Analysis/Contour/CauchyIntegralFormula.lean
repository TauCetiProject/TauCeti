/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.DixonDef

/-!
# Cauchy's integral formula and the pointwise homology Cauchy theorem

Once Dixon's glued function vanishes at a point — `dixonFunction f U γ a b w = 0`, the output of the
Liouville step `dixonFunction_eq_zero` — two classical consequences follow by pure algebra, needing
no curve regularity beyond continuity of `γ` and interval-integrability of the two integrands:

* **Cauchy's integral formula**
  (`dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero`): on `U` the vanishing collapses the
  `h₁`/`h₂` identity to `dixonH2 f γ a b w = 2πi · n(γ, w) · f w`, so the Cauchy-type integral
  recovers `2πi` times the generalized winding number weighted by `f w`.
* **The pointwise homology Cauchy theorem**
  (`intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero`): applied to the twist
  `g z = (z - w₀) · f z`, which has `g w₀ = 0`, the right side vanishes; and as
  `g (γ t) / (γ t - w₀) = f (γ t)` off the curve, the Cauchy-type integral of `g` is the contour
  integral of `f`, giving `∫ t in a..b, deriv γ t • f (γ t) = 0`.

Both take the pointwise vanishing `dixonFunction … = 0` as a hypothesis. Discharging it through
`dixonFunction_eq_zero` for a null-homologous closed curve yields the roadmap target
`homologyCauchyTheorem` (`TauCetiRoadmap/ContourIntegration/Suggested.lean`, Layer 3).

## Main results

* `TauCeti.Contour.dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero`
* `TauCeti.Contour.intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero`

## Provenance

Adapted from `cauchyIntegralFormula_nullHomologous_at` and
`contourIntegral_eq_zero_of_nullHomologous_at` in `DixonTheorem.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval. See J. D.
Dixon, *A brief proof of Cauchy's integral theorem*, Proc. Amer. Math. Soc. 29 (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

/-- **Cauchy's integral formula from pointwise Dixon-vanishing.** If Dixon's glued function vanishes
at `w ∈ U` (`dixonFunction f U γ a b w = 0`), then for `γ` continuous on `uIcc a b` and avoiding `w`
with the Cauchy-type and index integrands interval-integrable, the Cauchy-type integral evaluates to
`dixonH2 f γ a b w = 2πi · n(γ, w) · f w`: on `U` the vanishing collapses the `h₁`/`h₂` identity,
whose winding term is exactly this value. Discharging the vanishing hypothesis via
`dixonFunction_eq_zero` gives Cauchy's integral formula for a null-homologous curve. -/
theorem dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ}
    {a b : ℝ} {w : ℂ} (h_cont : ContinuousOn γ (uIcc a b)) (hw : w ∈ U)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (h_zero_at : dixonFunction f U γ a b w = 0)
    (h_cauchy_int : IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b)
    (h_base_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    dixonH2 f γ a b w = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b w * f w := by
  rw [dixonFunction_eq_dixonH1 hw] at h_zero_at
  have h_identity := dixonH1_eq_dixonH2_sub_windingNumber_mul_f h_cont hoff h_cauchy_int h_base_int
  rw [h_zero_at] at h_identity
  exact sub_eq_zero.mp h_identity.symm

/-- **The pointwise homology Cauchy theorem** `∮_γ f = 0`. Applying the Cauchy integral formula to
the twist `g z = (z - w₀) · f z`, which satisfies `g w₀ = 0`, forces `dixonH2 g γ a b w₀ = 0`; and
since `g (γ t) / (γ t - w₀) = f (γ t)` for `γ` off `w₀`, that Cauchy-type integral is the contour
integral of `f`. Hence `∫ t in a..b, deriv γ t • f (γ t) = 0`, given the pointwise vanishing
`dixonFunction (fun z ↦ (z - w₀) * f z) U γ a b w₀ = 0`, interval-integrability of the contour
integrand `deriv γ • f ∘ γ`, and of the index integrand. Discharging the vanishing via
`dixonFunction_eq_zero` yields the roadmap `homologyCauchyTheorem`. -/
theorem intervalIntegral_deriv_smul_eq_zero_of_dixonFunction_eq_zero {f : ℂ → ℂ} {U : Set ℂ}
    {γ : ℝ → ℂ} {a b : ℝ} (h_cont : ContinuousOn γ (uIcc a b)) (w₀ : ℂ) (hw₀_in_U : w₀ ∈ U)
    (hw₀_off : ∀ t ∈ uIcc a b, γ t ≠ w₀)
    (h_zero_at : dixonFunction (fun z ↦ (z - w₀) * f z) U γ a b w₀ = 0)
    (h_int : IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b)
    (h_base_int : IntervalIntegrable (fun t ↦ (γ t - w₀)⁻¹ * deriv γ t) volume a b) :
    ∫ t in a..b, deriv γ t • f (γ t) = 0 := by
  have key : ∀ t ∈ uIcc a b,
      (γ t - w₀) * f (γ t) / (γ t - w₀) * deriv γ t = deriv γ t • f (γ t) := fun t ht ↦ by
    rw [mul_div_cancel_left₀ _ (sub_ne_zero.mpr (hw₀_off t ht)), smul_eq_mul, mul_comm]
  have h_cif := dixonH2_eq_windingNumber_mul_f_of_dixonFunction_eq_zero
    (f := fun z ↦ (z - w₀) * f z) h_cont hw₀_in_U hw₀_off h_zero_at
    (h_int.congr fun t ht ↦ (key t (uIoc_subset_uIcc ht)).symm) h_base_int
  simp only [sub_self, zero_mul, mul_zero] at h_cif
  rw [dixonH2_def] at h_cif
  rw [← h_cif]
  exact intervalIntegral.integral_congr fun t ht ↦ (key t ht).symm

end TauCeti.Contour
