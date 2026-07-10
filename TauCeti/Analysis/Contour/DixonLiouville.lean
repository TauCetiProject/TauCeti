/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.DixonDef
import TauCeti.Analysis.Contour.DixonFunctionDiff
import TauCeti.Analysis.Contour.DixonH2Bound
import TauCeti.Analysis.Contour.WindingVanishing
import Mathlib.Analysis.Complex.Liouville

/-!
# The Dixon function vanishes (Liouville step)

Dixon's glued function `dixonFunction f U γ a b` is entire (`differentiable_dixonFunction`) and,
for a closed null-homologous curve, tends to `0` at infinity, so Liouville's theorem forces it to
vanish identically. The decay comes from the eventual agreement `dixonFunction = dixonH2` far from
the origin — off `U` by definition, and on `U` because the winding number is eventually `0`, which
collapses the `h₁`/`h₂` identity — combined with the `L¹` decay of `dixonH2`.

## Main results

* `TauCeti.Contour.dixonFunction_eq_zero` — `dixonFunction f U γ a b w = 0` for every `w`, for a
  closed null-homologous curve in `U` with `f` differentiable on the open set `U`.

This pointwise vanishing is the hinge of Dixon's proof of the homology form of Cauchy's theorem
(`homologyCauchyTheorem`, `TauCetiRoadmap/ContourIntegration/Suggested.lean`): applying it to
`(· - w₀) * f` yields the Cauchy integral formula and thence `∮_γ f = 0`.

## Provenance

Adapted from `dixonFunction_eventually_eq_dixonH2`, `dixonFunction_tendsto_zero` and
`dixonFunction_eq_zero` in `DixonTheorem.lean` of the AINTLIB `LeanModularForms` development,
restated for a raw `γ : ℝ → ℂ` on an oriented interval. See J. D. Dixon, *A brief proof of Cauchy's
integral theorem* (1971).
-/

public section

open Complex MeasureTheory Set Filter

open scoped Real Interval Topology

namespace TauCeti.Contour

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ}

/-- **The Dixon function eventually agrees with `dixonH2` along `cocompact ℂ`.** For a closed curve
`γ` continuous on `uIcc a b`, differentiable off a countable set, with interval-integrable
derivative and image in `U`, every `w` far from the origin lies off the curve with winding number
`0` (`windingNumber_eventually_zero_cocompact`). There `dixonFunction = dixonH2`: off `U` by
definition, and on `U` because the vanishing winding number collapses the `h₁`/`h₂` identity. -/
private theorem dixonFunction_eventually_eq_dixonH2 (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t) :
    ∀ᶠ w in cocompact ℂ, dixonFunction f U γ a b w = dixonH2 f γ a b w := by
  filter_upwards [windingNumber_eventually_zero_cocompact hclosed hP hγ_cont hγ_diff hderiv_int]
    with w ⟨hoff, hwn⟩
  exact dixonFunction_eq_dixonH2_of_windingNumber_zero hf hγ_cont hγU hderiv_int hoff hwn

/-- **The Dixon function tends to `0` along `cocompact ℂ`.** It eventually agrees with `dixonH2`,
which tends to `0` by the `L¹` decay bound: the image of the compact interval `uIcc a b` is bounded
(`IsCompact.exists_bound_of_continuousOn`), and the weight `f (γ ·) * deriv γ` is
interval-integrable (continuous `f ∘ γ` times the interval-integrable derivative). -/
private theorem dixonFunction_tendsto_zero (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t) :
    Tendsto (dixonFunction f U γ a b) (cocompact ℂ) (nhds 0) := by
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn hγ_cont
  have hg : IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b :=
    hderiv_int.continuousOn_mul (hf.continuousOn.comp hγ_cont hγU)
  exact (dixonH2_tendsto_zero_of_integrable (fun t ht ↦ hR t (uIoc_subset_uIcc ht)) hg).congr'
    (Filter.EventuallyEq.symm
      (dixonFunction_eventually_eq_dixonH2 hf hγ_cont hγU hderiv_int hclosed hP hγ_diff))

/-- **The Dixon function is identically zero (Liouville).** For a closed curve `γ`, null-homologous
in an open set `U` (continuous on `uIcc a b`, differentiable off a countable set, with
interval-integrable derivative and image in `U`) and `f` differentiable on `U`, the entire function
`dixonFunction f U γ a b` tends to `0` at infinity, so Liouville's theorem forces it to vanish at
every point. -/
theorem dixonFunction_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) (w : ℂ) : dixonFunction f U γ a b w = 0 := by
  have h_entire :=
    differentiable_dixonFunction hU hf hγ_cont hγU hderiv_int hclosed hP hγ_diff h_null
  exact Differentiable.apply_eq_of_tendsto_cocompact h_entire w
    (dixonFunction_tendsto_zero hf hγ_cont hγU hderiv_int hclosed hP hγ_diff)

end TauCeti.Contour
