/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.Dixon.Def
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Dixon.FunctionDiff
import TauCeti.Analysis.Contour.Dixon.H2.Bound
import TauCeti.Analysis.Contour.Winding.Vanishing
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Complex.Liouville

/-!
# The Dixon function vanishes (Liouville step)

For `f` holomorphic on an open set `U` and a closed absolutely continuous curve `γ` in `U` that is
null-homologous there, Dixon's glued function `dixonFunction f U γ a b` is entire
(`differentiable_dixonFunction`) and tends to `0` at infinity, so Liouville's theorem forces it to
vanish identically. The decay comes from the eventual agreement `dixonFunction = dixonH2` far from
the origin — off `U` by definition, and on `U` because the winding number is eventually `0`, which
collapses the `h₁`/`h₂` identity — combined with the decay of `dixonH2` at infinity.

## Main results

* `TauCeti.Contour.dixonFunction_eq_zero` — `dixonFunction f U γ a b w = 0` for every `w`, for a
  closed null-homologous absolutely continuous curve in `U` with `f` differentiable on the open
  set `U`.

This pointwise vanishing is the hinge of Dixon's proof of the homology form of Cauchy's theorem
for null-homologous curves: applied to `f` it yields Cauchy's integral formula, and applied to
`(· - w₀) * f` it yields `∮_γ f = 0`.

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

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ}

/-- **The Dixon function eventually agrees with `dixonH2` along `cocompact ℂ`.** For a closed
absolutely continuous curve `γ` with image in `U`, every `w` far from the origin lies off the curve
with winding number `0`
(`AbsolutelyContinuousOnInterval.windingNumber_eventually_zero_cocompact`). There
`dixonFunction = dixonH2`: off `U` by definition, and on `U` because the vanishing winding number
collapses the `h₁`/`h₂` identity. -/
private theorem dixonFunction_eventually_eq_dixonH2 (hf : ContinuousOn f U)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hclosed : γ a = γ b) :
    dixonFunction f U γ a b =ᶠ[cocompact ℂ] dixonH2 f γ a b := by
  have hderiv_int := hγ.intervalIntegrable_deriv_of_finiteDimensional
  filter_upwards [hγ.windingNumber_eventually_zero_cocompact hclosed] with w ⟨hw, hwn⟩
  have hoff : ∀ t ∈ uIcc a b, γ t ≠ w := fun t ht heq ↦ hw ⟨t, ht, heq⟩
  exact dixonFunction_eq_dixonH2_of_windingNumber_zero hγ.continuousOn hderiv_int
    (cauchy_integrand_intervalIntegrable hf hγ.continuousOn hγU hderiv_int hoff) hoff hwn

/-- **The Dixon function tends to `0` along `cocompact ℂ`.** It eventually agrees with `dixonH2`,
which tends to `0` for every curve continuous on `uIcc a b`
(`dixonH2_tendsto_zero_of_continuousOn`). -/
private theorem dixonFunction_tendsto_zero (hf : ContinuousOn f U)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hclosed : γ a = γ b) :
    Tendsto (dixonFunction f U γ a b) (cocompact ℂ) (𝓝 0) :=
  (dixonH2_tendsto_zero_of_continuousOn hγ.continuousOn).congr'
    (dixonFunction_eventually_eq_dixonH2 hf hγ hγU hclosed).symm

/-- **The Dixon function is identically zero (Liouville).** For a closed absolutely continuous
curve `γ` with image in an open set `U`, null-homologous there, and `f` differentiable on `U`, the
entire function `dixonFunction f U γ a b` tends to `0` at infinity, so Liouville's theorem forces
it to vanish at every point. -/
theorem dixonFunction_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hclosed : γ a = γ b) (h_null : IsNullHomologous γ a b U) (w : ℂ) :
    dixonFunction f U γ a b w = 0 :=
  (differentiable_dixonFunction hU hf hγ hγU h_null).apply_eq_of_tendsto_cocompact w
    (dixonFunction_tendsto_zero hf.continuousOn hγ hγU hclosed)

end TauCeti.Contour
