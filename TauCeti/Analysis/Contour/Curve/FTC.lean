/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import TauCeti.Analysis.Contour.Curve.Integrability

/-!
# The fundamental theorem of calculus along a piecewise-`C¹` curve

If `F` has derivative `f` at every point of a set `U ⊆ ℂ` on which `f` is continuous, then the
contour integral `∫ t in a..b, γ' t • f (γ t)` along a piecewise-`C¹` curve `γ` in `U` is the
endpoint difference `F (γ b) - F (γ a)`. A piecewise-`C¹` curve is differentiable off a countable
set of parameters, so this is Mathlib's fundamental theorem of calculus with a countable
exceptional set, `intervalIntegral.integral_eq_of_hasDerivAt_off_countable`, applied to `F ∘ γ`.
For curves differentiable at every interior point, see
`TauCeti.Contour.integral_deriv_smul_comp_eq_sub_of_hasDerivAt`.

## Main results

* `TauCeti.Contour.intervalIntegral_deriv_smul_eq_sub_of_hasDerivAt`: the fundamental theorem of
  calculus along a piecewise-`C¹` curve.
-/

public section

namespace TauCeti.Contour

open Set MeasureTheory intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set ℂ} {f : ℂ → E}

/-- **The fundamental theorem of calculus along a piecewise-`C¹` curve.** If `F` has derivative
`f` on a set `U` containing a piecewise-`C¹` curve `γ`, and `f` is continuous on `U`, then the
contour integral `∫ t in a..b, γ' t • f (γ t)` is `F (γ b) - F (γ a)`. -/
theorem intervalIntegral_deriv_smul_eq_sub_of_hasDerivAt [CompleteSpace E] {F : ℂ → E}
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (hγU : MapsTo γ (uIcc a b) U)
    (hf : ContinuousOn f U) (hF : ∀ z ∈ U, HasDerivAt F (f z) z) :
    ∫ t in a..b, deriv γ t • f (γ t) = F (γ b) - F (γ a) := by
  obtain ⟨P, hP, hPd⟩ := hγ.exists_countable_differentiableAt
  refine integral_eq_of_hasDerivAt_off_countable (fun t => F (γ t)) _ hP ?_
    (fun t ht => ?_) (hγ.intervalIntegrable_deriv_smul_comp_of_mapsTo hf hγU)
  · exact fun t ht => (hF _ (hγU ht)).continuousAt.comp_continuousWithinAt (hγ.continuousOn t ht)
  · have htu : t ∈ uIcc a b := by
      rw [← Icc_min_max]
      exact Ioo_subset_Icc_self ht.1
    exact (hF _ (hγU htu)).scomp t (hPd t ht).hasDerivAt

end TauCeti.Contour
