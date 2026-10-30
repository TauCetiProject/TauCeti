/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.RCLike.Basic

/-!
# The fundamental theorem of calculus along a contour

If `G' = g` along the image of a curve `γ : ℝ → 𝕜`, then the contour integral of `g` along `γ`
is the endpoint difference `G (γ b) - G (γ a)`, and hence vanishes for a closed curve. The curve
is a raw function `γ : ℝ → 𝕜` on a parameter interval `[a, b]`, with no bundled path structure,
and the contour integral is the ordinary interval integral `∫ t in a..b, g (γ t) * γ' t`, where
`γ'` is either a supplied velocity or `deriv γ`. The statements hold over any `RCLike` field `𝕜`;
the complex-analytic case is `𝕜 = ℂ`.

This is the statement that a function with a primitive integrates to zero around closed curves,
the elementary input to Cauchy's theorem and to the residue theorems. It is the chain rule
combined with Mathlib's interval-integral fundamental theorem of calculus.

## Main results

* `Contour.integral_comp_mul_eq_sub_of_hasDerivAt` — an explicit-velocity form using a supplied
  derivative `γ'`.
* `Contour.integral_comp_mul_deriv_eq_sub_of_hasDerivAt` — the same statement with `deriv γ`.
* `Contour.integral_comp_mul_eq_zero_of_hasDerivAt_of_closed` and
  `Contour.integral_comp_mul_deriv_eq_zero_of_hasDerivAt_of_closed` — closed-curve corollaries.

## Provenance

This is routine API around Mathlib's `intervalIntegral.integral_eq_sub_of_hasDeriv_right`,
following the contour-integral convention of N. Hungerbühler, M. Wasem, *Non-integer valued
winding numbers and a generalized Residue Theorem*, arXiv:1808.00997. Earlier formalizations of
the same step appear in the AINTLIB `LeanModularForms` sources
`ForMathlib/GeneralizedResidueTheory/CauchyPrimitive.lean`,
`ForMathlib/GeneralizedResidueTheory/ArcCalculus.lean`, and `ForMathlib/ArcFTC*.lean`; no formal
source is vendored here.
-/

public section

noncomputable section

namespace TauCeti.Contour

open MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] {γ γ' : ℝ → 𝕜} {g G : 𝕜 → 𝕜} {a b : ℝ}

/-- **FTC along a contour, explicit-velocity form.** If `γ' t` is the derivative of the curve
`γ` and `G' = g` at the points `γ t`, then the contour integral of `g` along `γ` is the endpoint
difference `G (γ b) - G (γ a)`. The integrability hypothesis is stated directly on the contour
integrand, so this lemma can be used with any regularity package that supplies it. -/
theorem integral_comp_mul_eq_sub_of_hasDerivAt (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt γ (γ' t) t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => g (γ t) * γ' t) volume a b) :
    ∫ t in a..b, g (γ t) * γ' t = G (γ b) - G (γ a) :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont
    (fun t ht => ((hG t ht).comp t (hγ t ht)).hasDerivWithinAt) hint

/-- **FTC along a contour, `deriv` form.** If `G' = g` along the image of a differentiable curve,
then the contour integral written with `deriv γ` is the endpoint difference
`G (γ b) - G (γ a)`. -/
theorem integral_comp_mul_deriv_eq_sub_of_hasDerivAt (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), DifferentiableAt ℝ γ t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => g (γ t) * deriv γ t) volume a b) :
    ∫ t in a..b, g (γ t) * deriv γ t = G (γ b) - G (γ a) :=
  integral_comp_mul_eq_sub_of_hasDerivAt hcont (fun t ht => (hγ t ht).hasDerivAt) hG hint

/-- A contour integral of an exact derivative vanishes on a closed curve, explicit-velocity form. -/
theorem integral_comp_mul_eq_zero_of_hasDerivAt_of_closed
    (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt γ (γ' t) t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => g (γ t) * γ' t) volume a b) (hclosed : γ a = γ b) :
    ∫ t in a..b, g (γ t) * γ' t = 0 := by
  rw [integral_comp_mul_eq_sub_of_hasDerivAt hcont hγ hG hint, hclosed, sub_self]

/-- A contour integral of an exact derivative vanishes on a closed curve, `deriv` form. -/
theorem integral_comp_mul_deriv_eq_zero_of_hasDerivAt_of_closed
    (hcont : ContinuousOn (G ∘ γ) (Set.uIcc a b))
    (hγ : ∀ t ∈ Set.Ioo (min a b) (max a b), DifferentiableAt ℝ γ t)
    (hG : ∀ t ∈ Set.Ioo (min a b) (max a b), HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => g (γ t) * deriv γ t) volume a b) (hclosed : γ a = γ b) :
    ∫ t in a..b, g (γ t) * deriv γ t = 0 :=
  integral_comp_mul_eq_zero_of_hasDerivAt_of_closed hcont (fun t ht => (hγ t ht).hasDerivAt) hG
    hint hclosed

end TauCeti.Contour

end
