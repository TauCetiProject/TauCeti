/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Complex.Basic

/-!
# The fundamental theorem of calculus along a contour

This file records the elementary arc-FTC step used by the contour-integration roadmap: if
`F' = f` along the image of a raw curve `γ : ℝ → ℂ`, then the contour integral of `f` along `γ`
is the endpoint difference `F (γ b) - F (γ a)`, and hence vanishes for a closed curve. The
statements keep the roadmap's raw-function convention and use the ordinary interval integral
`∫ t in a..b, γ' t • f (γ t)`.

This is the Layer 2 "FTC along an arc" prerequisite for Cauchy's theorem and the later residue
theorems. It is just the chain rule plus Mathlib's interval-integral fundamental theorem of
calculus.

## Main results

* `Contour.contourIntegral_eq_sub_of_hasDerivAt` — an explicit-velocity form using a supplied
  derivative `γ'`.
* `Contour.contourIntegral_deriv_eq_sub_of_hasDerivAt` — the same statement with `deriv γ`.
* `Contour.contourIntegral_eq_zero_of_hasDerivAt_of_closed` and
  `Contour.contourIntegral_deriv_eq_zero_of_hasDerivAt_of_closed` — closed-curve corollaries.

## Provenance

This is routine API around Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt`, following the contour-integral convention in
the Hungerbühler--Wasem contour-integration roadmap; no formal source is vendored.
-/

public section

noncomputable section

namespace TauCeti.Contour

open MeasureTheory

variable {γ γ' : ℝ → ℂ} {g G : ℂ → ℂ} {a b : ℝ}

/-- **FTC along a contour, explicit-velocity form.** If `γ' t` is the derivative of the curve
`γ` and `G' = g` at the points `γ t`, then the contour integral of `g` along `γ` is the endpoint
difference `G (γ b) - G (γ a)`. The integrability hypothesis is stated directly on the contour
integrand, so this lemma can be used with any regularity package that supplies it. -/
theorem contourIntegral_eq_sub_of_hasDerivAt
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hG : ∀ t ∈ Set.uIcc a b, HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => γ' t • g (γ t)) volume a b) :
    ∫ t in a..b, γ' t • g (γ t) = G (γ b) - G (γ a) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hG t ht).scomp t (hγ t ht)) hint

/-- **FTC along a contour, `deriv` form.** If `G' = g` along the image of a differentiable curve,
then the contour integral written with `deriv γ` is the endpoint difference
`G (γ b) - G (γ a)`. -/
theorem contourIntegral_deriv_eq_sub_of_hasDerivAt
    (hγ : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ γ t)
    (hG : ∀ t ∈ Set.uIcc a b, HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => deriv γ t • g (γ t)) volume a b) :
    ∫ t in a..b, deriv γ t • g (γ t) = G (γ b) - G (γ a) :=
  contourIntegral_eq_sub_of_hasDerivAt
    (γ' := fun t => deriv γ t) (fun t ht => (hγ t ht).hasDerivAt) hG hint

/-- A contour integral of an exact derivative vanishes on a closed curve, explicit-velocity form. -/
theorem contourIntegral_eq_zero_of_hasDerivAt_of_closed
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hG : ∀ t ∈ Set.uIcc a b, HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => γ' t • g (γ t)) volume a b)
    (hclosed : γ a = γ b) :
    ∫ t in a..b, γ' t • g (γ t) = 0 := by
  rw [contourIntegral_eq_sub_of_hasDerivAt hγ hG hint, hclosed, sub_self]

/-- A contour integral of an exact derivative vanishes on a closed curve, `deriv` form. -/
theorem contourIntegral_deriv_eq_zero_of_hasDerivAt_of_closed
    (hγ : ∀ t ∈ Set.uIcc a b, DifferentiableAt ℝ γ t)
    (hG : ∀ t ∈ Set.uIcc a b, HasDerivAt G (g (γ t)) (γ t))
    (hint : IntervalIntegrable (fun t => deriv γ t • g (γ t)) volume a b)
    (hclosed : γ a = γ b) :
    ∫ t in a..b, deriv γ t • g (γ t) = 0 := by
  rw [contourIntegral_deriv_eq_sub_of_hasDerivAt hγ hG hint, hclosed, sub_self]

end TauCeti.Contour

end
