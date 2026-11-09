/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Complex.Basic

/-!
# Reparametrization invariance of the contour integral

A contour integral `∫ t in a..b, deriv γ t • f (γ t)` is unchanged when the curve `γ` is
precomposed with a `C¹` change of parameter `φ`, the parameter interval `[[a, b]]` being replaced
by `[[φ a, φ b]]`. This file proves that invariance, together with the chain rule for the
reparametrized curve that it rests on.

The proof is the interval-integral change-of-variables formula
`intervalIntegral.integral_deriv_smul_comp'` applied to the contour integrand
`g u = deriv γ u • f (γ u)`, together with the chain rule
`deriv (γ ∘ φ) t = φ' t • deriv γ (φ t)`.

Three design points are worth flagging.

* Regularity is asked for as **ambient** pointwise derivatives, not `ContDiffOn`: `φ` satisfies
  `HasDerivAt φ (φ' t) t` at each `t ∈ [[a, b]]` and `γ` satisfies `DifferentiableAt ℝ γ` on the
  image, both two-sided in the ambient sense rather than merely within the set. This matches the
  global `deriv γ` appearing in the contour integrand, which the chain rule identifying
  `deriv (γ ∘ φ)` needs pointwise. "`C¹`" in the docstrings below is shorthand for exactly this
  data.
* The regularity hypotheses are placed on the **image** `φ '' [[a, b]]`, not on `[[φ a, φ b]]`.
  This is the honest domain: `φ` is not assumed monotone, so the composite curve may sweep past the
  endpoints `φ a`, `φ b` and back. The intermediate value theorem
  (`intermediate_value_uIcc`) supplies `[[φ a, φ b]] ⊆ φ '' [[a, b]]`, so the hypotheses on the
  image also cover the reparametrized interval, and no monotonicity is needed anywhere.
* The curve `γ` is asked to be `C¹` with no breakpoints; piecewise-`C¹` curves and the on-curve
  principal-value case are not treated here.

The chain-rule statements hold for a curve in any real normed space; the integral statement takes
a complex curve and an integrand `f` with values in any complex normed space.

## Main results

* `TauCeti.Contour.eqOn_deriv_comp_reparam` — the chain rule for a reparametrized curve on
  `[[a, b]]`, in the `deriv` form used by the contour integrand.
* `TauCeti.Contour.continuousOn_deriv_comp_reparam` — continuity of `deriv (γ ∘ φ)` on `[[a, b]]`,
  the regularity every consumer of the reparametrized contour integrand needs for integrability.
* `TauCeti.Contour.integral_deriv_smul_comp_reparam` — reparametrization invariance of the contour
  integral `∫ t in a..b, deriv γ t • f (γ t)`.

The winding-number consequences live in `TauCeti/Analysis/Contour/Winding/Number/Reparam.lean`.

## Provenance

This is routine API around the contour integrand; no formal source is vendored. The
change-of-variables input `intervalIntegral.integral_deriv_smul_comp'` is Mathlib's.
-/

public section

noncomputable section

namespace TauCeti.Contour

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {φ φ' : ℝ → ℝ} {a b : ℝ}

/-- On `[[a, b]]`, the derivative of the reparametrized curve is `φ' • (deriv γ ∘ φ)`. This is the
set-level chain rule, packaged for `ContinuousOn` and integral congruences. Here `φ` has an ambient
derivative `φ' t` at each `t ∈ [[a, b]]` and `γ` is ambient-differentiable on the swept image. -/
theorem eqOn_deriv_comp_reparam {γ : ℝ → F} (hφ : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t)
    (hγ : ∀ u ∈ φ '' Set.uIcc a b, DifferentiableAt ℝ γ u) :
    Set.EqOn (deriv (γ ∘ φ)) (fun t => φ' t • deriv γ (φ t)) (Set.uIcc a b) :=
  fun t ht => ((hγ (φ t) ⟨t, ht, rfl⟩).hasDerivAt.scomp t (hφ t ht)).deriv

/-- Continuity of the derivative of the reparametrized curve on `[[a, b]]`, the regularity every
consumer of the reparametrized contour integrand needs for integrability. As elsewhere, `φ` has an
ambient derivative `φ' t` at each `t ∈ [[a, b]]` with `φ'` continuous there, and `γ` is
ambient-differentiable with continuous derivative on the swept image `φ '' [[a, b]]`. -/
theorem continuousOn_deriv_comp_reparam {γ : ℝ → F}
    (hφ : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t) (hφ' : ContinuousOn φ' (Set.uIcc a b))
    (hγ : ∀ u ∈ φ '' Set.uIcc a b, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (φ '' Set.uIcc a b)) :
    ContinuousOn (deriv (γ ∘ φ)) (Set.uIcc a b) :=
  (hφ'.smul (hγ'.comp (HasDerivAt.continuousOn hφ) (Set.mapsTo_image φ _))).congr
    (eqOn_deriv_comp_reparam hφ hγ)

/-- **Reparametrization invariance of the contour integral.** If `φ` has an ambient derivative
`φ' t` at each `t ∈ [[a, b]]` with `φ'` continuous there, `γ` is ambient-differentiable with
continuous derivative on the swept image `φ '' [[a, b]]`, and `f` is continuous on the image of the
curve, then integrating `f` along the reparametrized curve `γ ∘ φ` over `[[a, b]]` gives the same
value as integrating along `γ` over `[[φ a, φ b]]`. -/
theorem integral_deriv_smul_comp_reparam {γ : ℝ → ℂ} {f : ℂ → E}
    (hφ : ∀ t ∈ Set.uIcc a b, HasDerivAt φ (φ' t) t) (hφ' : ContinuousOn φ' (Set.uIcc a b))
    (hγ : ∀ u ∈ φ '' Set.uIcc a b, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (φ '' Set.uIcc a b))
    (hf : ContinuousOn f (γ '' (φ '' Set.uIcc a b))) :
    ∫ t in a..b, deriv (γ ∘ φ) t • f ((γ ∘ φ) t) = ∫ u in φ a..φ b, deriv γ u • f (γ u) := by
  have hγcont : ContinuousOn γ (φ '' Set.uIcc a b) :=
    continuousOn_of_forall_continuousAt fun u hu => (hγ u hu).continuousAt
  refine (intervalIntegral.integral_congr fun t ht => ?_).trans
    (intervalIntegral.integral_deriv_smul_comp' hφ hφ'
      (hγ'.smul (hf.comp hγcont (Set.mapsTo_image γ _))))
  simp only [Function.comp_apply, eqOn_deriv_comp_reparam hφ hγ ht, smul_assoc]

end TauCeti.Contour

end
