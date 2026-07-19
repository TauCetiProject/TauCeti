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
precomposed with a `C¹` change of parameter `φ`, the parameter interval `[[c, d]]` being replaced
by `[[φ c, φ d]]`. This file proves that invariance, together with the chain rule for the
reparametrized curve that it rests on.

The proof is the interval-integral change-of-variables formula
`intervalIntegral.integral_deriv_smul_comp'` applied to the contour integrand
`g u = deriv γ u • f (γ u)`, together with the chain rule
`deriv (γ ∘ φ) t = φ' t • deriv γ (φ t)`.

Two design points are worth flagging.

* The regularity hypotheses are placed on the **image** `φ '' [[c, d]]`, not on `[[φ c, φ d]]`.
  This is the honest domain: `φ` is not assumed monotone, so the composite curve may sweep past the
  endpoints `φ c`, `φ d` and back. The intermediate value theorem
  (`intermediate_value_uIcc`) supplies `[[φ c, φ d]] ⊆ φ '' [[c, d]]`, so the hypotheses on the
  image also cover the reparametrized interval, and no monotonicity is needed anywhere.
* `deriv γ` is the *global* derivative, matching the raw-function design of the roadmap's curve
  layer. Differentiability of `γ` on the image is therefore an explicit hypothesis rather than a
  consequence of continuity, since the chain rule identifying `deriv (γ ∘ φ)` needs it pointwise.

## Main results

* `TauCeti.Contour.deriv_comp_reparam` — the chain rule for a reparametrized curve, in the
  `deriv` form used by the contour integrand.
* `TauCeti.Contour.eqOn_deriv_comp_reparam` — its set-level form on `[[c, d]]`.
* `TauCeti.Contour.integral_deriv_smul_comp_reparam` — reparametrization invariance of the contour
  integral `∫ t in a..b, deriv γ t • f (γ t)`.

The winding-number consequences live in `TauCeti/Analysis/Contour/Winding/Number/Reparam.lean`.

## Provenance

This is routine API around the contour integrand of the contour integration roadmap; no formal
source is vendored. The change-of-variables input `intervalIntegral.integral_deriv_smul_comp'` is
Mathlib's.
-/

public section

noncomputable section

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {φ φ' : ℝ → ℝ} {c d : ℝ} {f : ℂ → ℂ}

/-- **Chain rule for a reparametrized curve**, in `deriv` form: the derivative of `γ ∘ φ` is the
speed of the parameter change times the derivative of the curve. This is the identity that turns
the contour integrand of `γ ∘ φ` into the change-of-variables integrand `φ' • (g ∘ φ)`. -/
theorem deriv_comp_reparam {t : ℝ} (hφ : HasDerivAt φ (φ' t) t)
    (hγ : DifferentiableAt ℝ γ (φ t)) :
    deriv (γ ∘ φ) t = φ' t • deriv γ (φ t) :=
  (hγ.hasDerivAt.scomp t hφ).deriv

section Regularity

variable (hφ : ∀ t ∈ Set.uIcc c d, HasDerivAt φ (φ' t) t)
  (hγ : ∀ u ∈ φ '' Set.uIcc c d, DifferentiableAt ℝ γ u)

include hφ hγ

/-- On `[[c, d]]`, the derivative of the reparametrized curve is `φ' • (deriv γ ∘ φ)`. The
set-level form of `deriv_comp_reparam`, packaged for `ContinuousOn` and integral congruences. -/
theorem eqOn_deriv_comp_reparam :
    Set.EqOn (deriv (γ ∘ φ)) (fun t => φ' t • deriv γ (φ t)) (Set.uIcc c d) :=
  fun t ht => deriv_comp_reparam (hφ t ht) (hγ (φ t) ⟨t, ht, rfl⟩)

end Regularity

/-- **Reparametrization invariance of the contour integral.** If `φ` is `C¹` on `[[c, d]]`, the
curve `γ` is `C¹` on the swept image `φ '' [[c, d]]`, and `f` is continuous on the image of the
curve, then integrating `f` along the reparametrized curve `γ ∘ φ` over `[[c, d]]` gives the same
value as integrating along `γ` over `[[φ c, φ d]]`. -/
theorem integral_deriv_smul_comp_reparam
    (hφ : ∀ t ∈ Set.uIcc c d, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.uIcc c d))
    (hγ : ∀ u ∈ φ '' Set.uIcc c d, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (φ '' Set.uIcc c d))
    (hf : ContinuousOn f (γ '' (φ '' Set.uIcc c d))) :
    ∫ t in c..d, deriv (γ ∘ φ) t • f ((γ ∘ φ) t) = ∫ u in φ c..φ d, deriv γ u • f (γ u) := by
  have hγcont : ContinuousOn γ (φ '' Set.uIcc c d) :=
    fun u hu => (hγ u hu).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn (fun u => deriv γ u • f (γ u)) (φ '' Set.uIcc c d) :=
    hγ'.smul (hf.comp hγcont (Set.mapsTo_image γ _))
  have hcongr : Set.EqOn (fun t => deriv (γ ∘ φ) t • f ((γ ∘ φ) t))
      (fun t => φ' t • ((fun u => deriv γ u • f (γ u)) ∘ φ) t) (Set.uIcc c d) := by
    intro t ht
    simp only [Function.comp_apply, eqOn_deriv_comp_reparam hφ hγ ht, smul_assoc]
  rw [intervalIntegral.integral_congr hcongr]
  exact intervalIntegral.integral_deriv_smul_comp' hφ hφ' hgcont

end TauCeti.Contour

end
