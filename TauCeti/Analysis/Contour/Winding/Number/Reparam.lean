/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import TauCeti.Analysis.Contour.NullHomologous

/-!
# Reparametrization invariance for contour integrals and winding numbers

A contour integral `∫ t in a..b, deriv γ t • f (γ t)` depends on the curve `γ` only through its
oriented image: precomposing `γ` with a `C¹` change of parameter `φ` and integrating over a
parameter interval `[c, d]` with `φ c = a`, `φ d = b` gives the same value. This file records that
invariance and its consequence for the generalized winding number of Hungerbühler–Wasem Def 2.1.

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

Only the off-curve case is treated: when `z₀` lies on the curve the winding number is a Cauchy
principal value, whose symmetric excision windows are themselves reparametrized, and transporting
them is a separate argument. This is the case that the roadmap's cycle bookkeeping consumes.

## Main results

* `TauCeti.Contour.deriv_comp_reparam` — the chain rule for a reparametrized curve, in the
  `deriv` form used by the contour integrand.
* `TauCeti.Contour.integral_deriv_smul_comp_reparam` — reparametrization invariance of the contour
  integral `∫ t in a..b, deriv γ t • f (γ t)`.
* `TauCeti.Contour.windingNumber_comp_reparam` — the generalized winding number about a point off
  the curve is unchanged by a `C¹` reparametrization.
* `TauCeti.Contour.windingNumber_comp_affine` — the affine special case `φ t = α * t + β`.
* `TauCeti.Contour.IsNullHomologous.comp_reparam` — null-homology transports along a `C¹`
  reparametrization of a curve lying in the ambient set.

This is Layer 0 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3): the
reparametrization-invariance API that the cycle layer needs in order to treat a closed curve
independently of its parametrization.

## Provenance

This is routine API around the Hungerbühler--Wasem generalized winding number from the contour
integration roadmap; no formal source is vendored. The change-of-variables input
`intervalIntegral.integral_deriv_smul_comp'` is Mathlib's.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Def 2.1.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {φ φ' : ℝ → ℝ} {c d : ℝ} {z₀ : ℂ} {f : ℂ → ℂ} {Ω : Set ℂ}

/-- **Chain rule for a reparametrized curve.** If `φ` has derivative `φ' t` at `t` and `γ` is
differentiable at `φ t`, then the composite curve `γ ∘ φ` has derivative `φ' t • deriv γ (φ t)`.
Stated with `HasDerivAt` so that callers can extract either the derivative value or the
differentiability. -/
theorem hasDerivAt_comp_reparam {t : ℝ} (hφ : HasDerivAt φ (φ' t) t)
    (hγ : DifferentiableAt ℝ γ (φ t)) :
    HasDerivAt (γ ∘ φ) (φ' t • deriv γ (φ t)) t :=
  hγ.hasDerivAt.scomp t hφ

/-- The `deriv` form of `hasDerivAt_comp_reparam`: the derivative of a reparametrized curve is the
speed of the parameter change times the derivative of the curve. This is the identity that turns the
contour integrand of `γ ∘ φ` into the change-of-variables integrand `φ' • (g ∘ φ)`. -/
theorem deriv_comp_reparam {t : ℝ} (hφ : HasDerivAt φ (φ' t) t)
    (hγ : DifferentiableAt ℝ γ (φ t)) :
    deriv (γ ∘ φ) t = φ' t • deriv γ (φ t) :=
  (hasDerivAt_comp_reparam hφ hγ).deriv

section Regularity

variable (hφ : ∀ t ∈ Set.uIcc c d, HasDerivAt φ (φ' t) t)
  (hγ : ∀ u ∈ φ '' Set.uIcc c d, DifferentiableAt ℝ γ u)

include hφ

/-- A parameter change with a derivative everywhere on `[[c, d]]` is continuous there. -/
private theorem continuousOn_of_hasDerivAt : ContinuousOn φ (Set.uIcc c d) :=
  fun t ht => (hφ t ht).continuousAt.continuousWithinAt

/-- The reparametrized interval `[[φ c, φ d]]` is contained in the image `φ '' [[c, d]]`, by the
intermediate value theorem. Hypotheses stated on the image therefore also apply on `[[φ c, φ d]]`;
no monotonicity of `φ` is needed. -/
theorem uIcc_endpoints_subset_image : Set.uIcc (φ c) (φ d) ⊆ φ '' Set.uIcc c d :=
  intermediate_value_uIcc (continuousOn_of_hasDerivAt hφ)

include hγ

omit hφ in
/-- A curve differentiable on the image of the parameter change is continuous there. -/
private theorem continuousOn_of_differentiableAt : ContinuousOn γ (φ '' Set.uIcc c d) :=
  fun u hu => (hγ u hu).continuousAt.continuousWithinAt

/-- On `[[c, d]]`, the derivative of the reparametrized curve is `φ' • (deriv γ ∘ φ)`. The
set-level form of `deriv_comp_reparam`, packaged for `ContinuousOn` and integral congruences. -/
theorem eqOn_deriv_comp_reparam :
    Set.EqOn (deriv (γ ∘ φ)) (fun t => φ' t • deriv γ (φ t)) (Set.uIcc c d) :=
  fun t ht => deriv_comp_reparam (hφ t ht) (hγ (φ t) ⟨t, ht, rfl⟩)

end Regularity

/-- **Reparametrization invariance of the contour integral.** If `φ` is `C¹` on `[[c, d]]`, the
curve `γ` is `C¹` on the swept image `φ '' [[c, d]]`, and `f` is continuous on the image of the
curve, then integrating `f` along the reparametrized curve `γ ∘ φ` over `[[c, d]]` gives the same
value as integrating along `γ` over `[[φ c, φ d]]`. This is Mathlib's change-of-variables formula
applied to the contour integrand `u ↦ deriv γ u • f (γ u)`. -/
theorem integral_deriv_smul_comp_reparam
    (hφ : ∀ t ∈ Set.uIcc c d, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.uIcc c d))
    (hγ : ∀ u ∈ φ '' Set.uIcc c d, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (φ '' Set.uIcc c d))
    (hf : ContinuousOn f (γ '' (φ '' Set.uIcc c d))) :
    ∫ t in c..d, deriv (γ ∘ φ) t • f (γ (φ t)) = ∫ u in φ c..φ d, deriv γ u • f (γ u) := by
  have hgcont : ContinuousOn (fun u => deriv γ u • f (γ u)) (φ '' Set.uIcc c d) :=
    hγ'.smul ((hf.comp (continuousOn_of_differentiableAt hγ) (Set.mapsTo_image γ _)))
  have hcongr : Set.EqOn (fun t => deriv (γ ∘ φ) t • f (γ (φ t)))
      (fun t => φ' t • ((fun u => deriv γ u • f (γ u)) ∘ φ) t) (Set.uIcc c d) := by
    intro t ht
    simp only [Function.comp_apply, eqOn_deriv_comp_reparam hφ hγ ht, smul_assoc]
  rw [intervalIntegral.integral_congr hcongr]
  exact intervalIntegral.integral_deriv_smul_comp' hφ hφ' hgcont

/-- **Reparametrization invariance of the generalized winding number** (HW Def 2.1), for a point
`z₀` off the curve. A `C¹` change of parameter `φ` leaves the winding number unchanged, the
parameter interval `[[c, d]]` being replaced by `[[φ c, φ d]]`.

All hypotheses are stated on the swept image `φ '' [[c, d]]`, which contains `[[φ c, φ d]]` by the
intermediate value theorem, so `φ` need not be monotone. Off-curve is essential: on the curve the
winding number is a principal value, whose excision windows are themselves reparametrized. -/
theorem windingNumber_comp_reparam
    (hφ : ∀ t ∈ Set.uIcc c d, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.uIcc c d))
    (hγ : ∀ u ∈ φ '' Set.uIcc c d, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (φ '' Set.uIcc c d))
    (havoid : ∀ u ∈ φ '' Set.uIcc c d, γ u ≠ z₀) :
    windingNumber (γ ∘ φ) c d z₀ = windingNumber γ (φ c) (φ d) z₀ := by
  have hφcont : ContinuousOn φ (Set.uIcc c d) := continuousOn_of_hasDerivAt hφ
  have hγcont : ContinuousOn γ (φ '' Set.uIcc c d) := continuousOn_of_differentiableAt hγ
  have hsub : Set.uIcc (φ c) (φ d) ⊆ φ '' Set.uIcc c d := uIcc_endpoints_subset_image hφ
  have hmaps : Set.MapsTo φ (Set.uIcc c d) (φ '' Set.uIcc c d) := Set.mapsTo_image φ _
  -- the kernel `(· - z₀)⁻¹` is continuous along the curve, since `γ` avoids `z₀`
  have hker : ContinuousOn (fun z : ℂ => (z - z₀)⁻¹) (γ '' (φ '' Set.uIcc c d)) := by
    refine (continuousOn_id.sub continuousOn_const).inv₀ ?_
    rintro _ ⟨u, hu, rfl⟩
    exact sub_ne_zero.mpr (havoid u hu)
  -- the index integrand along the reparametrized curve is continuous, hence integrable
  have hderivcont : ContinuousOn (deriv (γ ∘ φ)) (Set.uIcc c d) :=
    ContinuousOn.congr (hφ'.smul (hγ'.comp hφcont hmaps)) (eqOn_deriv_comp_reparam hφ hγ)
  have hcompcont : ContinuousOn (γ ∘ φ) (Set.uIcc c d) := hγcont.comp hφcont hmaps
  have hcompavoid : ∀ t ∈ Set.uIcc c d, (γ ∘ φ) t ≠ z₀ := fun t ht => havoid (φ t) ⟨t, ht, rfl⟩
  have hintL : IntervalIntegrable
      (fun t => ((γ ∘ φ) t - z₀)⁻¹ * deriv (γ ∘ φ) t) volume c d :=
    (((hcompcont.sub continuousOn_const).inv₀
      fun t ht => sub_ne_zero.mpr (hcompavoid t ht)).mul hderivcont).intervalIntegrable
  have hintR : IntervalIntegrable
      (fun u => (γ u - z₀)⁻¹ * deriv γ u) volume (φ c) (φ d) :=
    ((((hγcont.mono hsub).sub continuousOn_const).inv₀
      fun u hu => sub_ne_zero.mpr (havoid u (hsub hu))).mul (hγ'.mono hsub)).intervalIntegrable
  rw [windingNumber_eq_integral_of_avoidance hcompcont hcompavoid hintL,
    windingNumber_eq_integral_of_avoidance (hγcont.mono hsub)
      (fun u hu => havoid u (hsub hu)) hintR]
  congr 1
  have := integral_deriv_smul_comp_reparam (f := fun z : ℂ => (z - z₀)⁻¹) hφ hφ' hγ hγ' hker
  simpa only [smul_eq_mul, mul_comm, Function.comp_apply] using this

/-- The affine special case of `windingNumber_comp_reparam`: precomposing a curve with
`t ↦ α * t + β` moves the parameter interval to `[[α * c + β, α * d + β]]` and leaves the winding
number about an off-curve point unchanged. Unlike the general statement this needs no separate
continuity hypothesis on the parameter speed, the derivative being the constant `α`. -/
theorem windingNumber_comp_affine {α β : ℝ}
    (hγ : ∀ u ∈ (fun t => α * t + β) '' Set.uIcc c d, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) ((fun t => α * t + β) '' Set.uIcc c d))
    (havoid : ∀ u ∈ (fun t => α * t + β) '' Set.uIcc c d, γ u ≠ z₀) :
    windingNumber (fun t => γ (α * t + β)) c d z₀
      = windingNumber γ (α * c + β) (α * d + β) z₀ :=
  windingNumber_comp_reparam (φ' := fun _ => α)
    (fun t _ => by simpa using ((hasDerivAt_id t).const_mul α).add_const β)
    continuousOn_const hγ hγ' havoid

/-- **Null-homology transports along a reparametrization.** If a curve lies in `Ω` and is
null-homologous there, then so is any `C¹` reparametrization of it: every point outside `Ω` is
automatically off the curve, so `windingNumber_comp_reparam` applies at each such point. -/
theorem IsNullHomologous.comp_reparam
    (h : IsNullHomologous γ (φ c) (φ d) Ω)
    (hφ : ∀ t ∈ Set.uIcc c d, HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' (Set.uIcc c d))
    (hγ : ∀ u ∈ φ '' Set.uIcc c d, DifferentiableAt ℝ γ u)
    (hγ' : ContinuousOn (deriv γ) (φ '' Set.uIcc c d))
    (hγΩ : ∀ u ∈ φ '' Set.uIcc c d, γ u ∈ Ω) :
    IsNullHomologous (γ ∘ φ) c d Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  have havoid : ∀ u ∈ φ '' Set.uIcc c d, γ u ≠ z := by
    intro u hu huz
    exact hz (huz ▸ hγΩ u hu)
  rw [windingNumber_comp_reparam (φ' := φ') hφ hφ' hγ hγ' havoid]
  exact h z hz

end TauCeti.Contour

end
