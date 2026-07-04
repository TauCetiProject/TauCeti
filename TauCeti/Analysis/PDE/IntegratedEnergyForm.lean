/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyFormIntegrability
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrated divergence-form energy forms

Lane D of the PDE roadmap asks for the weak energy form

`a(u, v) = ∫ aⁱʲ ∂ᵢu ∂ⱼv + bⁱ ∂ᵢu v + c u v`.

The preceding PDE files build the pointwise jet integrand
`energyIntegrand (a x) (b x) (c x)` and prove the measurability and integrability estimates
needed to integrate it.  This file performs that integration for raw jet fields
`U V : X → ℝ × EuclideanSpace ℝ n`.  It deliberately does not define a Sobolev space or weak
derivative: once Lane A supplies `W^{k,p}(Ω)`, its value-gradient jets can feed this definition.

## Main declarations

* `TauCeti.PDE.energyFormIntegral`: the integrated scalar energy form on two jet fields.
* `TauCeti.PDE.energyFormIntegral_one_zero_zero` and
  `TauCeti.PDE.energyFormIntegral_one_zero_mass`: the `−Δ` and shifted-`−Δ + c` model forms.
* `TauCeti.PDE.energyFormIntegral_add_left`, `TauCeti.PDE.energyFormIntegral_add_right`,
  `TauCeti.PDE.energyFormIntegral_smul_left`, and
  `TauCeti.PDE.energyFormIntegral_smul_right`: bilinearity identities under the usual
  Bochner-integrability hypotheses.
* `TauCeti.PDE.norm_energyFormIntegral_le_of_bound`: the integrated boundedness estimate
  obtained from the pointwise coefficient bounds.
-/

public section

namespace TauCeti

namespace PDE

open MeasureTheory Matrix
open scoped InnerProductSpace

variable {X n : Type*} [MeasurableSpace X] [Fintype n]

/-- The scalar energy form obtained by integrating the divergence-form pointwise jet
integrand against a measure.

For a Sobolev function `u`, the intended jet field is `x ↦ (u x, ∇u x)`.  This definition stays
at the raw-jet level because the roadmap's weak-derivative Sobolev spaces are a separate
prerequisite. -/
public noncomputable def energyFormIntegral (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (U V : X → ℝ × EuclideanSpace ℝ n) : ℝ :=
  ∫ x, (energyIntegrand (a x) (b x) (c x) (U x) (V x)) ∂μ

/-- Unfolding rule for the integrated energy form. -/
theorem energyFormIntegral_def (μ : Measure X) (a : X → Matrix n n ℝ)
    (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
    (U V : X → ℝ × EuclideanSpace ℝ n) :
    energyFormIntegral μ a b c U V =
      ∫ x, (energyIntegrand (a x) (b x) (c x) (U x) (V x)) ∂μ :=
  by simp [energyFormIntegral]

variable (μ : Measure X) (a : X → Matrix n n ℝ)
variable (b : X → EuclideanSpace ℝ n) (c : X → ℝ)
variable (U V W : X → ℝ × EuclideanSpace ℝ n)

/-- The integrated energy form respects almost-everywhere equality of all coefficient and jet
fields. -/
lemma energyFormIntegral_congr_ae {a' : X → Matrix n n ℝ} {b' : X → EuclideanSpace ℝ n}
    {c' : X → ℝ} {U' V' : X → ℝ × EuclideanSpace ℝ n}
    (ha : a =ᵐ[μ] a') (hb : b =ᵐ[μ] b') (hc : c =ᵐ[μ] c')
    (hU : U =ᵐ[μ] U') (hV : V =ᵐ[μ] V') :
    energyFormIntegral μ a b c U V = energyFormIntegral μ a' b' c' U' V' := by
  rw [energyFormIntegral_def, energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ha, hb, hc, hU, hV] with x hax hbx hcx hUx hVx
  simp [hax, hbx, hcx, hUx, hVx]

/-- Additivity in the left jet field, assuming the two summand energy densities are
integrable. -/
lemma energyFormIntegral_add_left
    (hU : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (hW : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (W x) (V x)) μ) :
    energyFormIntegral μ a b c (fun x => U x + W x) V =
      energyFormIntegral μ a b c U V + energyFormIntegral μ a b c W V := by
  rw [energyFormIntegral_def, energyFormIntegral_def, energyFormIntegral_def]
  rw [show (∫ x, (energyIntegrand (a x) (b x) (c x) ((fun y => U y + W y) x) (V x)) ∂μ)
      = ∫ x, (energyIntegrand (a x) (b x) (c x) (U x) (V x) +
          energyIntegrand (a x) (b x) (c x) (W x) (V x)) ∂μ by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp]
  exact integral_add hU hW

/-- Additivity in the right jet field, assuming the two summand energy densities are
integrable. -/
lemma energyFormIntegral_add_right
    (hV : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ)
    (hW : Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (W x)) μ) :
    energyFormIntegral μ a b c U (fun x => V x + W x) =
      energyFormIntegral μ a b c U V + energyFormIntegral μ a b c U W := by
  rw [energyFormIntegral_def, energyFormIntegral_def, energyFormIntegral_def]
  rw [show (∫ x, (energyIntegrand (a x) (b x) (c x) (U x) ((fun y => V y + W y) x)) ∂μ)
      = ∫ x, (energyIntegrand (a x) (b x) (c x) (U x) (V x) +
          energyIntegrand (a x) (b x) (c x) (U x) (W x)) ∂μ by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x =>
      map_add (energyIntegrand (a x) (b x) (c x) (U x)) (V x) (W x)]
  exact integral_add hV hW

/-- Homogeneity in the left jet field. -/
lemma energyFormIntegral_smul_left (r : ℝ) :
    energyFormIntegral μ a b c (fun x => r • U x) V =
      r * energyFormIntegral μ a b c U V := by
  rw [energyFormIntegral_def, energyFormIntegral_def]
  rw [show (∫ x, (energyIntegrand (a x) (b x) (c x) ((fun y => r • U y) x) (V x)) ∂μ)
      = ∫ x, (r • energyIntegrand (a x) (b x) (c x) (U x) (V x)) ∂μ by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp]
  rw [MeasureTheory.integral_smul]
  rfl

/-- Homogeneity in the right jet field. -/
lemma energyFormIntegral_smul_right (r : ℝ) :
    energyFormIntegral μ a b c U (fun x => r • V x) =
      r * energyFormIntegral μ a b c U V := by
  rw [energyFormIntegral_def, energyFormIntegral_def]
  rw [show (∫ x, (energyIntegrand (a x) (b x) (c x) (U x) ((fun y => r • V y) x)) ∂μ)
      = ∫ x, (r • energyIntegrand (a x) (b x) (c x) (U x) (V x)) ∂μ by
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp]
  rw [MeasureTheory.integral_smul]
  rfl

variable [DecidableEq n]

/-- The integrated `−Δ` model form is the integral of the dot product of the two gradient
components of the jet fields. -/
lemma energyFormIntegral_one_zero_zero :
    energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) (fun _ => 0) U V =
      ∫ x, ((V x).2 ⬝ᵥ (U x).2) ∂μ := by
  simp [energyFormIntegral_def]

/-- The integrated shifted Laplacian model form `−Δ + c` is the sum of the Dirichlet density
and the mass density. -/
lemma energyFormIntegral_one_zero_mass (m : X → ℝ) :
    energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) m U V =
      ∫ x, ((V x).2 ⬝ᵥ (U x).2 + m x * (U x).1 * (V x).1) ∂μ := by
  rw [energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_one_zero_mass_apply (m x) (U x) (V x)

/-- The diagonal of the integrated shifted Laplacian model is the integral of
`‖∇u‖² + c u²` at the jet level. -/
lemma energyFormIntegral_one_zero_mass_self (m : X → ℝ) :
    energyFormIntegral μ (fun _ => (1 : Matrix n n ℝ)) (fun _ => 0) m U U =
      ∫ x, (‖(U x).2‖ ^ 2 + m x * (U x).1 ^ 2) ∂μ := by
  rw [energyFormIntegral_def]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    energyIntegrand_one_zero_mass_self (m x) (U x)

variable {Lam beta gamma : ℝ}

omit [DecidableEq n] in
/-- Integrated boundedness of the raw-jet energy form from pointwise coefficient bounds.

This is the scalar integral version of `norm_energyIntegrand_apply_le_of_bounds`: if the
pointwise jet product `‖U x‖ * ‖V x‖` is integrable, the absolute value of the integrated form
is bounded by `(Λ + β + γ)` times its integral. -/
lemma norm_energyFormIntegral_le_of_bound (hLam : 0 ≤ Lam)
    (ha : ∀ x, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb : ∀ x, ‖b x‖ ≤ beta) (hc : ∀ x, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x => (Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) μ) :
    ‖energyFormIntegral μ a b c U V‖ ≤
      ∫ x, ((Lam + beta + gamma) * (‖U x‖ * ‖V x‖)) ∂μ := by
  rw [energyFormIntegral_def]
  refine norm_integral_le_of_norm_le hUV (Filter.Eventually.of_forall fun x => ?_)
  simpa [mul_assoc] using
    norm_energyIntegrand_apply_le_of_bounds hLam (ha x) (hb x) (hc x) (U x) (V x)

end PDE

end TauCeti
