/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration on groups

Integrating against an inverse measure is equivalent to precomposing the integrand with
inversion. This transports integrals between left and right Haar measures.

For a measure invariant under addition, an integral over a ball can be translated to a ball
about the origin. Only measurability of translations is needed; the measure need not be an
additive Haar measure, and the function need not be integrable.

For a measure invariant under a group action, an integrand invariant under `g` has the same
integral, and the same integrability, on `g • V` as on `V`.

## Main declarations

* `TauCeti.setIntegral_ball_eq_setIntegral_ball_zero_add`: translating a ball integral to the
  origin.
* `TauCeti.setIntegral_smul_set`, `TauCeti.integrableOn_smul_set_iff`: integrals and
  integrability of an invariant integrand over a translated set.
-/

public section

open MeasureTheory Metric Set

open scoped Pointwise

namespace TauCeti

/-- An integral against `μ.inv` is an integral against `μ` with the argument inverted.
This orientation removes the inverse measure and needs no integrability assumption. -/
theorem integral_inv_measure {G E : Type*} [MeasurableSpace G] [InvolutiveInv G]
    [MeasurableInv G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : G → E) (μ : Measure G) :
    ∫ x, f x ∂μ.inv = ∫ x, f x⁻¹ ∂μ := by
  rw [Measure.inv_def]
  exact integral_map_equiv (MeasurableEquiv.inv G) f

/-- For a measure invariant under right addition, the integral over `ball x₀ R` is the integral
over `ball 0 R` of the translate `y ↦ f (y + x₀)`. No integrability hypothesis is needed. -/
theorem setIntegral_ball_eq_setIntegral_ball_zero_add
    {E F : Type*} [SeminormedAddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    {μ : Measure E} [μ.IsAddRightInvariant] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x₀ : E) (R : ℝ) :
    ∫ x in ball x₀ R, f x ∂μ = ∫ y in ball (0 : E) R, f (y + x₀) ∂μ := by
  simpa using ((measurePreserving_add_right μ x₀).setIntegral_preimage_emb
    (MeasurableEquiv.addRight x₀).measurableEmbedding f (ball x₀ R)).symm

section SMulSet

variable {G α E : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
  {μ : Measure α} [SMulInvariantMeasure G α μ] [NormedAddCommGroup E]

/-- For an invariant measure, an integrand invariant under `g` is integrable on `g • V` exactly
when it is integrable on `V`. -/
theorem integrableOn_smul_set_iff {g : G} {f : α → E} (hf : ∀ x, f (g • x) = f x)
    (V : Set α) : IntegrableOn f (g • V) μ ↔ IntegrableOn f V μ := by
  rw [← image_smul, (measurePreserving_smul g μ).integrableOn_image
    (measurableEmbedding_const_smul g)]
  exact iff_of_eq (congrArg (IntegrableOn · V μ) (funext hf))

variable [NormedSpace ℝ E]

/-- For an invariant measure, an integrand invariant under `g` has the same integral over
`g • V` as over `V`. No integrability or measurability hypothesis is needed. -/
theorem setIntegral_smul_set {g : G} {f : α → E} (hf : ∀ x, f (g • x) = f x)
    (V : Set α) : ∫ x in g • V, f x ∂μ = ∫ x in V, f x ∂μ := by
  rw [← image_smul, (measurePreserving_smul g μ).setIntegral_image_emb
    (measurableEmbedding_const_smul g) f V]
  simp_rw [hf]

end SMulSet

end TauCeti
