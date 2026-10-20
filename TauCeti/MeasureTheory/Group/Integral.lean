/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration on groups

Integrating against an inverse measure is equivalent to precomposing the integrand with
inversion. This transports integrals between left and right Haar measures.

For a measure invariant under addition, an integral over a ball can be translated to a ball
about the origin. Only measurability of translations is needed; the measure need not be an
additive Haar measure, and the function need not be integrable.

## Main declarations

* `TauCeti.setIntegral_ball_eq_setIntegral_ball_zero_add`: translating a ball integral to the
  origin.
-/

public section

open MeasureTheory Metric

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

end TauCeti
