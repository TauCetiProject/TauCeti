/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Basic

/-!
# Exponential tilting of von Mises–Fisher laws

Tilting a von Mises–Fisher law by the linear weight `exp ⟪θ, x⟫` adds `θ` to its
natural parameter. In direction/concentration coordinates the new concentration is the
norm of the resulting vector and the new direction is given by `sphereDirection`. If the
vectors cancel, this retains the original direction at zero concentration, giving the uniform law.

The natural-parameter identity also includes the empty sphere in dimension zero. The
direction/concentration identity assumes a nonnegative input concentration, as negative
concentrations denote the zero measure.

The composition of tilts uses Mathlib's `MeasureTheory.tilted_tilted` and the
exponential integrability of linear observables on the sphere.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped InnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A linear exponential tilt adds its vector to the natural parameter. This includes
dimension zero, where both sides are the zero measure on the empty sphere. -/
@[simp]
theorem vonMisesFisherNaturalMeasure_tilted_inner (η θ : E) :
    (vonMisesFisherNaturalMeasure η).tilted (fun x ↦ ⟪θ, (x : E)⟫_ℝ) =
      vonMisesFisherNaturalMeasure (η + θ) := by
  rw [vonMisesFisherNaturalMeasure_def,
    tilted_tilted (integrable_exp_inner_uniformSphereMeasure η),
    vonMisesFisherNaturalMeasure_def]
  congr 1
  ext x
  simp only [Pi.add_apply, inner_add_left]

/-- Tilting a direction/concentration law adds the tilt vector to `κ • m`. A zero resultant
retains `m` at zero concentration, giving uniform sphere probability; otherwise its norm and
normalization are the new parameters.
-/
theorem vonMisesFisherMeasure_tilted_inner (m : sphere (0 : E) 1) {κ : ℝ}
    (hκ : 0 ≤ κ) (θ : E) :
    (vonMisesFisherMeasure m κ).tilted (fun x ↦ ⟪θ, (x : E)⟫_ℝ) =
      vonMisesFisherMeasure (sphereDirection m (κ • (m : E) + θ))
        ‖κ • (m : E) + θ‖ := by
  rw [vonMisesFisherMeasure_of_nonneg m hκ, vonMisesFisherNaturalMeasure_tilted_inner,
    vonMisesFisherMeasure_of_nonneg _ (norm_nonneg _), norm_smul_sphereDirection]

end TauCeti.Probability
