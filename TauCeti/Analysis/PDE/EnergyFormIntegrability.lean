/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyFormMeasurability
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability of pointwise PDE energy densities

The weak-form lane of the PDE roadmap will define the energy bilinear form by integrating the
pointwise scalar density
`x ↦ energyIntegrand (a x) (b x) (c x) (U x) (V x)`.  The preceding finite-dimensional files
give the measurability of this density and the pointwise bound with explicit coefficient
constants.  This file packages the next handoff: on a finite-measure domain, bounded measurable
coefficient fields and bounded measurable jet fields produce integrable scalar energy densities.

This remains below the Sobolev-space construction.  The coefficient bounds are stated inline,
matching the roadmap's bounded-measurable-coefficient hypotheses.

## Main declarations

* `TauCeti.PDE.integrable_energyIntegrand_apply₂_of_bounds`: coefficient bounds and bounded jet
  fields give scalar-density integrability.
* `TauCeti.PDE.integrable_energyIntegrand_apply_of_bounds`: the fixed-jet specialization.
-/

public section

namespace TauCeti

namespace PDE

open Matrix MeasureTheory
open scoped InnerProductSpace

variable {α n : Type*} [MeasurableSpace α] [Fintype n]
variable {μ : Measure α}

/-- Bounded measurable coefficient fields and bounded measurable jet fields give an integrable
scalar energy density on a finite-measure space. -/
lemma integrable_energyIntegrand_apply₂_of_bounds [IsFiniteMeasure μ]
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma R S : ℝ}
    (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ)
    (hV : AEStronglyMeasurable V μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hU_bound : ∀ᵐ x ∂μ, ‖U x‖ ≤ R)
    (hV_bound : ∀ᵐ x ∂μ, ‖V x‖ ≤ S) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ := by
  refine Integrable.of_bound (aestronglyMeasurable_energyIntegrand_apply₂ ha hb hc hU hV)
    ((Lam + beta + gamma) * R * S) ?_
  filter_upwards [ha_bound, hb_bound, hc_bound, hU_bound, hV_bound] with x hA hb₀ hc₀ hUx hVx
  have hbase := norm_energyIntegrand_apply_le_of_bounds hLam hA hb₀ hc₀ (U x) (V x)
  have hbeta : 0 ≤ beta := (norm_nonneg (b x)).trans hb₀
  have hgamma : 0 ≤ gamma := (norm_nonneg (c x)).trans hc₀
  have hK : 0 ≤ Lam + beta + gamma := add_nonneg (add_nonneg hLam hbeta) hgamma
  have hR : 0 ≤ R := (norm_nonneg (U x)).trans hUx
  calc
    ‖energyIntegrand (a x) (b x) (c x) (U x) (V x)‖
        ≤ (Lam + beta + gamma) * ‖U x‖ * ‖V x‖ := hbase
    _ ≤ (Lam + beta + gamma) * R * S :=
      by
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left
            (mul_le_mul hUx hVx (norm_nonneg (V x)) hR) hK

/-- Fixed-jet specialization of `integrable_energyIntegrand_apply₂_of_bounds`. -/
lemma integrable_energyIntegrand_apply_of_bounds [IsFiniteMeasure μ]
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {Lam beta gamma : ℝ}
    (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (U V : ℝ × EuclideanSpace ℝ n) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) U V) μ :=
  integrable_energyIntegrand_apply₂_of_bounds (U := fun _ => U) (V := fun _ => V)
    hLam ha hb hc aestronglyMeasurable_const aestronglyMeasurable_const
    ha_bound hb_bound hc_bound (Filter.Eventually.of_forall fun _ => le_rfl)
    (Filter.Eventually.of_forall fun _ => le_rfl)

end PDE

end TauCeti
