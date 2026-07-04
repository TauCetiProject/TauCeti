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
constants.  This file packages the next handoff: bounded measurable coefficient fields and
measurable jet fields whose norm product is integrable produce integrable scalar energy
densities.  In particular, this applies to square-integrable jet fields, and specializes on
finite-measure domains to bounded jet fields.

This remains below the Sobolev-space construction.  The coefficient bounds are stated inline,
matching the roadmap's bounded-measurable-coefficient hypotheses.

## Main declarations

* `TauCeti.PDE.integrable_energyIntegrand_apply₂_of_integrable_norm_mul`: coefficient bounds and
  an integrable product of jet norms give scalar-density integrability.
* `TauCeti.PDE.integrable_norm_mul_of_memLp_two`: square-integrable jet fields have integrable
  product of norms.
* `TauCeti.PDE.integrable_energyIntegrand_apply₂_of_memLp_two`: coefficient bounds and
  square-integrable jet fields give scalar-density integrability.
* `TauCeti.PDE.integrable_energyIntegrand_apply₂_of_bounds`: the bounded finite-measure
  specialization.
* `TauCeti.PDE.integrable_energyIntegrand_apply_of_bounds`: the fixed-jet specialization.
-/

public section

namespace TauCeti

namespace PDE

open Matrix MeasureTheory
open scoped InnerProductSpace

variable {α n : Type*} [MeasurableSpace α] [Fintype n]
variable {μ : Measure α}

/-- Bounded measurable coefficient fields and an integrable product of jet norms give an
integrable scalar energy density. -/
lemma integrable_energyIntegrand_apply₂_of_integrable_norm_mul
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma : ℝ}
    (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : AEStronglyMeasurable U μ)
    (hV : AEStronglyMeasurable V μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma)
    (hUV : Integrable (fun x => ‖U x‖ * ‖V x‖) μ) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ := by
  refine (hUV.const_mul (Lam + beta + gamma)).mono'
    (aestronglyMeasurable_energyIntegrand_apply₂ ha hb hc hU hV) ?_
  filter_upwards [ha_bound, hb_bound, hc_bound] with x hA hb₀ hc₀
  simpa [mul_assoc] using norm_energyIntegrand_apply_le_of_bounds hLam hA hb₀ hc₀ (U x) (V x)

/-- Square-integrable jet fields have integrable product of norms. -/
lemma integrable_norm_mul_of_memLp_two
    {U V : α → ℝ × EuclideanSpace ℝ n} (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    Integrable (fun x => ‖U x‖ * ‖V x‖) μ := by
  have hU₂ : Integrable (fun x => ‖U x‖ ^ 2) μ := by
    simpa [ENNReal.toReal_ofNat] using
      hU.integrable_norm_rpow (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)
  have hV₂ : Integrable (fun x => ‖V x‖ ^ 2) μ := by
    simpa [ENNReal.toReal_ofNat] using
      hV.integrable_norm_rpow (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)
  refine ((hU₂.add hV₂).const_mul (1 / 2)).mono' (hU.aestronglyMeasurable.norm.mul
    hV.aestronglyMeasurable.norm) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  change ‖U x‖ * ‖V x‖ ≤ (1 / 2) * (‖U x‖ ^ 2 + ‖V x‖ ^ 2)
  have htwo := two_mul_le_add_sq ‖U x‖ ‖V x‖
  nlinarith

/-- Bounded measurable coefficient fields and square-integrable jet fields give an integrable
scalar energy density. -/
lemma integrable_energyIntegrand_apply₂_of_memLp_two
    {a : α → Matrix n n ℝ} {b : α → EuclideanSpace ℝ n} {c : α → ℝ}
    {U V : α → ℝ × EuclideanSpace ℝ n} {Lam beta gamma : ℝ}
    (hLam : 0 ≤ Lam)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
    (hc : AEStronglyMeasurable c μ) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ)
    (ha_bound : ∀ᵐ x ∂μ, ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (a x *ᵥ ξ)| ≤ Lam * ‖η‖ * ‖ξ‖)
    (hb_bound : ∀ᵐ x ∂μ, ‖b x‖ ≤ beta)
    (hc_bound : ∀ᵐ x ∂μ, ‖c x‖ ≤ gamma) :
    Integrable (fun x => energyIntegrand (a x) (b x) (c x) (U x) (V x)) μ :=
  integrable_energyIntegrand_apply₂_of_integrable_norm_mul hLam ha hb hc
    hU.aestronglyMeasurable hV.aestronglyMeasurable ha_bound hb_bound hc_bound
    (integrable_norm_mul_of_memLp_two hU hV)

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
  refine integrable_energyIntegrand_apply₂_of_integrable_norm_mul hLam ha hb hc hU hV ha_bound
    hb_bound hc_bound ?_
  refine Integrable.of_bound (hU.norm.mul hV.norm) (R * S) ?_
  filter_upwards [hU_bound, hV_bound] with x hUx hVx
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hR : 0 ≤ R := (norm_nonneg (U x)).trans hUx
  exact mul_le_mul hUx hVx (norm_nonneg (V x)) hR

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
