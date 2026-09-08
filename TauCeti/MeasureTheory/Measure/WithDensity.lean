/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Pushing a weighted measure forward

A weight travels with the measure it weights: along a measurable equivalence `e`, the image of
`μ.withDensity f` is the image of `μ` weighted by `f ∘ e.symm`. Mathlib has this only for the
special case of a Radon–Nikodym derivative, in
`MeasurableEmbedding.map_withDensity_rnDeriv`.

On a finite-dimensional real normed space carrying an additive Haar measure, an invertible affine
map rescales the measure itself by the constant `|det A|⁻¹`
(`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`), so the two facts combine into the
classical change-of-variables formula for a density under an affine substitution. That is the
shape a location–scale family needs: it turns a density for the standard member of the family
into a density for every other member.

## Main statements

* `TauCeti.map_withDensity_equiv`: the image of a weighted measure along a measurable
  equivalence is the image measure weighted by the transported weight.
* `TauCeti.map_affine_withDensity`: the image of a weighted Haar measure under an invertible
  affine map is that Haar measure weighted by the substituted density, rescaled by the constant
  Jacobian factor.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **A weight travels with the measure it weights.** Pushing `μ.withDensity f` forward along a
measurable equivalence `e` gives the pushforward of `μ` weighted by `f ∘ e.symm`.

No measurability of `f` is needed: on a measurable set both sides unfold to the lower integral of
`f` over the preimage, and `MeasureTheory.lintegral_map_equiv` transports that integral along `e`
with no hypothesis on the integrand. -/
theorem map_withDensity_equiv (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity fun y => f (e.symm y) := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), Measure.restrict_map e.measurable hs,
    lintegral_map_equiv]
  simp only [MeasurableEquiv.symm_apply_apply]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

/-- **Change of variables for a density under an invertible affine map.** The image of
`μ.withDensity g` under `x ↦ c + A x` is `μ` weighted by the substituted density
`y ↦ g (A⁻¹ (y - c))`, scaled by the constant Jacobian factor `|det A|⁻¹`. -/
theorem map_affine_withDensity (μ : Measure E) [μ.IsAddHaarMeasure] (A : E ≃L[ℝ] E) (c : E)
    (g : E → ℝ≥0∞) :
    (μ.withDensity g).map (fun x => c + A x) =
      μ.withDensity fun y =>
        ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| * g (A.symm (y - c)) := by
  set r : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det (A : E →ₗ[ℝ] E))⁻¹| with hr
  have hdet : LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 := ((A : E ≃ₗ[ℝ] E).isUnit_det').ne_zero
  have hmapA : μ.map A = r • μ := by
    rw [hr]
    simpa using Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
  -- the linear part rescales the measure by the Jacobian, and substitutes `A⁻¹` in the density
  have hlin : (μ.withDensity g).map A = μ.withDensity fun y => r * g (A.symm y) := by
    rw [← A.coe_toHomeomorph, ← Homeomorph.toMeasurableEquiv_coe, map_withDensity_equiv]
    simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.toMeasurableEquiv_symm_coe,
      ContinuousLinearEquiv.coe_toHomeomorph, ContinuousLinearEquiv.coe_symm_toHomeomorph]
    rw [hmapA, withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    exact congrArg μ.withDensity (funext fun y => by simp only [Pi.smul_apply, smul_eq_mul, hr])
  -- the translation leaves the Haar measure alone, and substitutes `· - c` in the density
  calc (μ.withDensity g).map (fun x => c + A x)
      = ((μ.withDensity g).map A).map (fun y : E => c + y) :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = (μ.withDensity fun y => r * g (A.symm y)).map (fun y : E => c + y) := by rw [hlin]
    _ = μ.withDensity fun y => r * g (A.symm (y - c)) := by
        rw [← MeasurableEquiv.coe_addLeft c, map_withDensity_equiv]
        simp only [MeasurableEquiv.coe_addLeft, MeasurableEquiv.symm_addLeft,
          map_add_left_eq_self, neg_add_eq_sub]

end TauCeti
