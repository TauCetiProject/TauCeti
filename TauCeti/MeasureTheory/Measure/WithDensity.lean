/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Pushing a weighted measure forward

A weight travels with the measure it weights: along a measurable equivalence `e`, the image of
`μ.withDensity f` is the image of `μ` weighted by `f ∘ e.symm`. Mathlib has this only for the
special case of a Radon–Nikodym derivative, in
`MeasurableEmbedding.map_withDensity_rnDeriv`.

Combined with a rescaling law for the measure itself, such as
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` on a finite-dimensional real normed
space, this gives the change-of-variables formula for a density under an invertible affine map.
That is the shape a location–scale family needs: it turns a density for the standard member of the
family into a density for every other member.

A map that is injective only on part of the line admits the same change of variables there, at the
price of restricting Lebesgue measure to that part and inserting the absolute derivative into the
weight. The substitution `x = t ^ 2` on the positive half-line is the case a square-root law needs.

## Main statements

* `MeasurableEquiv.map_withDensity`: the image of a weighted measure along a measurable
  equivalence is the image measure weighted by the transported weight.
* `MeasureTheory.Measure.map_affine_withDensity`: the image of a weighted Haar measure under an
  invertible affine map is that Haar measure weighted by the substituted density, rescaled by the
  constant Jacobian factor.
* `TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul`: the change of variables on the real line
  along a map injective and differentiable on a measurable set.
* `TauCeti.MeasureTheory.map_sq_withDensity_restrict_Ioi`: its instance for squaring on the
  positive half-line.
-/
public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace MeasurableEquiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **A weight travels with the measure it weights.** Pushing `μ.withDensity f` forward along a
measurable equivalence `e` gives the pushforward of `μ` weighted by `f ∘ e.symm`. The weight `f`
is arbitrary; no measurability of it is required. -/
theorem map_withDensity (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity fun y => f (e.symm y) := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), Measure.restrict_map e.measurable hs,
    lintegral_map_equiv]
  simp only [MeasurableEquiv.symm_apply_apply]

end MeasurableEquiv

namespace MeasureTheory.Measure

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
    rw [← A.coe_toHomeomorph, ← Homeomorph.toMeasurableEquiv_coe, MeasurableEquiv.map_withDensity]
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
        rw [← MeasurableEquiv.coe_addLeft c, MeasurableEquiv.map_withDensity]
        simp only [MeasurableEquiv.coe_addLeft, MeasurableEquiv.symm_addLeft,
          map_add_left_eq_self, neg_add_eq_sub]

end MeasureTheory.Measure

namespace TauCeti.MeasureTheory

open Set

variable {s : Set ℝ} {φ φ' : ℝ → ℝ} {f : ℝ → ℝ≥0∞}

/-- **Change of variables for a weighted Lebesgue measure on the real line.** If `φ` is injective
and differentiable on a measurable set `s`, then weighting Lebesgue measure on `s` by
`|φ' t| * f (φ t)` and pushing forward along `φ` gives Lebesgue measure on the image `φ '' s`
weighted by `f`.

This is the measure-level form of Mathlib's
`MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul`, and it carries a weight where
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` has none: that theorem is the case
`f = 1`. Unlike
`MeasurableEquiv.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul`, it does not ask
`φ` to be injective off `s`, which is what a substitution on a half-line needs. The weight `f` is
arbitrary; no measurability of it is required. -/
theorem map_withDensity_abs_deriv_mul (hs : MeasurableSet s) (hφ : Measurable φ)
    (hφ' : ∀ x ∈ s, HasDerivWithinAt φ (φ' x) s x) (hinj : InjOn φ s) :
    ((volume.restrict s).withDensity fun t ↦ ENNReal.ofReal |φ' t| * f (φ t)).map φ =
      (volume.restrict (φ '' s)).withDensity f := by
  ext A hA
  rw [Measure.map_apply hφ hA, withDensity_apply _ (hφ hA), withDensity_apply _ hA,
    Measure.restrict_restrict (hφ hA), Measure.restrict_restrict hA]
  have himage : φ '' (φ ⁻¹' A ∩ s) = A ∩ φ '' s := by
    rw [inter_comm, image_inter_preimage, inter_comm]
  rw [← himage, lintegral_image_eq_lintegral_abs_deriv_mul ((hφ hA).inter hs)
    (fun x hx ↦ (hφ' x hx.2).mono inter_subset_right) (hinj.mono inter_subset_right)]

/-- **The substitution `x = t ^ 2` on the positive half-line.** Weighting Lebesgue measure on
`Ioi 0` by `2 * t * f (t ^ 2)` and pushing forward along squaring gives Lebesgue measure on
`Ioi 0` weighted by `f`. -/
theorem map_sq_withDensity_restrict_Ioi (f : ℝ → ℝ≥0∞) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦
        ENNReal.ofReal (2 * t) * f (t ^ 2)).map (fun t ↦ t ^ 2) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity f := by
  have himage : (fun t : ℝ ↦ t ^ 2) '' Ioi 0 = Ioi 0 := by
    ext x
    refine ⟨fun ⟨t, ht, htx⟩ ↦ htx ▸ mem_Ioi.mpr (pow_pos ht 2),
      fun hx ↦ ⟨√x, Real.sqrt_pos.mpr hx, ?_⟩⟩
    simpa using Real.sq_sqrt (mem_Ioi.mp hx).le
  have hinj : InjOn (fun t : ℝ ↦ t ^ 2) (Ioi 0) :=
    (pow_left_strictMonoOn₀ two_ne_zero).injOn.mono fun t ht ↦ le_of_lt ht
  have hweight : (fun t : ℝ ↦ ENNReal.ofReal (2 * t) * f (t ^ 2)) =ᵐ[volume.restrict (Ioi 0)]
      fun t ↦ ENNReal.ofReal |2 * t| * f (t ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [abs_of_pos (by simpa using ht : (0 : ℝ) < 2 * t)]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ ↦ u ^ 2) (2 * t) t := fun t ↦ by
    simpa using hasDerivAt_pow 2 t
  rw [withDensity_congr_ae hweight, map_withDensity_abs_deriv_mul measurableSet_Ioi (by fun_prop)
    (fun t _ ↦ (hderiv t).hasDerivWithinAt) hinj, himage]

end TauCeti.MeasureTheory
