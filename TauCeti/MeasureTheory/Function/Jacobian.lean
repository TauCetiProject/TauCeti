/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Pushforward bounds from a lower bound on the Jacobian

Let `f` be injective and differentiable on a measurable subset `s` of a finite-dimensional real
normed space with an additive Haar measure `μ`. Mathlib's change of variables formula
`MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar` says that `f` pushes the measure
`|det f'| μ` on `s` forward to `μ` on `f '' s`. If the Jacobian is bounded below, `c ≤ |det f'|`
on `s` with `c > 0`, then `f` pushes `μ` on `s` forward to at most `c⁻¹ μ` on `f '' s`
(`MeasureTheory.map_restrict_le_smul_restrict_image`).

For `f` differentiable on an open set `s` and mapping it into `t`, the same bound holds with the
Fréchet derivative `fderiv ℝ f` as Jacobian and `μ` on `t` in place of `μ` on `f '' s`
(`MeasureTheory.map_restrict_le_smul_restrict_of_differentiableOn`).

Such a pushforward bound `μ.map f ≤ C • ν` gives the `eLpNorm` estimate for precomposition with
`f` (`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). For a change of variables no upper bound on
the Jacobian is needed, but a Jacobian that may vanish gives no such bound.

## Main declarations

* `MeasureTheory.map_restrict_le_smul_restrict_image`: the pushforward of `μ` on `s` is at most
  `c⁻¹ μ` on `f '' s`.
* `MeasureTheory.map_restrict_le_smul_restrict_of_differentiableOn`: the same for `f`
  differentiable on an open set `s` and mapping it into `t`, with `μ` on `t` as the target.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {s t : Set E} {f : E → E} {f' : E → E →L[ℝ] E} {c : ℝ}

/-- **Pushforward bound from a Jacobian lower bound.** If `f` is injective and differentiable on
a measurable set `s`, and `c ≤ |det f'|` on `s` with `c > 0`, then `f` pushes `μ` restricted to
`s` forward to at most `c⁻¹` times `μ` restricted to `f '' s`. -/
theorem map_restrict_le_smul_restrict_image (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(f' x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ.restrict (f '' s) := by
  classical
  -- Replace `f` by a measurable function `g` agreeing with it on `s`, so that `Measure.map_mono`
  -- applies.
  have hcont : ContinuousOn f s := fun x hx => (hf' x hx).differentiableWithinAt.continuousWithinAt
  set g : E → E := s.piecewise f 0
  have hg : Measurable g := hcont.measurable_piecewise continuous_zero.continuousOn hs
  have hfg : f =ᵐ[μ.restrict s] g :=
    (ae_restrict_mem hs).mono fun x hx => (piecewise_eq_of_mem s f 0 hx).symm
  -- Mathlib's change of variables: `f` pushes `|det f'| μ` on `s` forward to `μ` on `f '' s`.
  set W := (μ.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|
  have hW : W.map f = μ.restrict (f '' s) :=
    map_withDensity_abs_det_fderiv_eq_addHaar μ hs.nullMeasurableSet hf' hf
  rw [← hW, Measure.map_congr hfg,
    Measure.map_congr (hfg.filter_mono (withDensity_absolutelyContinuous _ _).ae_le),
    ← Measure.map_smul _ hg.aemeasurable]
  -- It remains to compare `μ` on `s` with `c⁻¹ |det f'| μ` on `s`.
  refine Measure.map_mono (Measure.le_iff.2 fun t ht => ?_) hg
  have hc0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ ht, ← ENNReal.mul_le_iff_le_inv hc0
    ENNReal.ofReal_ne_top, ← setLIntegral_const]
  exact lintegral_mono_ae ((ae_restrict_of_ae (ae_restrict_mem hs)).mono fun x hx =>
    ENNReal.ofReal_le_ofReal (hdet x hx))

/-- **Pushforward bound for a map differentiable on an open set.** If `f` is injective and
differentiable on an open set `s`, maps `s` into `t`, and `c ≤ |det (fderiv ℝ f x)|` on `s` with
`c > 0`, then `f` pushes `μ` restricted to `s` forward to at most `c⁻¹` times `μ` restricted to
`t`. -/
theorem map_restrict_le_smul_restrict_of_differentiableOn (hs : IsOpen s)
    (hf : DifferentiableOn ℝ f s) (hinj : InjOn f s) (hmaps : MapsTo f s t) (hc : 0 < c)
    (hdet : ∀ x ∈ s, c ≤ |(fderiv ℝ f x).det|) :
    (μ.restrict s).map f ≤ (ENNReal.ofReal c)⁻¹ • μ.restrict t :=
  (map_restrict_le_smul_restrict_image μ hs.measurableSet (fun x hx =>
    ((hf x hx).differentiableAt (hs.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt) hinj hc
      hdet).trans (by gcongr; exact hmaps.image_subset)

end MeasureTheory
