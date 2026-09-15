/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convex.Star
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import TauCeti.Analysis.Calculus.SegmentIncrement
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Integral.Dilation

/-!
# The potential estimate behind the Poincaré–Wirtinger inequality

This file proves the pointwise estimate that controls the oscillation of a `C¹` function about
its mean by a Riesz potential of its derivative. Let `Ω` be an open subset of a finite-dimensional
real normed space `E` of dimension `n`, star-convex about `x` and contained in `closedBall x D`,
let `μ` be an additive Haar measure, and let `u` be `C¹` on `Ω`. Then

`∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ ≤ D ^ n / n * ∫⁻ y in Ω, ‖Du y‖ₑ * ‖x - y‖ₑ ^ (1 - n) ∂μ`,

and consequently, for every `S ⊆ Ω` of positive measure,

`‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤ D ^ n / (n μ(S)) * ∫⁻ y in Ω, ‖Du y‖ₑ * ‖x - y‖ₑ ^ (1 - n) ∂μ`.

For a bounded convex open `Ω` and `x ∈ Ω` one may take `D = diam Ω`; this is
Gilbarg–Trudinger, Lemma 7.16. Integrating the right-hand side in `x` and bounding the Riesz
potential `y ↦ ‖x - y‖ ^ (1 - n)` in `Lᵖ` yields the Poincaré–Wirtinger inequality.

The statements use lower Lebesgue integrals, so no integrability of the derivative or of the
kernel is assumed.

## Main declarations

* `TauCeti.setLIntegral_closedBall_lintegral_segment_le`: integrating a function along the
  segments from `x` to the points of `closedBall x D` gives at most `D ^ n / n` times its Riesz
  potential at `x`.
* `TauCeti.setLIntegral_enorm_sub_le_of_starConvex`: the integrated oscillation bound.
* `TauCeti.enorm_sub_setAverage_le_of_starConvex`: the bound on the deviation from the mean over
  any subset of positive measure.
* `TauCeti.enorm_sub_setAverage_le_of_convex`: the form for convex sets with `D = diam Ω`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16. The argument here rests on the segment increment estimate
  `TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply` and the homothety change of variables
  `TauCeti.lintegral_comp_homothety` in place of the integration in polar coordinates used there.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Module
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω S : Set E} {x : E} {D : ℝ}

/-- **Averaging along segments produces the Riesz potential.** Integrating a function `g` along
the segments from `x` to the points `y` of `closedBall x D`, weighted by their lengths, gives at
most `D ^ n / n` times the Riesz potential `∫ w, g w * ‖x - w‖ ^ (1 - n)`, where `n` is the
dimension of the space. -/
theorem setLIntegral_closedBall_lintegral_segment_le {g : E → ℝ≥0∞}
    (hg : Measurable g) (x : E) (D : ℝ) :
    ∫⁻ y in closedBall x D, (∫⁻ t in Ioc (0 : ℝ) 1, g (x + t • (y - x))) * ‖x - y‖ₑ ∂μ ≤
      ENNReal.ofReal (D ^ finrank ℝ E / finrank ℝ E) *
        ∫⁻ w, g w * ‖x - w‖ₑ ^ (1 - (finrank ℝ E : ℝ)) ∂μ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have hzero : ∀ y : E, ‖x - y‖ₑ = 0 := fun y => by
      rw [Subsingleton.elim x y, sub_self, enorm_zero]
    simp [hzero]
  set n := finrank ℝ E
  have hn : 0 < n := finrank_pos
  -- The integrand as a function of the parameter `t` and of `y`.
  set K : ℝ → E → ℝ≥0∞ := fun t y =>
    g (x + t • (y - x)) * if ‖x - y‖ ≤ D then ENNReal.ofReal ‖x - y‖ else 0
  -- The same integrand after the substitution `w = x + t • (y - x)`.
  set L : ℝ → E → ℝ≥0∞ := fun t w => ENNReal.ofReal (t ^ (-(n : ℝ) - 1)) *
    (g w * if ‖x - w‖ ≤ t * D then ENNReal.ofReal ‖x - w‖ else 0) with hL_def
  have hKmeas : Measurable (Function.uncurry fun y t => K t y) := by
    refine (hg.comp (?_ : Measurable fun q : E × ℝ => x + q.2 • (q.1 - x))).mul
      (Measurable.ite (measurableSet_le (?_ : Measurable fun q : E × ℝ => ‖x - q.1‖)
        measurable_const) (?_ : Measurable fun q : E × ℝ => ENNReal.ofReal ‖x - q.1‖)
        measurable_const)
    all_goals fun_prop
  have hLmeas : Measurable (Function.uncurry fun w t => L t w) := by
    refine (?_ : Measurable fun q : E × ℝ => ENNReal.ofReal (q.2 ^ (-(n : ℝ) - 1))).mul
      ((hg.comp measurable_fst).mul (Measurable.ite
        (measurableSet_le (?_ : Measurable fun q : E × ℝ => ‖x - q.1‖)
          (?_ : Measurable fun q : E × ℝ => q.2 * D))
        (?_ : Measurable fun q : E × ℝ => ENNReal.ofReal ‖x - q.1‖) measurable_const))
    all_goals fun_prop
  have hK : ∀ y, (closedBall x D).indicator
      (fun y => (∫⁻ t in Ioc (0 : ℝ) 1, g (x + t • (y - x))) * ‖x - y‖ₑ) y =
        ∫⁻ t in Ioc (0 : ℝ) 1, K t y := by
    intro y
    by_cases hy : y ∈ closedBall x D
    · rw [indicator_of_mem hy, ← lintegral_mul_const' _ _ enorm_ne_top]
      simp only [K, ite_eq_left (mem_closedBall_iff_norm'.1 hy), ofReal_norm]
    · rw [indicator_of_notMem hy]
      simp [K, ite_eq_right (mt mem_closedBall_iff_norm'.2 hy)]
  -- Exchange the integrals over `y` and `t`, substitute `w = x + t • (y - x)` for each `t`,
  -- exchange back, and integrate out `t` for each `w`.
  calc
    _ = ∫⁻ y, (∫⁻ t in Ioc (0 : ℝ) 1, K t y) ∂μ :=
      (lintegral_indicator measurableSet_closedBall _).symm.trans (lintegral_congr hK)
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y, K t y ∂μ :=
      lintegral_lintegral_swap hKmeas.aemeasurable
    _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ w, L t w ∂μ := setLIntegral_congr_fun measurableSet_Ioc
      fun t ht => lintegral_comp_add_smul_sub_mul_ite μ g x D ht.1
    _ = ∫⁻ w, (∫⁻ t in Ioc (0 : ℝ) 1, L t w) ∂μ :=
      (lintegral_lintegral_swap hLmeas.aemeasurable).symm
    _ ≤ ∫⁻ w, ENNReal.ofReal (D ^ n / n) * (g w * ‖x - w‖ₑ ^ (1 - (n : ℝ))) ∂μ :=
      lintegral_mono fun w => by
        simpa only [hL_def, ofReal_norm] using
          setLIntegral_Ioc_rpow_mul_ite_le hn (g w) (norm_nonneg (x - w)) D
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **The integrated oscillation bound.** If `u` is `C¹` on an open set `Ω` which is star-convex
about `x` and contained in `closedBall x D`, then the integral over `Ω` of `‖u x - u y‖` is
bounded by `D ^ n / n` times the Riesz potential at `x` of the norm of the derivative of `u`,
where `n` is the dimension of the space. -/
theorem setLIntegral_enorm_sub_le_of_starConvex (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (hx : StarConvex ℝ x Ω) (hD : Ω ⊆ closedBall x D) :
    ∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ ≤
      ENNReal.ofReal (D ^ finrank ℝ E / finrank ℝ E) *
        ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ * ‖x - y‖ₑ ^ (1 - (finrank ℝ E : ℝ)) ∂μ := by
  classical
  -- The norm of the derivative, extended by zero off `Ω`.
  set g : E → ℝ≥0∞ := Ω.indicator fun w => ‖fderiv ℝ u w‖ₑ with hg_def
  have hcont := hu.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have hg : Measurable g := by
    rw [hg_def, ← piecewise_eq_indicator]
    exact hcont.enorm.measurable_piecewise continuousOn_const hΩ.measurableSet
  -- The segment estimate for `u` between `x` and a point `y` of `Ω`.
  have hseg : ∀ y ∈ Ω,
      ‖u x - u y‖ₑ ≤ (∫⁻ t in Ioc (0 : ℝ) 1, g (x + t • (y - x))) * ‖x - y‖ₑ := by
    intro y hy
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ Ω :=
      fun t ht => hx.add_smul_sub_mem hy ht.1 ht.2
    have h := enorm_sub_le_lintegral_enorm_fderiv_apply (u := u) x (y - x)
      (fun t ht => (hu.differentiableOn one_ne_zero _ (hmem t ht)).differentiableAt
        (hΩ.mem_nhds (hmem t ht)))
      ((hcont.comp (by fun_prop : Continuous fun t : ℝ => x + t • (y - x)).continuousOn
        hmem).clm_apply continuousOn_const)
    rw [add_sub_cancel, enorm_sub_rev] at h
    rw [← lintegral_mul_const' _ _ enorm_ne_top, setLIntegral_congr Ioc_ae_eq_Icc]
    refine h.trans (setLIntegral_mono' measurableSet_Icc fun t ht => ?_)
    simp only [g, indicator_of_mem (hmem t ht), enorm_sub_rev x y]
    exact ContinuousLinearMap.le_opENorm _ _
  calc
    ∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ ≤
        ∫⁻ y in Ω, (∫⁻ t in Ioc (0 : ℝ) 1, g (x + t • (y - x))) * ‖x - y‖ₑ ∂μ :=
      setLIntegral_mono' hΩ.measurableSet hseg
    _ ≤ ∫⁻ y in closedBall x D, (∫⁻ t in Ioc (0 : ℝ) 1, g (x + t • (y - x))) * ‖x - y‖ₑ ∂μ :=
      lintegral_mono_set hD
    _ ≤ _ := setLIntegral_closedBall_lintegral_segment_le hg x D
    _ = _ := by
      rw [← lintegral_indicator hΩ.measurableSet]
      simp only [g, indicator_mul_left]

/-- **The potential estimate for the mean.** If `u` is `C¹` on an open set `Ω` which is
star-convex about `x` and contained in `closedBall x D`, then for every `S ⊆ Ω` of positive
measure the deviation of `u x` from the mean of `u` over `S` is bounded by `D ^ n / (n μ(S))`
times the Riesz potential at `x` of the norm of the derivative of `u`, where `n` is the dimension
of the space. -/
theorem enorm_sub_setAverage_le_of_starConvex [CompleteSpace F] (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 1 u Ω) (hx : StarConvex ℝ x Ω) (hD : Ω ⊆ closedBall x D) (hS : S ⊆ Ω)
    (hS₀ : μ S ≠ 0) :
    ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤
      ENNReal.ofReal (D ^ finrank ℝ E / finrank ℝ E) / μ S *
        ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ * ‖x - y‖ₑ ^ (1 - (finrank ℝ E : ℝ)) ∂μ := by
  have hS_top : μ S ≠ ∞ := ((measure_mono (hS.trans hD)).trans_lt measure_closedBall_lt_top).ne
  have hcore := setLIntegral_enorm_sub_le_of_starConvex (μ := μ) hΩ hu hx hD
  rw [ENNReal.div_eq_inv_mul, mul_assoc]
  have hmeas : AEStronglyMeasurable (fun y => u x - u y) (μ.restrict S) :=
    (aestronglyMeasurable_const.sub ((hu.continuousOn.aestronglyMeasurable
      hΩ.measurableSet).mono_measure (Measure.restrict_mono hS le_rfl)))
  by_cases hint : ∫⁻ y in S, ‖u x - u y‖ₑ ∂μ = ∞
  · have htop : ∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ = ∞ := top_le_iff.1 (hint ▸ lintegral_mono_set hS)
    rw [htop, top_le_iff] at hcore
    rw [hcore, ENNReal.mul_top (ENNReal.inv_ne_zero.2 hS_top)]
    exact le_top
  have hdiff : IntegrableOn (fun y => u x - u y) S μ := ⟨hmeas, Ne.lt_top hint⟩
  have hu_int : IntegrableOn u S μ := by
    refine ((integrableOn_const (C := u x) hS_top).sub hdiff).congr (ae_of_all _ fun y => ?_)
    simp
  have hmean : u x - ⨍ y in S, u y ∂μ = ⨍ y in S, (u x - u y) ∂μ := by
    rw [setAverage_fun_sub (integrableOn_const (C := u x) hS_top) hu_int,
      setAverage_const hS₀ hS_top]
  calc
    ‖u x - ⨍ y in S, u y ∂μ‖ₑ = ‖(μ.real S)⁻¹ • ∫ y in S, (u x - u y) ∂μ‖ₑ := by
      rw [hmean, setAverage_eq]
    _ ≤ (μ S)⁻¹ * ∫⁻ y in S, ‖u x - u y‖ₑ ∂μ := by
      rw [enorm_smul]
      gcongr
      · rw [Real.enorm_of_nonneg (inv_nonneg.2 measureReal_nonneg), ENNReal.ofReal_inv_of_pos
          (by rw [measureReal_def]; exact ENNReal.toReal_pos hS₀ hS_top),
        ofReal_measureReal hS_top]
      · exact enorm_integral_le_lintegral_enorm _
    _ ≤ (μ S)⁻¹ * ∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ := by gcongr
    _ ≤ _ := by gcongr

/-- **Gilbarg–Trudinger, Lemma 7.16.** If `u` is `C¹` on a bounded convex open set `Ω` and
`x ∈ Ω`, then for every `S ⊆ Ω` of positive measure the deviation of `u x` from the mean of `u`
over `S` is bounded by `(diam Ω) ^ n / (n μ(S))` times the Riesz potential at `x` of the norm of
the derivative of `u`, where `n` is the dimension of the space. -/
theorem enorm_sub_setAverage_le_of_convex [CompleteSpace F] (hΩ : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 1 u Ω) (hx : x ∈ Ω) (hS : S ⊆ Ω)
    (hS₀ : μ S ≠ 0) :
    ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤
      ENNReal.ofReal (diam Ω ^ finrank ℝ E / finrank ℝ E) / μ S *
        ∫⁻ y in Ω, ‖fderiv ℝ u y‖ₑ * ‖x - y‖ₑ ^ (1 - (finrank ℝ E : ℝ)) ∂μ :=
  enorm_sub_setAverage_le_of_starConvex hΩ hu (hΩc.starConvex hx)
    (fun _ hy => mem_closedBall.2 (dist_le_diam_of_mem hb hy hx)) hS hS₀

end TauCeti
