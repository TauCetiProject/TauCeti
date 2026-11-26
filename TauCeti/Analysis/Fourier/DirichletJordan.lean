/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import TauCeti.Analysis.Fourier.SincKernel

import TauCeti.Analysis.Fourier.Inversion
import TauCeti.MeasureTheory.Integral.IntervalIntegral.BoundedVariation
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Dirichlet–Jordan Fourier inversion

Symmetric truncations of the inverse Fourier integral converge to the mean of the one-sided
limits at a point where the integrable source function is locally of bounded variation.
`MeasureTheory.Integrable.intervalIntegral_fourierInv_fourier_eq_integral_sinc` reduces the
proof to one-sided integrals. Near the origin, the variation estimate uses
`TauCeti.norm_intervalIntegral_sincKernel_le` and `TauCeti.tendsto_intervalIntegral_sincKernel`.
Away from the origin, `TauCeti.tendsto_setIntegral_sincKernel_smul_Ioi` gives convergence.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, §5.1.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal FourierTransform

namespace TauCeti

/-- One-sided Dirichlet–Jordan convergence at zero for an integrable function of locally bounded
variation. The limit is half the right limit of the function, by the one-sided argument in
Montgomery and Vaughan, *Multiplicative Number Theory I*, §5.1. -/
theorem tendsto_setIntegral_sincKernel_smul_Ioi_of_boundedVariationOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → E} {r : ℝ} (hr : 0 < r) (hf : IntegrableOn f (Ioi 0))
    (hv : BoundedVariationOn f (Ioc 0 r)) :
    Tendsto (fun T : ℝ ↦ ∫ x in Ioi 0, sincKernel T x • f x) atTop
      (𝓝 ((1 / 2 : ℝ) • f.rightLim 0)) := by
  have hl := hv.tendsto_rightLim_of_mem_nhdsGT
    (mem_of_superset (Ioo_mem_nhdsGT hr) Ioo_subset_Ioc_self)
  refine Metric.tendsto_nhds.2 (fun ε hε ↦ ?_)
  let C := 2 * Real.sineIntegral Real.pi / Real.pi
  have hC : 0 ≤ C := (norm_nonneg _).trans (norm_intervalIntegral_sincKernel_le 0 0 0)
  have hden : 0 < 3 * (C + 1) := by positivity
  have hη : 0 < ε / (3 * (C + 1)) := div_pos hε hden
  obtain ⟨d, hd, hsmall⟩ :=
    hv.exists_eVariationOn_Ioc_lt hr (ENNReal.ofReal_pos.mpr hη)
  have hdv : BoundedVariationOn f (Ioc 0 d) :=
    hv.mono (Ioc_subset_Ioc_right hd.2.le)
  have hnear (T : ℝ) :
      ‖∫ x in 0..d, sincKernel T x • (f x - f.rightLim 0)‖ < ε / 3 := by
    refine (hdv.norm_intervalIntegral_smul_sub_const_le_of_tendsto_nhdsGT hl hd.1.le
      ((continuous_sincKernel T).intervalIntegrable _ _)
      (fun c _ ↦ norm_intervalIntegral_sincKernel_le T c d)).trans_lt ?_
    have h := (ENNReal.toReal_lt_toReal hdv ENNReal.ofReal_ne_top).2 hsmall
    rw [ENNReal.toReal_ofReal hη.le, lt_div_iff₀ hden] at h
    nlinarith [ENNReal.toReal_nonneg (a := eVariationOn f (Ioc 0 d))]
  have hmass := ((tendsto_intervalIntegral_sincKernel hd.1).smul_const (f.rightLim 0)).eventually
    (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 3))
  have htail := (tendsto_setIntegral_sincKernel_smul_Ioi hd.1
    (hf.mono_set (Ioi_subset_Ioi hd.1.le))).eventually
      (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 3))
  filter_upwards [hmass, htail] with T hT hT'
  have hi : IntegrableOn (fun u ↦ sincKernel T u • f u) (Ioi 0) := hf.sincKernel_smul T
  have hw := (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.1.le).2
    (hi.mono_set Ioc_subset_Ioi_self)
  have hsplit :=
    intervalIntegral.integral_interval_add_Ioi hi (hi.mono_set (Ioi_subset_Ioi hd.1.le))
  simp only [dist_eq_norm, sub_zero] at hT hT'
  rw [dist_eq_norm, ← hsplit]
  have heq : (∫ x in 0..d, sincKernel T x • f x) -
      (∫ x in 0..d, sincKernel T x) • f.rightLim 0 =
        ∫ x in 0..d, sincKernel T x • (f x - f.rightLim 0) := by
    have hconst : IntervalIntegrable (fun x ↦ sincKernel T x • f.rightLim 0) volume 0 d :=
      ((continuous_sincKernel T).smul continuous_const).intervalIntegrable _ _
    rw [← intervalIntegral.integral_smul_const, ← intervalIntegral.integral_sub hw hconst]
    simp only [smul_sub]
  let A := ∫ x in 0..d, sincKernel T x • f x
  let B := (∫ x in 0..d, sincKernel T x) • f.rightLim 0
  let D := ∫ x in Ioi d, sincKernel T x • f x
  let L := (1 / 2 : ℝ) • f.rightLim 0
  have hsum : A + D - L = (A - B) + (B - L) + D := by abel
  have hnear' : ‖A - B‖ < ε / 3 := heq ▸ hnear T
  calc
    ‖A + D - L‖ ≤ ‖A - B‖ + ‖B - L‖ + ‖D‖ := by
      rw [hsum]
      exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ < ε := by linarith

end TauCeti

open TauCeti in
/-- **Dirichlet–Jordan inversion.** If an integrable function has bounded variation on a
neighbourhood of `x`, its symmetric inverse Fourier integrals converge to the mean of its
left and right limits at `x` (Montgomery and Vaughan, *Multiplicative Number Theory I*, §5.1). -/
theorem MeasureTheory.Integrable.tendsto_intervalIntegral_fourierInv_fourier_of_boundedVariationOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) {x r : ℝ} (hr : 0 < r)
    (hv : BoundedVariationOn f (Icc (x - r) (x + r))) :
    Tendsto (fun T : ℝ ↦ ∫ t in -T..T, 𝐞 (t * x) • 𝓕 f t) atTop
      (𝓝 ((1 / 2 : ℝ) • (f.leftLim x + f.rightLim x))) := by
  let left : ℝ → ℝ := fun u ↦ x - u
  let right : ℝ → ℝ := fun u ↦ x + u
  have hleft : BoundedVariationOn (f ∘ left) (Ioc 0 r) :=
    ne_top_of_le_ne_top hv
      (eVariationOn.comp_le_of_antitoneOn f left (by intro u _ v _ huv; dsimp [left]; linarith)
        (by intro u hu; dsimp [left]; grind))
  have hright : BoundedVariationOn (f ∘ right) (Ioc 0 r) :=
    ne_top_of_le_ne_top hv
      (eVariationOn.comp_le_of_monotoneOn f right (by intro u _ v _ huv; dsimp [right]; linarith)
        (by intro u hu; dsimp [right]; grind))
  have hmem : Icc (x - r) (x + r) ∈ 𝓝 x :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hl : Function.rightLim (f ∘ left) 0 = f.leftLim x := by
    have ha : StrictAnti left := fun _ _ huv ↦ sub_lt_sub_left huv x
    have hc : ContinuousAt left 0 := by fun_prop
    have hmap : Tendsto left (𝓝[>] 0) (𝓝[<] x) := by
      simpa only [left, sub_zero] using
        hc.continuousWithinAt.tendsto_nhdsWithin (ha.mapsTo_Ioi (a := 0))
    exact rightLim_eq_of_tendsto
      ((hv.tendsto_leftLim_of_mem_nhdsLT (mem_nhdsWithin_of_mem_nhds hmem)).comp hmap)
  have hrr : Function.rightLim (f ∘ right) 0 = f.rightLim x := by
    have hm : StrictMono right := fun _ _ huv ↦ add_lt_add_right huv x
    have hc : ContinuousAt right 0 := by fun_prop
    have hmap : Tendsto right (𝓝[>] 0) (𝓝[>] x) := by
      simpa only [right, add_zero] using
        hc.continuousWithinAt.tendsto_nhdsWithin (hm.mapsTo_Ioi (a := 0))
    exact rightLim_eq_of_tendsto
      ((hv.tendsto_rightLim_of_mem_nhdsGT (mem_nhdsWithin_of_mem_nhds hmem)).comp hmap)
  have hl' := tendsto_setIntegral_sincKernel_smul_Ioi_of_boundedVariationOn hr
    (hf.comp_sub_left x).integrableOn hleft
  have hr' := tendsto_setIntegral_sincKernel_smul_Ioi_of_boundedVariationOn hr
    (hf.comp_add_left x).integrableOn hright
  simp only [left, Function.comp_def] at hl
  simp only [right, Function.comp_def] at hrr
  rw [hl] at hl'
  rw [hrr] at hr'
  refine (by simpa only [smul_add] using hl'.add hr' :
    Tendsto (fun T : ℝ ↦ (∫ u in Ioi 0, sincKernel T u • f (x - u)) +
      ∫ u in Ioi 0, sincKernel T u • f (x + u)) atTop _).congr (fun T ↦ ?_)
  rw [hf.intervalIntegral_fourierInv_fourier_eq_integral_sinc]
  have hi : Integrable (fun u ↦ sincKernel T u • f (x - u)) :=
    (hf.comp_sub_left x).sincKernel_smul T
  have hs := integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hi
  have hneg := integral_comp_neg_Ioi 0 (fun u ↦ sincKernel T u • f (x - u))
  rw [neg_zero] at hneg
  rw [compl_Ioi, ← hneg] at hs
  simpa only [sincKernel_neg, sub_neg_eq_add] using hs
