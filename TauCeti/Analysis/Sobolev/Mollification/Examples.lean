/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic

import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Group.Integral
import TauCeti.Analysis.Normed.Group.Real
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Function.Sign

/-!
# Endpoint example: mollification of `|x|` on `ℝ`

The absolute value `x ↦ |x|` on `ℝ` illustrates the endpoint behaviour of Sobolev mollification:
its mollifications are smooth, agree identically with `|x|` for `|x| ≥ φ.rOut` by symmetry of
the bump, and have derivatives converging to `sign` in `Lᵖ(K)` for every `1 ≤ p < ∞` and compact
`K`, while any function continuous at `0` — in particular the derivative of any mollification —
stays at `L^∞(B(0, r))` distance at least `1` from `sign`.

## Main declarations

* `TauCeti.hasWeakFDerivOn_abs`: `|x|` has weak derivative `(SignType.sign x : ℝ) • id`.
* `TauCeti.normed_convolution_abs_eq_of_le_abs`: `(φ.normed volume ⋆ |·|) x = |x|`
  for `|x| ≥ φ.rOut`.
* `ContDiffBump.fderiv_normed_convolution_abs_apply`: derivative of `φ.normed volume ⋆ |·|`.
* `TauCeti.tendsto_eLpNorm_fderiv_normed_convolution_abs_sub`: `Lᵖ(K)` convergence to `sign`
  for `1 ≤ p < ∞`.
* `TauCeti.one_le_eLpNorm_top_sub_sign_of_continuousAt` and
  `TauCeti.one_le_eLpNorm_top_fderiv_normed_convolution_abs_sub`: `L^∞` convergence fails near `0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Chapter 5, §5.3.1.
-/

public section

noncomputable section

open ContinuousLinearMap Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution ENNReal Topology

namespace TauCeti

/-- The absolute value on `ℝ` has weak Fréchet derivative `x ↦ (SignType.sign x : ℝ) • id`. -/
theorem hasWeakFDerivOn_abs :
    HasWeakFDerivOn (volume : Measure ℝ) ⊤ (abs : ℝ → ℝ)
      fun x => (SignType.sign x : ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  have hlip : LocallyLipschitzOn (⊤ : Opens ℝ) (abs : ℝ → ℝ) :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun x y => by
      simpa [Real.dist_eq] using abs_abs_sub_abs_le x y).locallyLipschitz.locallyLipschitzOn
  refine hlip.hasWeakFDerivOn ?_
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by rw [ae_iff]; simp
  filter_upwards [hne] with x hx _
  exact (hasFDerivAt_id x).abs hx

/-- Away from the origin (`φ.rOut ≤ |x|`), convolving `|·|` with a normalized smooth bump centred
at `0` reproduces `|x|` identically, because the bump is symmetric and `|·|` is affine on each
half-line. -/
theorem normed_convolution_abs_eq_of_le_abs {φ : ContDiffBump (0 : ℝ)} {x : ℝ}
    (hx : φ.rOut ≤ |x|) :
    (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) x = |x| := by
  have hodd : ∫ y : ℝ, φ.normed volume y * y ∂volume = 0 := by
    have hneg := integral_neg_eq_self (fun y : ℝ => φ.normed volume y * y) (volume : Measure ℝ)
    simp only [φ.normed_neg, mul_neg, integral_neg] at hneg
    linarith
  have hint_id : Integrable (fun y : ℝ => φ.normed volume y * y) volume :=
    (φ.continuous_normed.mul continuous_id).integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed.mul_right
  have hint_const : Integrable (fun y : ℝ => φ.normed volume y * x) volume :=
    φ.integrable_normed.mul_const x
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx ⊢
    have hcongr : ∀ y : ℝ, φ.normed volume y * |x - y| =
        φ.normed volume y * x - φ.normed volume y * y := fun y => by
      by_cases hy : y ∈ ball (0 : ℝ) φ.rOut
      · rw [mem_ball_zero_iff, Real.norm_eq_abs] at hy
        rw [abs_of_nonneg (by linarith [(abs_le.1 hy.le).2]), mul_sub]
      · rw [← φ.support_normed_eq (μ := volume), Function.notMem_support] at hy
        simp [hy]
    simp only [convolution_def, lsmul_apply, smul_eq_mul, hcongr]
    rw [integral_sub hint_const hint_id, integral_mul_const, φ.integral_normed, one_mul, hodd,
      sub_zero]
  · rw [abs_of_neg hx0] at hx ⊢
    have hcongr : ∀ y : ℝ, φ.normed volume y * |x - y| =
        φ.normed volume y * y - φ.normed volume y * x := fun y => by
      by_cases hy : y ∈ ball (0 : ℝ) φ.rOut
      · rw [mem_ball_zero_iff, Real.norm_eq_abs] at hy
        rw [abs_of_nonpos (by linarith [(abs_le.1 hy.le).1])]
        ring
      · rw [← φ.support_normed_eq (μ := volume), Function.notMem_support] at hy
        simp [hy]
    simp only [convolution_def, lsmul_apply, smul_eq_mul, hcongr]
    rw [integral_sub hint_id hint_const, hodd, integral_mul_const, φ.integral_normed, one_mul,
      zero_sub]

/-- The derivative of `φ.normed volume ⋆ |·|` is `φ.normed volume ⋆ sign`. -/
theorem _root_.ContDiffBump.fderiv_normed_convolution_abs_apply (φ : ContDiffBump (0 : ℝ))
    (x : ℝ) :
    fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) x 1 =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] fun y : ℝ => (SignType.sign y : ℝ)) x := by
  have hDu_loc : LocallyIntegrable
      (fun y : ℝ => (SignType.sign y : ℝ) • ContinuousLinearMap.id ℝ ℝ) volume :=
    (memLp_top_of_bound (f := fun y : ℝ => (SignType.sign y : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      (measurable_coe_sign.aestronglyMeasurable.smul aestronglyMeasurable_const) 1
      (.of_forall fun y => by
        rw [norm_smul, ContinuousLinearMap.norm_id, mul_one]
        exact SignType.norm_coe_le_one (SignType.sign y))).locallyIntegrable le_top
  have h := hasWeakFDerivOn_abs.fderiv_convolution_right continuous_abs.locallyIntegrable hDu_loc
    (φ.normed volume) φ.contDiff_normed φ.hasCompactSupport_normed x (fun _ _ => trivial)
  rw [convolution_flip, convolution_flip] at h
  rw [h]
  have hint : Integrable (fun t : ℝ => φ.normed volume t •
      ((SignType.sign (x - t) : ℝ) • ContinuousLinearMap.id ℝ ℝ)) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) φ.continuous_normed hDu_loc x
  simp only [convolution_def, lsmul_apply]
  rw [ContinuousLinearMap.integral_apply hint]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]

/-- On every compact set `K ⊆ ℝ` and for every `1 ≤ p < ∞`, the derivatives of the mollifications
of `|·|` converge to `sign` in `Lᵖ(K)`. -/
theorem tendsto_eLpNorm_fderiv_normed_convolution_abs_sub {K : Set ℝ} (hK : IsCompact K)
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ (∞ : ℝ≥0∞)) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm
      (fun x => fderiv ℝ ((φ i).normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) x 1 -
        (SignType.sign x : ℝ)) p (volume.restrict K)) l (𝓝 0) := by
  have : Fact (1 ≤ p) := ⟨hp1⟩
  have hmem : MemLp (fun y : ℝ => (SignType.sign y : ℝ)) p
      (volume.restrict (thickening 1 K)) := by
    have : IsFiniteMeasure (volume.restrict (thickening 1 K)) :=
      isFiniteMeasure_restrict.2
        ((measure_mono (thickening_subset_cthickening 1 K)).trans_lt
          hK.cthickening.measure_lt_top).ne
    exact (memLp_top_of_bound measurable_coe_sign.aestronglyMeasurable 1
      (.of_forall fun y => SignType.norm_coe_le_one (SignType.sign y))).mono_exponent le_top
  refine (tendsto_eLpNorm_normed_convolution_sub_restrict hp hφ one_pos hmem).congr fun i => ?_
  congr 1
  ext x
  rw [(φ i).fderiv_normed_convolution_abs_apply x, Pi.sub_apply]

/-- Any real function continuous at `0` stays at `L^∞(B(0, r))` distance at least `1` from `sign`
for every `r > 0`. -/
theorem one_le_eLpNorm_top_sub_sign_of_continuousAt {g : ℝ → ℝ} (hg : ContinuousAt g 0)
    {r : ℝ} (hr : 0 < r) :
    1 ≤ eLpNorm (fun x : ℝ => g x - (SignType.sign x : ℝ)) ∞ (volume.restrict (ball 0 r)) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε0 : 0 < (ε : ℝ) := NNReal.coe_pos.2 hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hg (ε : ℝ) hε0
  set η := min δ r
  have hη : 0 < η := lt_min hδ hr
  set c : ℝ≥0∞ := eLpNorm (fun x => g x - (SignType.sign x : ℝ)) ∞ (volume.restrict (ball 0 r))
  have hae : ∀ᵐ x ∂volume.restrict (ball (0 : ℝ) r), ‖g x - (SignType.sign x : ℝ)‖ₑ ≤ c :=
    ae_le_eLpNormEssSup.mono fun x hx => hx.trans eLpNormEssSup_le_eLpNorm_top
  have hstep {a b s : ℝ} (hab : a < b) (hsub : Ioo a b ⊆ ball (0 : ℝ) r)
      (hsign : ∀ x ∈ Ioo a b, (SignType.sign x : ℝ) = s)
      (hclose : ∀ x ∈ Ioo a b, |g x - g 0| < ε) (hgap : (1 : ℝ) ≤ |g 0 - s|) :
      (1 : ℝ≥0∞) ≤ c + ε := by
    have hpos : volume (Ioo a b) ≠ 0 := by simp [Real.volume_Ioo, hab]
    obtain ⟨x, hxIoo, hxc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
      (ae_restrict_of_ae_restrict_of_subset hsub hae)
    have h1 : (1 : ℝ) ≤ |g x - (SignType.sign x : ℝ)| + ε := by
      have htri : |g 0 - s| ≤ |g 0 - g x| + |g x - s| := abs_sub_le _ _ _
      rw [abs_sub_comm (g 0) (g x)] at htri
      rw [hsign x hxIoo]
      linarith [hclose x hxIoo]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal (|g x - (SignType.sign x : ℝ)| + ε) := ENNReal.ofReal_le_ofReal h1
      _ = ‖g x - (SignType.sign x : ℝ)‖ₑ + ε := by
          rw [ENNReal.ofReal_add (abs_nonneg _) hε0.le, ← Real.norm_eq_abs, ofReal_norm,
            ENNReal.ofReal_coe_nnreal]
      _ ≤ c + ε := by gcongr
  rcases le_or_gt (g 0) 0 with hg0 | hg0
  · refine hstep hη (fun x hx => by
        rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos hx.1]
        exact hx.2.trans_le (min_le_right _ _))
      (fun x hx => by rw [sign_pos hx.1, SignType.coe_one])
      (fun x hx => hδg <| by
        rw [Real.dist_eq, sub_zero, abs_of_pos hx.1]
        exact hx.2.trans_le (min_le_left _ _))
      (by linarith [neg_le_abs (g 0 - 1)])
  · refine hstep (neg_lt_zero.2 hη) (fun x hx => by
        rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_neg hx.2]
        linarith [hx.1, min_le_right δ r])
      (fun x hx => by rw [sign_neg hx.2, SignType.coe_neg, SignType.coe_one])
      (fun x hx => hδg <| by
        rw [Real.dist_eq, sub_zero, abs_of_neg hx.2]
        linarith [hx.1, min_le_left δ r])
      (by linarith [le_abs_self (g 0 - (-1))])

/-- The derivatives of the mollifications of `|·|` do not converge to `sign` in `L^∞` near `0`:
they stay at `L^∞(B(0, r))` distance at least `1` from `sign` for every `r > 0`. -/
theorem one_le_eLpNorm_top_fderiv_normed_convolution_abs_sub {r : ℝ} (hr : 0 < r)
    (φ : ContDiffBump (0 : ℝ)) :
    1 ≤ eLpNorm (fun x : ℝ => fderiv ℝ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) x 1 -
      (SignType.sign x : ℝ)) ∞ (volume.restrict (ball 0 r)) := by
  have hsm : ContDiff ℝ ∞ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] (abs : ℝ → ℝ)) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
      continuous_abs.locallyIntegrable
  exact one_le_eLpNorm_top_sub_sign_of_continuousAt
    ((hsm.continuous_fderiv (by simp)).clm_apply continuous_const).continuousAt hr

end TauCeti

end
