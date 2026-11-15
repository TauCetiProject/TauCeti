/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Pastur.Basic
public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
import TauCeti.MeasureTheory.Measure.ResolventTransform.Inversion
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The Pastur semigroup on semicircle laws and Ornstein–Uhlenbeck ergodicity

The Pastur measure evolution `ν ↦ ν.pastur t` represents additive free convolution `ν ⊞ SC_t`
with the centred semicircle law `semicircleReal 0 t` of variance `t`. At a point mass `δ_a`, the
Pastur self-consistent equation `w = (a - z - t w)⁻¹` rearranges to the semicircle quadratic
`t w² + (z - a) w + 1 = 0`, identifying `(Measure.dirac a).pastur t = semicircleReal a t`
(`TauCeti.Probability.pastur_dirac`). Combining this with the semigroup identity
`Measure.pastur_pastur` shows that the semicircle family is closed under the Pastur flow:
`(semicircleReal a s).pastur t = semicircleReal a (s + t)`
(`TauCeti.Probability.pastur_semicircleReal`).

Under the deterministic Ornstein–Uhlenbeck space-time change `x ↦ e^(-t/2) x` at variance time
`e^t - 1` (`0 ≤ t`), affine equivariance of the Pastur evolution yields
`((ν.pastur (e^t - 1)).map (e^(-t/2) · ·)) = (ν.map (e^(-t/2) · ·)).pastur (1 - e^(-t))`
(`TauCeti.Probability.map_exp_neg_half_pastur`). Consequently:

* Starting from `δ_0`, the Ornstein–Uhlenbeck law at time `t ≥ 0` is
  `semicircleReal 0 (1 - e^(-t))` (`TauCeti.Probability.map_exp_neg_half_pastur_dirac_zero`).
* The standard semicircle law `semicircleReal 0 1` is invariant under the Ornstein–Uhlenbeck flow
  (`TauCeti.Probability.map_exp_neg_half_pastur_semicircleReal_zero_one`).
* For **every** initial probability measure `ν` on `ℝ` (with no moment assumptions), the
  Ornstein–Uhlenbeck flow converges weakly as `t → ∞` to `semicircleReal 0 1`
  (`TauCeti.Probability.tendsto_map_exp_neg_half_pastur`), by joint weak continuity of
  `ProbabilityMeasure.pastur`.

## Main results

* `TauCeti.Probability.pastur_dirac`: `(Measure.dirac a).pastur t = semicircleReal a t`.
* `TauCeti.Probability.pastur_semicircleReal`:
  `(semicircleReal a s).pastur t = semicircleReal a (s + t)`.
* `TauCeti.Probability.map_exp_neg_half_pastur`: Ornstein–Uhlenbeck scaling of the Pastur flow.
* `TauCeti.Probability.map_exp_neg_half_pastur_semicircleReal_zero_one`: stationarity of
  `semicircleReal 0 1`.
* `TauCeti.Probability.tendsto_map_exp_neg_half_pastur`: weak convergence of the
  Ornstein–Uhlenbeck flow to `semicircleReal 0 1` from an arbitrary initial probability measure.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §4.3.2 and Exercise 4.3.18.
* P. Biane, *On the free convolution with a semi-circular distribution*, Indiana Univ. Math. J.
  46 (1997), 705–718.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

/-- **Pastur evolution from a point mass.** Evolving `Measure.dirac a` for variance time `t`
produces the semicircle law `semicircleReal a t` with centre `a` and variance `t`. -/
@[simp]
theorem pastur_dirac (a : ℝ) (t : ℝ≥0) :
    (Measure.dirac a).pastur t = semicircleReal a t := by
  apply Measure.ext_of_resolventTransform fun z hz ↦ ?_
  let w := resolventTransform (semicircleReal a t) z
  obtain ⟨hw_im, hq⟩ := (eq_resolventTransform_semicircleReal_iff (a := a) (v := t) hz).1 rfl
  refine ((eq_resolventTransform_pastur_iff (ν := Measure.dirac a) t hz).2 ⟨hw_im.le, ?_⟩).symm
  have hprod : w * ((a : ℂ) - (z + (t : ℂ) * w)) = 1 := by linear_combination -hq
  rw [resolventTransform_dirac, resolvent, Ring.inverse_eq_inv']
  exact eq_inv_of_mul_eq_one_left hprod

/-- **Semicircle laws are closed under the Pastur semigroup.** -/
@[simp]
theorem pastur_semicircleReal (a : ℝ) (s t : ℝ≥0) :
    (semicircleReal a s).pastur t = semicircleReal a (s + t) := by
  rw [← pastur_dirac, Measure.pastur_pastur, pastur_dirac]

/-- **Ornstein–Uhlenbeck scaling of the Pastur evolution.** Rescaling `ν.pastur (e^t - 1)` by
`x ↦ e^(-t/2) x` for `0 ≤ t` equals the Pastur evolution at variance `1 - e^(-t)` started from
the contracted initial measure `ν.map (x ↦ e^(-t/2) x)`. -/
theorem map_exp_neg_half_pastur {ν : Measure ℝ} [IsFiniteMeasure ν] {t : ℝ} (ht : 0 ≤ t) :
    (ν.pastur (Real.toNNReal (Real.exp t - 1))).map (fun x : ℝ ↦ Real.exp (-t / 2) * x) =
      (ν.map (fun x : ℝ ↦ Real.exp (-t / 2) * x)).pastur (Real.toNNReal (1 - Real.exp (-t))) := by
  have hfun : (fun x : ℝ ↦ Real.exp (-t / 2) * x) = fun x : ℝ ↦ 0 + Real.exp (-t / 2) * x := by
    ext x; ring
  have htime : Real.toNNReal (Real.exp (-t / 2) ^ 2) * Real.toNNReal (Real.exp t - 1) =
      Real.toNNReal (1 - Real.exp (-t)) := by
    ext
    have ht1 : 0 ≤ Real.exp t - 1 := sub_nonneg.2 (Real.one_le_exp ht)
    have ht2 : 0 ≤ 1 - Real.exp (-t) :=
      sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 ht))
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ ht1,
      Real.coe_toNNReal _ ht2]
    have hsq : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hexp : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [hsq]
    linear_combination hexp
  rw [hfun, Measure.map_affine_pastur, htime]

/-- Starting from `δ_0`, the Ornstein–Uhlenbeck measure at time `t ≥ 0` is the centred semicircle
law of variance `1 - e^(-t)`. -/
theorem map_exp_neg_half_pastur_dirac_zero {t : ℝ} (ht : 0 ≤ t) :
    ((Measure.dirac 0).pastur (Real.toNNReal (Real.exp t - 1))).map
        (fun x : ℝ ↦ Real.exp (-t / 2) * x) =
      semicircleReal 0 (Real.toNNReal (1 - Real.exp (-t))) := by
  rw [map_exp_neg_half_pastur ht, Measure.map_dirac' (by fun_prop), mul_zero, pastur_dirac]

/-- **Stationarity of the standard semicircle law under the Ornstein–Uhlenbeck flow.** -/
theorem map_exp_neg_half_pastur_semicircleReal_zero_one {t : ℝ} (ht : 0 ≤ t) :
    ((semicircleReal 0 1).pastur (Real.toNNReal (Real.exp t - 1))).map
        (fun x : ℝ ↦ Real.exp (-t / 2) * x) =
      semicircleReal 0 1 := by
  rw [pastur_semicircleReal]
  have hfun : (fun x : ℝ ↦ Real.exp (-t / 2) * x) = fun x : ℝ ↦ 0 + Real.exp (-t / 2) * x := by
    ext x; ring
  rw [hfun, map_affine_semicircleReal]
  simp only [mul_zero, add_zero]
  congr 1
  ext
  have ht1 : 0 ≤ Real.exp t - 1 := sub_nonneg.2 (Real.one_le_exp ht)
  rw [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal _ (sq_nonneg _),
    Real.coe_toNNReal _ ht1]
  have hsq : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hsq]
  linear_combination hexp

/-- Contracting any probability measure `ν` on `ℝ` by `x ↦ e^(-t/2) x` converges weakly to `δ_0`
as `t → ∞`. -/
private lemma tendsto_map_exp_neg_half_dirac_zero (ν : ProbabilityMeasure ℝ)
    {δ₀ : ProbabilityMeasure ℝ} (hδ₀ : (δ₀ : Measure ℝ) = Measure.dirac 0) :
    Tendsto (fun t : ℝ ↦ ν.map (fun x : ℝ ↦ Real.exp (-t / 2) * x)) atTop (𝓝 δ₀) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_resolventTransform]
  intro z hz
  have hexp_half : Tendsto (fun t : ℝ ↦ Real.exp (-t / 2)) atTop (𝓝 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const zero_lt_two)).congr fun t ↦ by simp [neg_div]
  have hmap_eq (t : ℝ) :
      resolventTransform ((ν.map (fun x : ℝ ↦ Real.exp (-t / 2) * x) : ProbabilityMeasure ℝ) :
          Measure ℝ) z =
        ∫ x, resolvent z (Real.exp (-t / 2) * x) ∂(ν : Measure ℝ) := by
    rw [ProbabilityMeasure.toMeasure_map, resolventTransform_apply, integral_map (by fun_prop)
      (Complex.continuous_resolvent_real hz.ne').aestronglyMeasurable]
  have hdirac_eq :
      resolventTransform (δ₀ : Measure ℝ) z = ∫ _, resolvent z (0 : ℝ) ∂(ν : Measure ℝ) := by
    rw [hδ₀, resolventTransform_dirac, integral_const, probReal_univ, one_smul]
  simp_rw [hmap_eq, hdirac_eq]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ |z.im|⁻¹)
    (Eventually.of_forall fun t ↦
      ((Complex.continuous_resolvent_real hz.ne').comp (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun t ↦ ae_of_all _ fun x ↦
      Complex.norm_resolvent_real_le z _ hz.ne')
    (integrable_const _) (ae_of_all _ fun x ↦ ?_)
  have hmul : Tendsto (fun t : ℝ ↦ Real.exp (-t / 2) * x) atTop (𝓝 0) := by
    simpa using hexp_half.mul (tendsto_const_nhds (x := x))
  exact (Complex.continuous_resolvent_real hz.ne').tendsto 0 |>.comp hmul

/-- **Ergodicity of the macroscopic Ornstein–Uhlenbeck flow.** For every initial probability
measure `ν` on `ℝ`, the rescaled Pastur evolution `(ν.pastur (e^t - 1)).map (x ↦ e^(-t/2) x)`
converges weakly as `t → ∞` to the standard semicircle law `semicircleReal 0 1`. -/
theorem tendsto_map_exp_neg_half_pastur {ν : ProbabilityMeasure ℝ} :
    Tendsto (fun t : ℝ ↦ (ν.pastur (Real.toNNReal (Real.exp t - 1))).map
        (fun x : ℝ ↦ Real.exp (-t / 2) * x))
      atTop (𝓝 (⟨semicircleReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  let δ₀ : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩
  let σ : ProbabilityMeasure ℝ := ⟨semicircleReal 0 1, inferInstance⟩
  have hδ₀ : (δ₀ : Measure ℝ) = Measure.dirac 0 := ProbabilityMeasure.coe_mk _ _
  have hσ : (σ : Measure ℝ) = semicircleReal 0 1 := ProbabilityMeasure.coe_mk _ _
  have htime_lim : Tendsto (fun t : ℝ ↦ Real.toNNReal (1 - Real.exp (-t))) atTop (𝓝 1) := by
    have hsub : Tendsto (fun t : ℝ ↦ 1 - Real.exp (-t)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub Real.tendsto_exp_neg_atTop_nhds_zero
    have h1 : Real.toNNReal 1 = 1 := by simp
    rw [← h1]
    exact (continuous_real_toNNReal.tendsto 1).comp hsub
  have hlim : Tendsto (fun t : ℝ ↦
        (ν.map (fun x : ℝ ↦ Real.exp (-t / 2) * x)).pastur (Real.toNNReal (1 - Real.exp (-t))))
      atTop (𝓝 (δ₀.pastur 1)) :=
    (ProbabilityMeasure.continuous_pastur.tendsto (δ₀, 1)).comp
      ((tendsto_map_exp_neg_half_dirac_zero ν hδ₀).prodMk_nhds htime_lim)
  have htarget : δ₀.pastur 1 = σ := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_pastur, hδ₀, hσ, pastur_dirac]
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_pastur, ProbabilityMeasure.toMeasure_map,
    ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pastur]
  exact (map_exp_neg_half_pastur ht).symm

end TauCeti.Probability

end
