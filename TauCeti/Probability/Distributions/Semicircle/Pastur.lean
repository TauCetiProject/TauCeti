/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.ResolventTransform.Pastur.Basic
public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Map
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# The Pastur semigroup on semicircle laws and Ornstein–Uhlenbeck ergodicity

By Biane (1997), the Pastur measure evolution `ν ↦ ν.pastur t` corresponds to the additive free
convolution with the centred semicircle law `semicircleReal 0 t` of variance `t` (that
identification is not formalized here). At a point mass `δ_a`, the
Pastur self-consistent equation `w = (a - z - t w)⁻¹` rearranges to the semicircle quadratic
`t w² + (z - a) w + 1 = 0`, identifying `(Measure.dirac a).pastur t = semicircleReal a t`
(`TauCeti.Probability.pastur_dirac`). Combining this with the semigroup identity
`Measure.pastur_pastur` shows that the semicircle family is closed under the Pastur flow:
`(semicircleReal a s).pastur t = semicircleReal a (s + t)`
(`TauCeti.Probability.pastur_semicircleReal`).

Under the deterministic Ornstein–Uhlenbeck space-time change `x ↦ e^(-t/2) x` at variance time
`Real.toNNReal (e^t - 1)`, affine equivariance of the Pastur evolution yields
`((ν.pastur (Real.toNNReal (e^t - 1))).map (e^(-t/2) · ·)) =
  (ν.map (e^(-t/2) · ·)).pastur (Real.toNNReal (1 - e^(-t)))`
(`MeasureTheory.Measure.map_exp_neg_half_pastur`). Consequently:

* On any semicircle law `semicircleReal a v`, the Ornstein–Uhlenbeck action transports the centre
  to `e^(-t/2) a` and the variance to `e^(-t) v + Real.toNNReal (1 - e^(-t))`
  (`TauCeti.Probability.map_exp_neg_half_pastur_semicircleReal`).
* Starting from `δ_0`, the Ornstein–Uhlenbeck law at time `t` is
  `semicircleReal 0 (Real.toNNReal (1 - e^(-t)))`
  (`TauCeti.Probability.map_exp_neg_half_pastur_dirac_zero`).
* The standard semicircle law `semicircleReal 0 1` is invariant under the Ornstein–Uhlenbeck flow
  for `0 ≤ t` (`TauCeti.Probability.map_exp_neg_half_pastur_semicircleReal_zero_one`).
* For **every** initial probability measure `ν` on `ℝ` (with no moment assumptions), the
  Ornstein–Uhlenbeck flow converges weakly as `t → ∞` to `semicircleReal 0 1`
  (`MeasureTheory.ProbabilityMeasure.tendsto_map_exp_neg_half_pastur`), by joint weak continuity of
  `ProbabilityMeasure.pastur`.

## Main results

* `TauCeti.Probability.pastur_dirac`: `(Measure.dirac a).pastur t = semicircleReal a t`.
* `TauCeti.Probability.pastur_semicircleReal`:
  `(semicircleReal a s).pastur t = semicircleReal a (s + t)`.
* `MeasureTheory.Measure.map_exp_neg_half_pastur`: Ornstein–Uhlenbeck scaling of the Pastur flow.
* `TauCeti.Probability.map_exp_neg_half_pastur_semicircleReal` and
  `TauCeti.Probability.map_exp_neg_half_pastur_semicircleReal_zero_one`: Ornstein–Uhlenbeck action
  on semicircle laws and stationarity of `semicircleReal 0 1`.
* `MeasureTheory.ProbabilityMeasure.tendsto_map_exp_neg_half_pastur`: weak convergence of the
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

private lemma exp_neg_half_sq (t : ℝ) : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
  rw [sq, ← Real.exp_add]
  congr 1
  ring

private lemma map_exp_neg_half_eq_affine (μ : Measure ℝ) (t : ℝ) :
    μ.map (fun x : ℝ ↦ Real.exp (-t / 2) * x) =
      μ.map (fun x : ℝ ↦ 0 + Real.exp (-t / 2) * x) := by
  congr 1 with x
  ring

private lemma one_sub_exp_neg_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ 1 - Real.exp (-t) :=
  sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 ht))

/-- **Ornstein–Uhlenbeck scaling of the Pastur evolution.** Rescaling
`ν.pastur (Real.toNNReal (e^t - 1))` by `x ↦ e^(-t/2) x` equals the Pastur evolution at variance
`Real.toNNReal (1 - e^(-t))` started from the scaled initial measure `ν.map (x ↦ e^(-t/2) x)`. -/
theorem MeasureTheory.Measure.map_exp_neg_half_pastur (ν : Measure ℝ) (t : ℝ) :
    (ν.pastur (Real.toNNReal (Real.exp t - 1))).map (fun x : ℝ ↦ Real.exp (-t / 2) * x) =
      (ν.map (fun x : ℝ ↦ Real.exp (-t / 2) * x)).pastur (Real.toNNReal (1 - Real.exp (-t))) := by
  have htime : Real.toNNReal (Real.exp (-t / 2) ^ 2) * Real.toNNReal (Real.exp t - 1) =
      Real.toNNReal (1 - Real.exp (-t)) := by
    by_cases ht : 0 ≤ t
    · ext
      have ht1 : 0 ≤ Real.exp t - 1 := sub_nonneg.2 (Real.one_le_exp ht)
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _), Real.coe_toNNReal _ ht1,
        Real.coe_toNNReal _ (one_sub_exp_neg_nonneg ht), exp_neg_half_sq]
      have hexp : Real.exp (-t) * Real.exp t = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      linear_combination hexp
    · have ht' : t ≤ 0 := le_of_not_ge ht
      have ht1 : Real.exp t - 1 ≤ 0 := sub_nonpos.2 (Real.exp_le_one_iff.2 ht')
      have ht2 : 1 - Real.exp (-t) ≤ 0 :=
        sub_nonpos.2 (Real.one_le_exp (neg_nonneg.2 ht'))
      rw [Real.toNNReal_eq_zero.2 ht1, Real.toNNReal_eq_zero.2 ht2, mul_zero]
  rw [map_exp_neg_half_eq_affine, map_exp_neg_half_eq_affine ν, Measure.map_affine_pastur, htime]

namespace TauCeti.Probability

/-- **Pastur evolution from a point mass.** Evolving `Measure.dirac a` for variance time `t`
produces the semicircle law `semicircleReal a t` with centre `a` and variance `t`. -/
@[simp]
theorem pastur_dirac (a : ℝ) (t : ℝ≥0) :
    (Measure.dirac a).pastur t = semicircleReal a t := by
  symm
  refine Measure.eq_pastur_iff.2 fun z hz ↦ ?_
  obtain ⟨_, hq⟩ := (eq_resolventTransform_semicircleReal_iff (a := a) (v := t) hz).1 rfl
  have hprod : resolventTransform (semicircleReal a t) z *
      ((a : ℂ) - (z + (t : ℂ) * resolventTransform (semicircleReal a t) z)) = 1 := by
    linear_combination -hq
  rw [resolventTransform_dirac, Complex.resolvent_real_eq_inv]
  exact eq_inv_of_mul_eq_one_left hprod

/-- **Semicircle laws are closed under the Pastur semigroup.** -/
@[simp]
theorem pastur_semicircleReal (a : ℝ) (s t : ℝ≥0) :
    (semicircleReal a s).pastur t = semicircleReal a (s + t) := by
  rw [← pastur_dirac, Measure.pastur_pastur, pastur_dirac]

/-- **Ornstein–Uhlenbeck action on semicircle laws.** Evolving `semicircleReal a v` for variance
time `Real.toNNReal (e^t - 1)` and scaling by `x ↦ e^(-t/2) x` yields a semicircle law with centre
`e^(-t/2) a` and variance `e^(-t) v + Real.toNNReal (1 - e^(-t))`. -/
theorem map_exp_neg_half_pastur_semicircleReal (a : ℝ) (v : ℝ≥0) (t : ℝ) :
    ((semicircleReal a v).pastur (Real.toNNReal (Real.exp t - 1))).map
        (fun x : ℝ ↦ Real.exp (-t / 2) * x) =
      semicircleReal (Real.exp (-t / 2) * a)
        (Real.toNNReal (Real.exp (-t)) * v + Real.toNNReal (1 - Real.exp (-t))) := by
  rw [Measure.map_exp_neg_half_pastur, map_exp_neg_half_eq_affine, map_affine_semicircleReal,
    zero_add, exp_neg_half_sq, pastur_semicircleReal]

/-- Starting from `δ_0`, the Ornstein–Uhlenbeck measure at time `t` is the centred semicircle law
of variance `Real.toNNReal (1 - e^(-t))`. -/
theorem map_exp_neg_half_pastur_dirac_zero (t : ℝ) :
    ((Measure.dirac 0).pastur (Real.toNNReal (Real.exp t - 1))).map
        (fun x : ℝ ↦ Real.exp (-t / 2) * x) =
      semicircleReal 0 (Real.toNNReal (1 - Real.exp (-t))) := by
  simpa using map_exp_neg_half_pastur_semicircleReal 0 0 t

/-- **Stationarity of the standard semicircle law under the Ornstein–Uhlenbeck flow.** -/
theorem map_exp_neg_half_pastur_semicircleReal_zero_one {t : ℝ} (ht : 0 ≤ t) :
    ((semicircleReal 0 1).pastur (Real.toNNReal (Real.exp t - 1))).map
        (fun x : ℝ ↦ Real.exp (-t / 2) * x) =
      semicircleReal 0 1 := by
  rw [map_exp_neg_half_pastur_semicircleReal, mul_zero, mul_one]
  congr 1
  ext
  rw [NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal _ (Real.exp_nonneg _),
    Real.coe_toNNReal _ (one_sub_exp_neg_nonneg ht), add_sub_cancel]

end TauCeti.Probability

/-- **Ergodicity of the macroscopic Ornstein–Uhlenbeck flow.** For every initial probability
measure `ν` on `ℝ`, the rescaled Pastur evolution `(ν.pastur (e^t - 1)).map (x ↦ e^(-t/2) x)`
converges weakly as `t → ∞` to the standard semicircle law `semicircleReal 0 1`. -/
theorem MeasureTheory.ProbabilityMeasure.tendsto_map_exp_neg_half_pastur
    (ν : ProbabilityMeasure ℝ) :
    Tendsto (fun t : ℝ ↦ (ν.pastur (Real.toNNReal (Real.exp t - 1))).map
        (fun x : ℝ ↦ Real.exp (-t / 2) * x))
      atTop (𝓝 (TauCeti.Probability.semicircleReal 0 1).toProbabilityMeasure) := by
  open TauCeti.Probability in
  have hexp_half : Tendsto (fun t : ℝ ↦ Real.exp (-t / 2)) atTop (𝓝 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const zero_lt_two)).congr fun t ↦ by simp [neg_div]
  have hmap_zero : ν.map (fun x : ℝ ↦ (0 : ℝ) * x) = diracProba 0 :=
    ProbabilityMeasure.toMeasure_injective (by simp [diracProba, Measure.map_const])
  have hmap_lim : Tendsto (fun t : ℝ ↦ ν.map (fun x : ℝ ↦ Real.exp (-t / 2) * x))
      atTop (𝓝 (diracProba 0)) :=
    hmap_zero ▸ ((ProbabilityMeasure.continuous_map_of_continuous_uncurry
      (f := fun a x : ℝ ↦ a * x) continuous_mul).tendsto (0, ν)).comp
      (hexp_half.prodMk_nhds tendsto_const_nhds)
  have htime_lim : Tendsto (fun t : ℝ ↦ Real.toNNReal (1 - Real.exp (-t))) atTop (𝓝 1) := by
    have hsub : Tendsto (fun t : ℝ ↦ 1 - Real.exp (-t)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub Real.tendsto_exp_neg_atTop_nhds_zero
    have h1 : Real.toNNReal 1 = 1 := by simp
    exact h1 ▸ (continuous_real_toNNReal.tendsto 1).comp hsub
  have hlim : Tendsto (fun t : ℝ ↦
        (ν.map (fun x : ℝ ↦ Real.exp (-t / 2) * x)).pastur (Real.toNNReal (1 - Real.exp (-t))))
      atTop (𝓝 ((diracProba 0).pastur 1)) :=
    (ProbabilityMeasure.continuous_pastur.tendsto (diracProba 0, 1)).comp
      (hmap_lim.prodMk_nhds htime_lim)
  have htarget : (diracProba 0).pastur 1 =
      (TauCeti.Probability.semicircleReal 0 1).toProbabilityMeasure := by
    apply ProbabilityMeasure.toMeasure_injective
    rw [ProbabilityMeasure.toMeasure_pastur]
    simp [diracProba]
  rw [htarget] at hlim
  refine hlim.congr fun t ↦ ProbabilityMeasure.toMeasure_injective ?_
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pastur,
    ProbabilityMeasure.toMeasure_pastur, ProbabilityMeasure.toMeasure_map]
  exact (Measure.map_exp_neg_half_pastur (ν : Measure ℝ) t).symm

end
