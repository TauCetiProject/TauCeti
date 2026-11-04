/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.CompoundPoisson.Support
public import TauCeti.Probability.Distributions.Stable.Approximation.Basic
public import TauCeti.Topology.Instances.Real.AddSubmonoid

/-!
# Support of compensated compound-Poisson stable approximations

This file determines the topological support of the jump law and of the compensated
compound-Poisson approximation used to construct a non-Gaussian stable law. At full positive or
negative skewness, every retained jump has the corresponding sign. The compound-Poisson support
therefore consists of the no-jump atom together with a half-line separated from it by the cutoff.
At strict interior skewness, one positive and one negative retained jump can realize any real sum,
so the approximation has full support.

These exact finite-cutoff supports provide the finite-jump component of the large-jump/small-jump
decomposition used to identify the support of the limiting stable law.

## Main results

* `support_cond_stableLevyMeasure_one` and `support_cond_stableLevyMeasure_neg_one` identify the
  one-sided cutoff jump-law supports.
* `support_cond_stableLevyMeasure_of_abs_lt_one` identifies the two-sided cutoff jump-law support.
* `support_stableCompensatedPoissonMeasure_one` and
  `support_stableCompensatedPoissonMeasure_neg_one` identify the isolated no-jump atom and the
  translated half-line in the fully skewed cases.
* `support_stableCompensatedPoissonMeasure_of_abs_lt_one` proves full support at strict interior
  skewness.

## References

* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, §24.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Topology
open scoped ENNReal NNReal Pointwise

namespace TauCeti.Probability

/-- At full positive skewness, the normalized jumps above a positive cutoff have support
`[ε, ∞)`. -/
@[simp]
theorem support_cond_stableLevyMeasure_one {α ε : ℝ} (hα : α ∈ Ioo 0 2) (hε : 0 < ε) :
    (cond (stableLevyMeasure α 1) {x : ℝ | ε < |x|}).support = Ici ε := by
  let s : Set ℝ := {x | ε < |x|}
  have hs : MeasurableSet s := by measurability
  have htop : stableLevyMeasure α 1 s ≠ ∞ := stableLevyMeasure_abs_gt_ne_top hε
  rw [ProbabilityTheory.cond, Measure.support_smul_measure _ _ (ENNReal.inv_ne_zero.mpr htop),
    stableLevyMeasure_def, restrict_withDensity hs, ← withDensity_indicator hs]
  calc
    (volume.withDensity (s.indicator fun x ↦ ENNReal.ofReal (stableLevyDensity α 1 x))).support =
        closure (Ioi ε) := by
      apply Measure.support_withDensity_eq_closure_of_subset
      · exact (measurable_stableLevyDensity.comp
          (by fun_prop : Measurable (fun x : ℝ ↦ ((α, (1 : ℝ)), x)))).ennreal_ofReal.indicator hs
      · exact isOpen_Ioi
      · intro x hx
        rw [Function.mem_support, Set.indicator_of_mem]
        · rw [ENNReal.ofReal_ne_zero_iff]
          have hx0 : 0 < x := hε.trans hx
          rw [stableLevyDensity_of_ne_zero hα (by norm_num) (hε.trans hx).ne']
          simp only [ite_eq_left hx0, abs_of_pos hx0, one_add_one_eq_two]
          exact mul_pos (mul_pos (stableLevyDensity_coefficient_pos hα) (by norm_num))
            (rpow_pos_of_pos (hε.trans hx) _)
        · simp only [s, mem_ofPred_eq]
          rw [abs_of_pos (hε.trans hx)]
          exact hx
      · intro x hx
        rw [Function.mem_support] at hx
        by_cases hxs : x ∈ s
        · simp only [Set.indicator_of_mem hxs] at hx
          simp only [s, mem_ofPred_eq] at hxs
          have hxpos : ε < x := by
            rcases (lt_abs.mp hxs) with hpos | hneg
            · exact hpos
            · have hzero : stableLevyDensity α 1 x = 0 := by
                rw [stableLevyDensity_of_ne_zero hα (by norm_num) (by linarith)]
                simp [not_lt.mpr (le_of_lt (by linarith : x < 0))]
              exact (hx (by rw [hzero]; exact ENNReal.ofReal_zero)).elim
          simpa only [closure_Ioi, mem_Ici] using hxpos.le
        · simp [hxs] at hx
    _ = Ici ε := closure_Ioi ε

/-- At full negative skewness, the normalized jumps above a positive absolute cutoff have support
`(-∞, -ε]`. -/
@[simp]
theorem support_cond_stableLevyMeasure_neg_one {α ε : ℝ} (hα : α ∈ Ioo 0 2) (hε : 0 < ε) :
    (cond (stableLevyMeasure α (-1)) {x : ℝ | ε < |x|}).support = Iic (-ε) := by
  let s : Set ℝ := {x | ε < |x|}
  have hs : MeasurableSet s := by measurability
  have htop : stableLevyMeasure α (-1) s ≠ ∞ := stableLevyMeasure_abs_gt_ne_top hε
  rw [ProbabilityTheory.cond, Measure.support_smul_measure _ _ (ENNReal.inv_ne_zero.mpr htop),
    stableLevyMeasure_def, restrict_withDensity hs, ← withDensity_indicator hs]
  calc
    (volume.withDensity
        (s.indicator fun x ↦ ENNReal.ofReal (stableLevyDensity α (-1) x))).support =
      closure (Iio (-ε)) := by
      apply Measure.support_withDensity_eq_closure_of_subset
      · exact (measurable_stableLevyDensity.comp
          (by fun_prop : Measurable
            (fun x : ℝ ↦ ((α, (-1 : ℝ)), x)))).ennreal_ofReal.indicator hs
      · exact isOpen_Iio
      · intro x hx
        simp only [mem_Iio] at hx
        rw [Function.mem_support, Set.indicator_of_mem]
        · rw [ENNReal.ofReal_ne_zero_iff]
          have hx0 : x < 0 := hx.trans (neg_neg_of_pos hε)
          rw [stableLevyDensity_of_ne_zero hα (by norm_num) hx0.ne]
          simp only [ite_eq_right (not_lt.mpr hx0.le), sub_neg_eq_add, one_add_one_eq_two]
          exact mul_pos (mul_pos (stableLevyDensity_coefficient_pos hα) (by norm_num))
            (rpow_pos_of_pos (abs_pos.mpr hx0.ne) _)
        · simp only [s, mem_ofPred_eq]
          rw [abs_of_neg (hx.trans (neg_neg_of_pos hε))]
          simpa using (neg_lt_neg hx)
      · intro x hx
        rw [Function.mem_support] at hx
        by_cases hxs : x ∈ s
        · simp only [Set.indicator_of_mem hxs] at hx
          simp only [s, mem_ofPred_eq] at hxs
          have hxneg : x < -ε := by
            rcases (lt_abs.mp hxs) with hpos | hneg
            · have hzero : stableLevyDensity α (-1) x = 0 := by
                rw [stableLevyDensity_of_ne_zero hα (by norm_num) (by linarith)]
                simp [hε.trans hpos]
              exact (hx (by rw [hzero]; exact ENNReal.ofReal_zero)).elim
            · linarith
          simpa only [closure_Iio, mem_Iic] using hxneg.le
        · simp [hxs] at hx
    _ = Iic (-ε) := closure_Iio (-ε)

/-- At strict interior skewness, the normalized cutoff jump law has both closed tails as its
support. -/
@[simp]
theorem support_cond_stableLevyMeasure_of_abs_lt_one {α β ε : ℝ} (hα : α ∈ Ioo 0 2)
    (hβ : |β| < 1) (hε : 0 < ε) :
    (cond (stableLevyMeasure α β) {x : ℝ | ε < |x|}).support =
      Iic (-ε) ∪ Ici ε := by
  let s : Set ℝ := {x | ε < |x|}
  have hs : MeasurableSet s := by measurability
  have htop : stableLevyMeasure α β s ≠ ∞ := stableLevyMeasure_abs_gt_ne_top hε
  rw [ProbabilityTheory.cond, Measure.support_smul_measure _ _ (ENNReal.inv_ne_zero.mpr htop),
    stableLevyMeasure_def, restrict_withDensity hs, ← withDensity_indicator hs]
  have hs_open : IsOpen s := by
    exact isOpen_lt continuous_const continuous_abs
  have hsupp : Function.support
      (s.indicator fun x ↦ ENNReal.ofReal (stableLevyDensity α β x)) = s := by
    ext x
    constructor
    · intro hx
      rw [Function.mem_support] at hx
      by_contra hxs
      simp [hxs] at hx
    · intro hxs
      rw [Function.mem_support, Set.indicator_of_mem hxs, ENNReal.ofReal_ne_zero_iff]
      simp only [s, mem_ofPred_eq] at hxs
      have hx0 : x ≠ 0 := by
        intro hx
        subst x
        exact not_lt_of_ge hε.le (by simpa only [abs_zero] using hxs)
      rw [stableLevyDensity_of_ne_zero hα hβ.le hx0]
      have hb := abs_lt.mp hβ
      rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
      · simp only [ite_eq_right (not_lt.mpr hxneg.le)]
        exact mul_pos (mul_pos (stableLevyDensity_coefficient_pos hα) (by linarith))
          (rpow_pos_of_pos (abs_pos.mpr hx0) _)
      · simp only [ite_eq_left hxpos]
        exact mul_pos (mul_pos (stableLevyDensity_coefficient_pos hα) (by linarith))
          (rpow_pos_of_pos (abs_pos.mpr hx0) _)
  calc
    (volume.withDensity
        (s.indicator fun x ↦ ENNReal.ofReal (stableLevyDensity α β x))).support =
      closure s := Measure.support_withDensity_eq_closure
          ((measurable_stableLevyDensity.comp
            (by fun_prop : Measurable (fun x : ℝ ↦ ((α, β), x)))).ennreal_ofReal.indicator hs)
          hs_open hsupp
    _ = Iic (-ε) ∪ Ici ε := by
      have hs_eq : s = Iio (-ε) ∪ Ioi ε := by
        ext x
        simp only [s, mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, lt_abs, lt_neg, or_comm]
      rw [hs_eq, closure_union, closure_Iio, closure_Ioi]

/-- At full positive skewness, the compensated approximation has the translated no-jump atom and
then the translated right half-line of one-or-more-jump outcomes. -/
@[simp]
theorem support_stableCompensatedPoissonMeasure_one {α ε : ℝ} (hα : α ∈ Ioo 0 2)
    (hε : 0 < ε) :
    (stableCompensatedPoissonMeasure α 1 ε).support =
      {-∫ y in {y : ℝ | ε < |y|}, sin y ∂stableLevyMeasure α 1} ∪
        Ici (ε - ∫ y in {y : ℝ | ε < |y|}, sin y ∂stableLevyMeasure α 1) := by
  let ν := stableLevyMeasure α 1
  let s : Set ℝ := {x | ε < |x|}
  let c := ∫ y in s, sin y ∂ν
  have hr : (ν s).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.mpr
    ⟨(stableLevyMeasure_abs_gt_pos hα (by norm_num) hε).ne',
      stableLevyMeasure_abs_gt_ne_top hε⟩
  rw [stableCompensatedPoissonMeasure_def]
  -- The defining equation expands `ν`, `s`, and `c`; fold them back to the local names.
  change ((compoundPoissonMeasure (ν s).toNNReal (cond ν s)).map
    (fun x ↦ x - c)).support = {-c} ∪ Ici (ε - c)
  have hmap : (fun x : ℝ ↦ x - c) = fun x ↦ -c + 1 * x := by funext x; ring
  rw [hmap, support_map_affine (by norm_num), support_compoundPoissonMeasure hr,
    support_cond_stableLevyMeasure_one hα hε, closure_addSubmonoidClosure_Ici hε.le]
  rw [← hmap]
  let e : ℝ ≃o ℝ := OrderIso.subRight c
  have he : (fun x : ℝ ↦ x - c) = e := rfl
  rw [he, image_union, image_singleton, e.image_Ici]
  simp only [e, OrderIso.subRight_apply, zero_sub]

/-- At full negative skewness, the compensated approximation has the translated no-jump atom and
then the translated left half-line of one-or-more-jump outcomes. -/
@[simp]
theorem support_stableCompensatedPoissonMeasure_neg_one {α ε : ℝ} (hα : α ∈ Ioo 0 2)
    (hε : 0 < ε) :
    (stableCompensatedPoissonMeasure α (-1) ε).support =
      {-∫ y in {y : ℝ | ε < |y|}, sin y ∂stableLevyMeasure α (-1)} ∪
        Iic (-ε - ∫ y in {y : ℝ | ε < |y|}, sin y ∂stableLevyMeasure α (-1)) := by
  let ν := stableLevyMeasure α (-1)
  let s : Set ℝ := {x | ε < |x|}
  let c := ∫ y in s, sin y ∂ν
  have hr : (ν s).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.mpr
    ⟨(stableLevyMeasure_abs_gt_pos hα (by norm_num) hε).ne',
      stableLevyMeasure_abs_gt_ne_top hε⟩
  rw [stableCompensatedPoissonMeasure_def]
  -- The defining equation expands `ν`, `s`, and `c`; fold them back to the local names.
  change ((compoundPoissonMeasure (ν s).toNNReal (cond ν s)).map
    (fun x ↦ x - c)).support = {-c} ∪ Iic (-ε - c)
  have hmap : (fun x : ℝ ↦ x - c) = fun x ↦ -c + 1 * x := by funext x; ring
  rw [hmap, support_map_affine (by norm_num), support_compoundPoissonMeasure hr,
    support_cond_stableLevyMeasure_neg_one hα hε, closure_addSubmonoidClosure_Iic hε.le, ← hmap]
  let e : ℝ ≃o ℝ := OrderIso.subRight c
  have he : (fun x : ℝ ↦ x - c) = e := rfl
  rw [he, image_union, image_singleton, e.image_Iic]
  simp only [e, OrderIso.subRight_apply, zero_sub]

/-- At strict interior skewness, every compensated compound-Poisson approximation has full
topological support. -/
@[simp]
theorem support_stableCompensatedPoissonMeasure_of_abs_lt_one {α β ε : ℝ}
    (hα : α ∈ Ioo 0 2) (hβ : |β| < 1) (hε : 0 < ε) :
    (stableCompensatedPoissonMeasure α β ε).support = univ := by
  let ν := stableLevyMeasure α β
  let s : Set ℝ := {x | ε < |x|}
  let c := ∫ y in s, sin y ∂ν
  have hr : (ν s).toNNReal ≠ 0 := ENNReal.toNNReal_ne_zero.mpr
    ⟨(stableLevyMeasure_abs_gt_pos hα hβ.le hε).ne',
      stableLevyMeasure_abs_gt_ne_top hε⟩
  rw [stableCompensatedPoissonMeasure_def]
  -- The defining equation expands `ν`, `s`, and `c`; fold them back to the local names.
  change ((compoundPoissonMeasure (ν s).toNNReal (cond ν s)).map
    (fun x ↦ x - c)).support = univ
  have hmap : (fun x : ℝ ↦ x - c) = fun x ↦ -c + 1 * x := by funext x; ring
  rw [hmap, support_map_affine (by norm_num), support_compoundPoissonMeasure hr,
    support_cond_stableLevyMeasure_of_abs_lt_one hα hβ hε,
    closure_addSubmonoidClosure_twoSided, image_univ]
  ext y
  simp only [mem_range, mem_univ, iff_true]
  exact ⟨y + c, by ring⟩

end TauCeti.Probability
