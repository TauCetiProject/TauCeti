/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.MeasureTheory.Group.Measure
public import TauCeti.Probability.Quantile

/-!
# Quantiles of pushforwards along monotone maps

If `X` has law `μ` and `g : ℝ → ℝ` is continuous and nondecreasing, the quantile function of
`g X` is `g` composed with the quantile function of `X`: at every level `t` strictly between `0`
and `1`,

`(μ.map g).quantile t = g (μ.quantile t)`,

and the same holds for the upper quantile. Strict monotonicity is not needed: a flat piece of `g`
merges values without changing which point is the `t`-quantile.

A nonincreasing map reverses the order of levels and exchanges the two quantiles. Negation is the
basic case, `μ.neg.quantile t = -μ.upperQuantile (1 - t)`, and composing with it gives
`(μ.map g).quantile t = g (μ.upperQuantile (1 - t))` for continuous nonincreasing `g`. The upper
quantile cannot be replaced by the lower one when the cumulative distribution function of `μ` has
a plateau at level `1 - t`.

Maps such as the logarithm or the reciprocal are monotone and continuous only on part of the line.
The general statements therefore only ask for the hypotheses on an interval `s` carrying all the
mass of `μ`. Every quantile at a level strictly between `0` and `1` lies in such an interval
(`Set.OrdConnected.quantile_mem`), so the hypotheses on `s` apply at the quantile.

## Main statements

* `Set.OrdConnected.quantile_mem`, `Set.OrdConnected.upperQuantile_mem` — interior quantiles lie
  in every interval of full mass;
* `MeasureTheory.Measure.quantile_map_of_monotoneOn`,
  `MeasureTheory.Measure.upperQuantile_map_of_monotoneOn` — the quantiles of a pushforward along a
  map that is nondecreasing and continuous on an interval of full mass, with the global forms
  `MeasureTheory.Measure.quantile_map_of_monotone` and
  `MeasureTheory.Measure.upperQuantile_map_of_monotone`;
* `MeasureTheory.Measure.quantile_neg`, `MeasureTheory.Measure.upperQuantile_neg` — the quantiles
  of the reflected law, with `MeasureTheory.Measure.cdf_neg_of_measure_singleton_eq_zero` its
  cumulative distribution function away from atoms;
* `MeasureTheory.Measure.quantile_map_of_antitoneOn`,
  `MeasureTheory.Measure.upperQuantile_map_of_antitoneOn` — the quantiles of a pushforward along a
  nonincreasing continuous map, with the global forms
  `MeasureTheory.Measure.quantile_map_of_antitone` and
  `MeasureTheory.Measure.upperQuantile_map_of_antitone`;
* `MeasureTheory.Measure.quantile_map_exp`, `MeasureTheory.Measure.quantile_map_log`,
  `MeasureTheory.Measure.quantile_map_rpow`, `MeasureTheory.Measure.quantile_map_sqrt`,
  `MeasureTheory.Measure.quantile_map_inv` and their upper-quantile counterparts — the elementary
  maps, with the logarithm, real powers and the reciprocal taken on the half-line carrying a
  positive or nonnegative law.

## References

* P. Embrechts and M. Hofert, *A note on generalized inverses*, Mathematical Methods of
  Operations Research 77 (2013), 423--432.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

variable {μ : Measure ℝ} {s : Set ℝ} {t : ℝ}

namespace MeasureTheory.Measure

variable {g : ℝ → ℝ}

/-! ### Nondecreasing maps -/

/-- **Quantiles of a nondecreasing image.** If `g` is nondecreasing and continuous on an interval
carrying all the mass of `μ`, then at every level strictly between `0` and `1` the quantile of the
law of `g X` is `g` applied to the quantile of the law of `X`. -/
theorem quantile_map_of_monotoneOn [IsProbabilityMeasure μ] (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : MonotoneOn g s) (hgc : ContinuousOn g s) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map g).quantile t = g (μ.quantile t) := by
  have hgm : AEMeasurable g μ :=
    restrict_eq_self_of_ae_mem hμs ▸ aemeasurable_restrict_of_monotoneOn hs.measurableSet hg
  have hq := hs.quantile_mem hμs h0 h1
  refine le_antisymm ((quantile_le_iff _ h0 h1).2 ?_) (le_of_not_gt fun hlt ↦ ?_)
  · -- Every point of `s` below the quantile is sent below its image.
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hgm measurableSet_Iic]
    refine (le_cdf_quantile μ h1).trans ?_
    rw [cdf_eq_real]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (hμs.mono fun x hx hxq ↦ hg hx hq hxq))
  · -- Left continuity keeps `g` above the smaller quantile on some `s ∩ Ioc l q`, so the mass
    -- sent below it is at most `cdf μ l`, which is smaller than `t`.
    obtain ⟨l, hlq, hl⟩ := exists_Ioc_subset_of_mem_nhds
      (eventually_nhdsWithin_iff.1 ((hgc _ hq).eventually (lt_mem_nhds hlt)))
      ⟨μ.quantile t - 1, by linarith⟩
    refine ((lt_quantile_iff μ h0 h1).1 hlq).not_ge ((le_cdf_quantile (μ.map g) h1).trans ?_)
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hgm measurableSet_Iic, cdf_eq_real]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hμs.mono fun x hx hxy ↦ ?_))
    simp only [mem_preimage, mem_Iic] at hxy ⊢
    by_contra! hxl
    rcases le_or_gt x (μ.quantile t) with hxq | hxq
    · exact (hl ⟨hxl, hxq⟩ hx).not_ge hxy
    · exact hlt.not_ge ((hg hq hx hxq.le).trans hxy)

/-- **Upper quantiles of a nondecreasing image.** If `g` is nondecreasing and continuous on an
interval carrying all the mass of `μ`, then at every level strictly between `0` and `1` the upper
quantile of the law of `g X` is `g` applied to the upper quantile of the law of `X`. -/
theorem upperQuantile_map_of_monotoneOn [IsProbabilityMeasure μ] (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : MonotoneOn g s) (hgc : ContinuousOn g s) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map g).upperQuantile t = g (μ.upperQuantile t) := by
  have hgm : AEMeasurable g μ :=
    restrict_eq_self_of_ae_mem hμs ▸ aemeasurable_restrict_of_monotoneOn hs.measurableSet hg
  have hp := hs.upperQuantile_mem hμs h0 h1
  refine le_antisymm (le_of_forall_gt_imp_ge_of_dense fun y hy ↦ ?_)
    ((le_upperQuantile_iff _ h0 h1).2 ?_)
  · -- Right continuity keeps `g` below `y` on some `s ∩ Ico p r`, so every point of `s` below `r`
    -- is sent to at most `y`, and that mass exceeds `t`.
    obtain ⟨r, hpr, hr⟩ := exists_Ico_subset_of_mem_nhds
      (eventually_nhdsWithin_iff.1 ((hgc _ hp).eventually (gt_mem_nhds hy)))
      ⟨μ.upperQuantile t + 1, by linarith⟩
    refine upperQuantile_le_of_lt_cdf _ h0 (((upperQuantile_lt_iff μ h0 h1).1 hpr).trans_le ?_)
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hgm measurableSet_Iic]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae (hμs.mono fun x hx hxr ↦ ?_))
    rcases le_or_gt (μ.upperQuantile t) x with hpx | hxp
    · exact (hr ⟨hpx, hxr⟩ hx).le
    · exact (hg hx hp hxp.le).trans hy.le
  · -- A point of `s` sent strictly below the image of the upper quantile lies strictly below it.
    refine le_trans ?_ (measureReal_Iio_upperQuantile_le μ h0 h1)
    rw [map_measureReal_apply_of_aemeasurable hgm measurableSet_Iio]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono_ae (hμs.mono fun x hx hxp ↦ lt_of_not_ge fun hpx ↦
        (hg hp hx hpx).not_gt hxp))

/-- **Quantiles of a nondecreasing image.** For a nondecreasing continuous `g`, the quantile of
the law of `g X` at a level strictly between `0` and `1` is `g` applied to the quantile of the law
of `X`. -/
theorem quantile_map_of_monotone [IsProbabilityMeasure μ] (hg : Monotone g) (hgc : Continuous g)
    (h0 : 0 < t) (h1 : t < 1) : (μ.map g).quantile t = g (μ.quantile t) :=
  quantile_map_of_monotoneOn ordConnected_univ (ae_of_all _ mem_univ) (hg.monotoneOn _)
    hgc.continuousOn h0 h1

/-- **Upper quantiles of a nondecreasing image.** For a nondecreasing continuous `g`, the upper
quantile of the law of `g X` at a level strictly between `0` and `1` is `g` applied to the upper
quantile of the law of `X`. -/
theorem upperQuantile_map_of_monotone [IsProbabilityMeasure μ] (hg : Monotone g)
    (hgc : Continuous g) (h0 : 0 < t) (h1 : t < 1) :
    (μ.map g).upperQuantile t = g (μ.upperQuantile t) :=
  upperQuantile_map_of_monotoneOn ordConnected_univ (ae_of_all _ mem_univ) (hg.monotoneOn _)
    hgc.continuousOn h0 h1

/-! ### Reflection and nonincreasing maps -/

/-- **Quantiles of the reflected law.** The quantile of the law of `-X` at a level strictly between
`0` and `1` is minus the upper quantile of the law of `X` at the complementary level. -/
@[simp] theorem quantile_neg [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    μ.neg.quantile t = -μ.upperQuantile (1 - t) := by
  refine eq_of_forall_ge_iff fun y ↦ ?_
  have hpre : (Neg.neg ⁻¹' Iic y : Set ℝ) = (Iio (-y))ᶜ := by
    ext x
    simp
  rw [quantile_le_iff _ h0 h1, cdf_eq_real, neg_def,
    map_measureReal_apply measurable_neg measurableSet_Iic, hpre,
    measureReal_compl measurableSet_Iio, probReal_univ, neg_le,
    le_upperQuantile_iff μ (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

/-- **Upper quantiles of the reflected law.** The upper quantile of the law of `-X` at a level
strictly between `0` and `1` is minus the quantile of the law of `X` at the complementary level. -/
@[simp] theorem upperQuantile_neg [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    μ.neg.upperQuantile t = -μ.quantile (1 - t) := by
  refine eq_of_forall_le_iff fun y ↦ ?_
  have hpre : (Neg.neg ⁻¹' Iio y : Set ℝ) = (Iic (-y))ᶜ := by
    ext x
    simp
  rw [le_upperQuantile_iff _ h0 h1, neg_def,
    map_measureReal_apply measurable_neg measurableSet_Iio, hpre,
    measureReal_compl measurableSet_Iic, probReal_univ, le_neg,
    quantile_le_iff μ (by linarith) (by linarith), cdf_eq_real]
  constructor <;> intro h <;> linarith

/-- **The cumulative distribution function of the reflected law.** If `μ` has no atom at `-x`,
the law of `-X` puts mass `1 - cdf μ (-x)` on `Iic x`. -/
theorem cdf_neg_of_measure_singleton_eq_zero [IsProbabilityMeasure μ] {x : ℝ} (hx : μ {-x} = 0) :
    cdf μ.neg x = 1 - cdf μ (-x) := by
  have hpre : (Neg.neg ⁻¹' Iic x : Set ℝ) = (Iio (-x))ᶜ := by
    ext y
    simp
  rw [cdf_eq_real, neg_def, map_measureReal_apply measurable_neg measurableSet_Iic, hpre,
    measureReal_compl measurableSet_Iio, probReal_univ, measureReal_congr (Iio_ae_eq_Iic' hx),
    cdf_eq_real]

/-- Pushing forward along a nonincreasing map `g` is pushing the reflected law forward along the
map `x ↦ g (-x)`, which is nondecreasing and continuous on the reflected interval, and that
interval carries all the mass of the reflected law. -/
private theorem map_eq_map_neg_comp (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : AntitoneOn g s) (hgc : ContinuousOn g s) :
    μ.map g = μ.neg.map (g ∘ Neg.neg) ∧ (Neg.neg ⁻¹' s).OrdConnected ∧
      (∀ᵐ x ∂μ.neg, x ∈ Neg.neg ⁻¹' s) ∧
      MonotoneOn (g ∘ Neg.neg) (Neg.neg ⁻¹' s) ∧ ContinuousOn (g ∘ Neg.neg) (Neg.neg ⁻¹' s) := by
  have hae : ∀ᵐ x ∂μ.neg, x ∈ Neg.neg ⁻¹' s := by
    exact μ.ae_neg_mem_preimage hs.measurableSet hμs
  have hmono : MonotoneOn (g ∘ Neg.neg) (Neg.neg ⁻¹' s) :=
    fun x hx y hy hxy ↦ hg hy hx (neg_le_neg hxy)
  refine ⟨?_, hs.preimage_anti fun _ _ ↦ neg_le_neg, hae, hmono,
    hgc.comp continuousOn_neg fun _ hx ↦ hx⟩
  have hgm : AEMeasurable (g ∘ Neg.neg) μ.neg := restrict_eq_self_of_ae_mem hae ▸
    aemeasurable_restrict_of_monotoneOn (measurable_neg hs.measurableSet) hmono
  exact (μ.map_neg_comp hgm).symm

/-- **Quantiles of a nonincreasing image.** If `g` is nonincreasing and continuous on an interval
carrying all the mass of `μ`, then at every level strictly between `0` and `1` the quantile of the
law of `g X` is `g` applied to the upper quantile of the law of `X` at the complementary level. -/
theorem quantile_map_of_antitoneOn [IsProbabilityMeasure μ] (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : AntitoneOn g s) (hgc : ContinuousOn g s) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map g).quantile t = g (μ.upperQuantile (1 - t)) := by
  obtain ⟨hmap, hs', hμs', hg', hgc'⟩ := map_eq_map_neg_comp hs hμs hg hgc
  rw [hmap, quantile_map_of_monotoneOn hs' hμs' hg' hgc' h0 h1, Function.comp_apply,
    quantile_neg h0 h1, neg_neg]

/-- **Upper quantiles of a nonincreasing image.** If `g` is nonincreasing and continuous on an
interval carrying all the mass of `μ`, then at every level strictly between `0` and `1` the upper
quantile of the law of `g X` is `g` applied to the quantile of the law of `X` at the complementary
level. -/
theorem upperQuantile_map_of_antitoneOn [IsProbabilityMeasure μ] (hs : s.OrdConnected)
    (hμs : ∀ᵐ x ∂μ, x ∈ s) (hg : AntitoneOn g s) (hgc : ContinuousOn g s) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map g).upperQuantile t = g (μ.quantile (1 - t)) := by
  obtain ⟨hmap, hs', hμs', hg', hgc'⟩ := map_eq_map_neg_comp hs hμs hg hgc
  rw [hmap, upperQuantile_map_of_monotoneOn hs' hμs' hg' hgc' h0 h1, Function.comp_apply,
    upperQuantile_neg h0 h1, neg_neg]

/-- **Quantiles of a nonincreasing image.** For a nonincreasing continuous `g`, the quantile of
the law of `g X` at a level strictly between `0` and `1` is `g` applied to the upper quantile of
the law of `X` at the complementary level. -/
theorem quantile_map_of_antitone [IsProbabilityMeasure μ] (hg : Antitone g) (hgc : Continuous g)
    (h0 : 0 < t) (h1 : t < 1) : (μ.map g).quantile t = g (μ.upperQuantile (1 - t)) :=
  quantile_map_of_antitoneOn ordConnected_univ (ae_of_all _ mem_univ) (hg.antitoneOn _)
    hgc.continuousOn h0 h1

/-- **Upper quantiles of a nonincreasing image.** For a nonincreasing continuous `g`, the upper
quantile of the law of `g X` at a level strictly between `0` and `1` is `g` applied to the
quantile of the law of `X` at the complementary level. -/
theorem upperQuantile_map_of_antitone [IsProbabilityMeasure μ] (hg : Antitone g)
    (hgc : Continuous g) (h0 : 0 < t) (h1 : t < 1) :
    (μ.map g).upperQuantile t = g (μ.quantile (1 - t)) :=
  upperQuantile_map_of_antitoneOn ordConnected_univ (ae_of_all _ mem_univ) (hg.antitoneOn _)
    hgc.continuousOn h0 h1

/-! ### Elementary maps -/

/-- The quantile of the law of `exp X` is the exponential of the quantile of the law of `X`. -/
@[simp] theorem quantile_map_exp [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    (μ.map Real.exp).quantile t = Real.exp (μ.quantile t) :=
  quantile_map_of_monotone Real.exp_monotone Real.continuous_exp h0 h1

/-- The upper quantile of the law of `exp X` is the exponential of the upper quantile of the law
of `X`. -/
@[simp] theorem upperQuantile_map_exp [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    (μ.map Real.exp).upperQuantile t = Real.exp (μ.upperQuantile t) :=
  upperQuantile_map_of_monotone Real.exp_monotone Real.continuous_exp h0 h1

/-- For a law carried by the positive half-line, the quantile of the law of `log X` is the
logarithm of the quantile of the law of `X`. -/
@[simp] theorem quantile_map_log [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 < x) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map Real.log).quantile t = Real.log (μ.quantile t) :=
  quantile_map_of_monotoneOn ordConnected_Ioi hμ Real.strictMonoOn_log.monotoneOn
    (Real.continuousOn_log.mono fun _ hx ↦ (ne_of_gt hx)) h0 h1

/-- For a law carried by the positive half-line, the upper quantile of the law of `log X` is the
logarithm of the upper quantile of the law of `X`. -/
@[simp] theorem upperQuantile_map_log [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 < x) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map Real.log).upperQuantile t = Real.log (μ.upperQuantile t) :=
  upperQuantile_map_of_monotoneOn ordConnected_Ioi hμ Real.strictMonoOn_log.monotoneOn
    (Real.continuousOn_log.mono fun _ hx ↦ (ne_of_gt hx)) h0 h1

/-- For a law carried by the nonnegative half-line and a nonnegative exponent `r`, the quantile of
the law of `X ^ r` is the `r`-th power of the quantile of the law of `X`. -/
@[simp] theorem quantile_map_rpow [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {r : ℝ}
    (hr : 0 ≤ r)
    (h0 : 0 < t) (h1 : t < 1) : (μ.map (· ^ r)).quantile t = μ.quantile t ^ r :=
  quantile_map_of_monotoneOn ordConnected_Ici hμ (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hr)
    (Real.continuous_rpow_const hr).continuousOn h0 h1

/-- For a law carried by the nonnegative half-line and a nonnegative exponent `r`, the upper
quantile of the law of `X ^ r` is the `r`-th power of the upper quantile of the law of `X`. -/
@[simp] theorem upperQuantile_map_rpow [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {r : ℝ}
    (hr : 0 ≤ r) (h0 : 0 < t) (h1 : t < 1) :
    (μ.map (· ^ r)).upperQuantile t = μ.upperQuantile t ^ r :=
  upperQuantile_map_of_monotoneOn ordConnected_Ici hμ
    (Real.monotoneOn_rpow_Ici_of_exponent_nonneg hr) (Real.continuous_rpow_const hr).continuousOn
    h0 h1

/-- The quantile of the law of `√X` is the square root of the quantile of the law of `X`. Since
`Real.sqrt` is nondecreasing and continuous on the whole line, no support hypothesis is needed. -/
@[simp] theorem quantile_map_sqrt [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    (μ.map Real.sqrt).quantile t = √(μ.quantile t) :=
  quantile_map_of_monotone (fun _ _ ↦ Real.sqrt_le_sqrt) Real.continuous_sqrt h0 h1

/-- The upper quantile of the law of `√X` is the square root of the upper quantile of the law
of `X`. -/
@[simp] theorem upperQuantile_map_sqrt [IsProbabilityMeasure μ] (h0 : 0 < t) (h1 : t < 1) :
    (μ.map Real.sqrt).upperQuantile t = √(μ.upperQuantile t) :=
  upperQuantile_map_of_monotone (fun _ _ ↦ Real.sqrt_le_sqrt) Real.continuous_sqrt h0 h1

/-- For a law carried by the positive half-line, the quantile of the law of `X⁻¹` is the
reciprocal of the upper quantile of the law of `X` at the complementary level. -/
@[simp] theorem quantile_map_inv [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 < x) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map (·⁻¹)).quantile t = (μ.upperQuantile (1 - t))⁻¹ :=
  quantile_map_of_antitoneOn ordConnected_Ioi hμ (fun _ hx _ _ hxy ↦ inv_anti₀ hx hxy)
    (continuousOn_inv₀.mono fun _ hx ↦ (ne_of_gt hx)) h0 h1

/-- For a law carried by the positive half-line, the upper quantile of the law of `X⁻¹` is the
reciprocal of the quantile of the law of `X` at the complementary level. -/
@[simp] theorem upperQuantile_map_inv [IsProbabilityMeasure μ] (hμ : ∀ᵐ x ∂μ, 0 < x) (h0 : 0 < t)
    (h1 : t < 1) : (μ.map (·⁻¹)).upperQuantile t = (μ.quantile (1 - t))⁻¹ :=
  upperQuantile_map_of_antitoneOn ordConnected_Ioi hμ (fun _ hx _ _ hxy ↦ inv_anti₀ hx hxy)
    (continuousOn_inv₀.mono fun _ hx ↦ (ne_of_gt hx)) h0 h1

end MeasureTheory.Measure
