/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Section
public import TauCeti.Probability.Quantile
-- Proof-only: almost every point of a convex set is interior, derivatives of quotients and
-- of local inverses, integrals of inner products, and integrability under conditioning.
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Convex.Measure
import TauCeti.Probability.ConditionalProbability

/-!
# The height quantile of a convex set

Let `s` be a set of positive finite volume in a finite-dimensional Euclidean space and `e` a
unit vector. The height `⟪e, x⟫` of a point `x` drawn uniformly from `s` has the law
`(volume[|s]).map fun x ↦ ⟪e, x⟫`. Its cumulative distribution function at `c` is the
proportion of the volume of `s` lying below the hyperplane `⟪e, x⟫ = c`, and it is continuous
because hyperplanes are null.

For a convex set the cumulative distribution function takes a value strictly between `0` and
`1` exactly at the heights of interior points of `s`, and it is strictly increasing there.
Hence the quantile function of the height law is a strictly increasing continuous
parametrization of the open interval `⟪e, interior s⟫` by the levels in `Ioo 0 1`. If `s` is
moreover bounded and Borel, the derivative of the volume below a hyperplane is the volume of the
hyperplane section, which is positive at the height of an interior point. The inverse function
theorem then shows that at every level `τ ∈ Ioo 0 1` the quantile `z` has derivative
`volume s / volume {y ∈ (ℝ ∙ e)ᗮ | y + z τ • e ∈ s}`.
For a bounded Borel set `s`, inverse transform sampling shows that the average of the quantile
over the levels is the mean height, that is, the height of the centroid of `s`.

This volume-fraction parametrization of heights is the change of variables in the
Kneser–Süss proof of the equality case of the Brunn–Minkowski inequality for convex bodies:
two bodies of equal volume are compared along each direction at heights cutting off equal
volume fractions.

## Main results

* `TauCeti.nullSingletonClass_map_inner_cond`: the height law has no atoms.
* `TauCeti.cdf_map_inner_cond`: the cumulative distribution function of the height law.
* `TauCeti.continuous_cdf_map_inner_cond`: it is continuous.
* `Convex.cdf_map_inner_cond_mem_Ioo_iff`: for a convex set it lies strictly between `0` and `1`
  exactly at the heights of interior points.
* `Convex.strictMonoOn_cdf_map_inner_cond`: it is strictly increasing there.
* `Convex.image_quantile_map_inner_cond_Ioo`: the quantile maps `Ioo 0 1` onto the heights of
  interior points.
* `Convex.quantile_map_inner_cond_mem_image_interior`: each interior level goes to the height of
  an interior point.
* `Convex.volume_real_hyperplaneSection_quantile_pos`,
  `Convex.continuousOn_volume_real_hyperplaneSection_quantile`: the hyperplane section at the
  quantile has positive volume, depending continuously on the level.
* `Convex.hasDerivAt_quantile_map_inner_cond`: the derivative of the quantile.
* `TauCeti.setIntegral_quantile_map_inner_cond`: the quantile averages to the height of the
  centroid.

## References

* H. Kneser and W. Süss, *Die Volumina in linearen Scharen konvexer Körper*, Mat. Tidsskr. B
  (1932), 19–25, for the volume-fraction comparison of convex bodies.
* R. Schneider, *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge University
  Press, 2014, Section 7.1, for an exposition of the Kneser–Süss argument.
-/

public section

open Filter MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e : E} {s : Set E}
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The height law gives a Borel set of heights the proportion of the volume of `s` at those
heights. -/
private theorem map_inner_cond_apply (e : E) (s : Set E) {I : Set ℝ} (hI : MeasurableSet I) :
    (volume[|s]).map (fun x ↦ ⟪e, x⟫) I = (volume s)⁻¹ * volume {x ∈ s | ⟪e, x⟫ ∈ I} := by
  have hm : Measurable fun x : E ↦ ⟪e, x⟫ := (continuous_const.inner continuous_id).measurable
  rw [Measure.map_apply hm hI, cond_apply' (hI.preimage hm)]
  -- `s ∩ (fun x ↦ ⟪e, x⟫) ⁻¹' I` is `{x ∈ s | ⟪e, x⟫ ∈ I}` by definition.
  rfl

private theorem isProbabilityMeasure_map_inner_cond (e : E) (hs0 : volume s ≠ 0)
    (hsi : volume s ≠ ∞) : IsProbabilityMeasure ((volume[|s]).map fun x ↦ ⟪e, x⟫) :=
  have := cond_isProbabilityMeasure_of_finite hs0 hsi
  inferInstance

/-- The law of the height along a unit vector of a point drawn uniformly from any set has no
atoms, since hyperplanes are null. -/
theorem nullSingletonClass_map_inner_cond (he : ‖e‖ = 1) (s : Set E) :
    NullSingletonClass ((volume[|s]).map fun x ↦ ⟪e, x⟫) := by
  refine ⟨fun c ↦ ?_⟩
  have h : volume {x ∈ (univ : Set E) | ⟪e, x⟫ ∈ ({c} : Set ℝ)} = 0 := by
    rw [volume_sep_inner_mem_eq_setLIntegral e he nullMeasurableSet_univ
      (measurableSet_singleton c)]
    exact setLIntegral_measure_zero _ _ Real.volume_singleton
  rw [map_inner_cond_apply e s (measurableSet_singleton c),
    measure_mono_null (fun x (hx : x ∈ {x ∈ s | ⟪e, x⟫ ∈ ({c} : Set ℝ)}) ↦
      (⟨mem_univ x, hx.2⟩ : x ∈ {x ∈ (univ : Set E) | ⟪e, x⟫ ∈ ({c} : Set ℝ)})) h, mul_zero]

/-- The cumulative distribution function of the height along `e` of a point drawn uniformly from
`s` is the proportion of the volume of `s` below the hyperplane at height `c`. -/
theorem cdf_map_inner_cond (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) (c : ℝ) :
    cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫) c =
      volume.real {x ∈ s | ⟪e, x⟫ ≤ c} / volume.real s := by
  have := isProbabilityMeasure_map_inner_cond e hs0 hsi
  rw [cdf_eq_real, measureReal_def, map_inner_cond_apply e s measurableSet_Iic,
    ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def, measureReal_def, div_eq_inv_mul]
  -- Membership in `Iic c` is `⟪e, x⟫ ≤ c` by definition.
  rfl

/-- The cumulative distribution function of the height law of a set of positive finite volume is
continuous, since hyperplanes are null. -/
theorem continuous_cdf_map_inner_cond (he : ‖e‖ = 1) (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) :
    Continuous (cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫)) :=
  have := isProbabilityMeasure_map_inner_cond e hs0 hsi
  have := nullSingletonClass_map_inner_cond he s
  continuous_cdf_of_noAtoms _

/-- The cumulative distribution function of the height law lies strictly between `0` and `1`
exactly when `s` has positive volume both below and above the height `c`. -/
private theorem cdf_map_inner_cond_mem_Ioo_iff_volume (he : ‖e‖ = 1) (hs0 : volume s ≠ 0)
    (hsi : volume s ≠ ∞) (c : ℝ) :
    cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫) c ∈ Ioo 0 1 ↔
      volume {x ∈ s | ⟪e, x⟫ ∈ Iio c} ≠ 0 ∧ volume {x ∈ s | ⟪e, x⟫ ∈ Ioi c} ≠ 0 := by
  set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
  have := isProbabilityMeasure_map_inner_cond e hs0 hsi
  have := nullSingletonClass_map_inner_cond he s
  have hinv : (volume s)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hsi
  have hlo : 0 < cdf ν c ↔ volume {x ∈ s | ⟪e, x⟫ ∈ Iio c} ≠ 0 := by
    rw [← ENNReal.ofReal_pos, ofReal_cdf, ← measure_congr Iio_ae_eq_Iic, pos_iff_ne_zero,
      map_inner_cond_apply e s measurableSet_Iio, mul_ne_zero_iff, and_iff_right hinv]
  have hhi : cdf ν c < 1 ↔ volume {x ∈ s | ⟪e, x⟫ ∈ Ioi c} ≠ 0 := by
    rw [← ENNReal.ofReal_lt_one, ofReal_cdf, ← tsub_pos_iff_lt, ← prob_compl_eq_one_sub
      measurableSet_Iic, compl_Iic, pos_iff_ne_zero, map_inner_cond_apply e s measurableSet_Ioi,
      mul_ne_zero_iff, and_iff_right hinv]
  rw [mem_Ioo, hlo, hhi]

/-- For a convex set of positive finite volume, the cumulative distribution function of the
height law lies strictly between `0` and `1` exactly at the heights of interior points. -/
theorem _root_.Convex.cdf_map_inner_cond_mem_Ioo_iff (hs : Convex ℝ s) (he : ‖e‖ = 1)
    (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) {c : ℝ} :
    cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫) c ∈ Ioo 0 1 ↔ c ∈ (fun x ↦ ⟪e, x⟫) '' interior s := by
  rw [cdf_map_inner_cond_mem_Ioo_iff_volume he hs0 hsi]
  constructor
  · rintro ⟨hlo, hhi⟩
    obtain ⟨x, hx, hxc⟩ := hs.interior_inter_nonempty_of_addHaar_inter_ne_zero
      (t := (fun x ↦ ⟪e, x⟫) ⁻¹' Iio c) hlo
    obtain ⟨y, hy, hyc⟩ := hs.interior_inter_nonempty_of_addHaar_inter_ne_zero
      (t := (fun x ↦ ⟪e, x⟫) ⁻¹' Ioi c) hhi
    exact (convex_iff_ordConnected.1 (hs.interior.linear_image (innerₛₗ ℝ e))).out
      ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨le_of_lt hxc, le_of_lt hyc⟩
  · intro hc
    have hnhds : ∀ᶠ t in 𝓝 c, t ∈ (fun x ↦ ⟪e, x⟫) '' interior s :=
      (isOpen_image_inner_interior he s).mem_nhds hc
    obtain ⟨a, hac, x, hx, rfl⟩ := hnhds.exists_lt
    obtain ⟨b, hcb, y, hy, rfl⟩ := hnhds.exists_gt
    exact ⟨(volume_sep_inner_mem_pos isOpen_Iio ⟨x, hx, hac⟩).ne',
      (volume_sep_inner_mem_pos isOpen_Ioi ⟨y, hy, hcb⟩).ne'⟩

/-- For a convex set of positive finite volume, the cumulative distribution function of the
height law is strictly increasing where it lies strictly between `0` and `1`. -/
theorem _root_.Convex.strictMonoOn_cdf_map_inner_cond (hs : Convex ℝ s) (he : ‖e‖ = 1)
    (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) :
    StrictMonoOn (cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫))
      (cdf ((volume[|s]).map fun x ↦ ⟪e, x⟫) ⁻¹' Ioo 0 1) := by
  set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
  have := isProbabilityMeasure_map_inner_cond e hs0 hsi
  intro c hc c' hc' hcc'
  rw [mem_preimage, hs.cdf_map_inner_cond_mem_Ioo_iff he hs0 hsi] at hc hc'
  -- An interior point lies strictly between the heights `c` and `c'`.
  have hmid := (convex_iff_ordConnected.1 (hs.interior.linear_image (innerₛₗ ℝ e))).out hc hc'
    ⟨by linarith, (by linarith : (c + c') / 2 ≤ c')⟩
  obtain ⟨x, hx, hxc⟩ := hmid
  have hpos : 0 < ν (Ioc c c') := by
    rw [map_inner_cond_apply e s measurableSet_Ioc]
    refine ENNReal.mul_pos (ENNReal.inv_ne_zero.2 hsi) ((volume_sep_inner_mem_pos isOpen_Ioo
      ⟨x, hx, ?_⟩).trans_le (measure_mono fun y (hy : y ∈ {x ∈ s | ⟪e, x⟫ ∈ Ioo c c'}) ↦
      (⟨hy.1, Ioo_subset_Ioc_self hy.2⟩ : y ∈ {x ∈ s | ⟪e, x⟫ ∈ Ioc c c'}))).ne'
    have hxc' : ⟪e, x⟫ = (c + c') / 2 := hxc
    rw [hxc']
    constructor <;> linarith
  rw [cdf_eq_real, cdf_eq_real, ← Iic_union_Ioc_eq_Iic hcc'.le,
    measureReal_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc]
  exact lt_add_of_pos_right _ (ENNReal.toReal_pos hpos.ne' (measure_ne_top ν _))

/-- For a convex set of positive finite volume, the quantile function of the height law maps the
levels in `Ioo 0 1` onto the heights of interior points. -/
theorem _root_.Convex.image_quantile_map_inner_cond_Ioo (hs : Convex ℝ s) (he : ‖e‖ = 1)
    (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) :
    ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile '' Ioo 0 1 = (fun x ↦ ⟪e, x⟫) '' interior s := by
  set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
  have hcont := continuous_cdf_map_inner_cond he hs0 hsi
  refine Subset.antisymm ?_ fun c hc ↦ ?_
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [← hs.cdf_map_inner_cond_mem_Ioo_iff he hs0 hsi, cdf_quantile ν hcont hτ.1 hτ.2]
    exact hτ
  · rw [← hs.cdf_map_inner_cond_mem_Ioo_iff he hs0 hsi] at hc
    exact ⟨cdf ν c, hc, quantile_cdf ν (hs.strictMonoOn_cdf_map_inner_cond he hs0 hsi) hc⟩

/-- For a convex set of positive finite volume, the quantile function of the height law takes
every level in `Ioo 0 1` to the height of an interior point. -/
theorem _root_.Convex.quantile_map_inner_cond_mem_image_interior (hs : Convex ℝ s) (he : ‖e‖ = 1)
    (hs0 : volume s ≠ 0) (hsi : volume s ≠ ∞) {τ : ℝ} (hτ : τ ∈ Ioo 0 1) :
    ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ ∈ (fun x ↦ ⟪e, x⟫) '' interior s :=
  hs.image_quantile_map_inner_cond_Ioo he hs0 hsi ▸ mem_image_of_mem _ hτ

/-- The hyperplane section of a bounded convex set of positive volume at its height quantile has
positive finite volume at every level in `Ioo 0 1`. -/
theorem _root_.Convex.volume_real_hyperplaneSection_quantile_pos (hs : Convex ℝ s)
    (hsb : Bornology.IsBounded s) (hs0 : volume s ≠ 0) (he : ‖e‖ = 1) {τ : ℝ}
    (hτ : τ ∈ Ioo 0 1) :
    0 < volume.real {y : (ℝ ∙ e)ᗮ |
      (y : E) + ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ s} :=
  ENNReal.toReal_pos (volume_hyperplaneSection_pos e he
    (hs.quantile_map_inner_cond_mem_image_interior he hs0 hsb.measure_lt_top.ne hτ)).ne'
    (hsb.volume_hyperplaneSection_lt_top e _).ne

/-- The volume of the hyperplane section of a bounded convex set of positive volume at its height
quantile is continuous on the levels in `Ioo 0 1`. -/
theorem _root_.Convex.continuousOn_volume_real_hyperplaneSection_quantile (hs : Convex ℝ s)
    (hsb : Bornology.IsBounded s) (hs0 : volume s ≠ 0) (he : ‖e‖ = 1) :
    ContinuousOn (fun τ ↦ volume.real {y : (ℝ ∙ e)ᗮ |
      (y : E) + ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ s}) (Ioo 0 1) := by
  have hsi : volume s ≠ ∞ := hsb.measure_lt_top.ne
  refine (hs.continuousOn_volume_real_hyperplaneSection he
    fun t ↦ (hsb.volume_hyperplaneSection_lt_top e t).ne).comp
    (continuousOn_quantile _ (continuous_cdf_map_inner_cond he hs0 hsi)
      (hs.strictMonoOn_cdf_map_inner_cond he hs0 hsi)) fun τ hτ ↦ ?_
  exact interior_maximal (image_mono interior_subset) (isOpen_image_inner_interior he s)
    (hs.quantile_map_inner_cond_mem_image_interior he hs0 hsi hτ)

/-- **Derivative of the height quantile.** For a bounded Borel convex set `s` of positive volume
and a unit vector `e`, the quantile function `z` of the height law along `e` is differentiable at
every level `τ ∈ Ioo 0 1`, with derivative the volume of `s` divided by the volume of the
hyperplane section of `s` at height `z τ`. -/
theorem _root_.Convex.hasDerivAt_quantile_map_inner_cond (hs : Convex ℝ s)
    (hsb : Bornology.IsBounded s) (hsm : MeasurableSet s) (hs0 : volume s ≠ 0) (he : ‖e‖ = 1)
    {τ : ℝ} (hτ : τ ∈ Ioo 0 1) :
    HasDerivAt ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile
      (volume.real s / volume.real {y : (ℝ ∙ e)ᗮ |
        (y : E) + ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ • e ∈ s}) τ := by
  set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
  have hsi : volume s ≠ ∞ := hsb.measure_lt_top.ne
  have hcont := continuous_cdf_map_inner_cond he hs0 hsi
  have hz := hs.quantile_map_inner_cond_mem_image_interior he hs0 hsi hτ
  -- The quantile lies at an interior height, where the volume below a hyperplane is
  -- differentiable with the section volume as derivative.
  have hzi : ν.quantile τ ∈ interior ((fun x ↦ ⟪e, x⟫) '' s) :=
    interior_maximal (image_mono interior_subset) (isOpen_image_inner_interior he s) hz
  have hcdf : HasDerivAt (cdf ν) (volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + ν.quantile τ • e ∈ s} /
      volume.real s) (ν.quantile τ) :=
    HasDerivAt.congr_of_eventuallyEq
      (HasDerivAt.div_const (hs.hasDerivAt_volume_real_sep_inner_le hsb hsm he hzi) _)
      (Eventually.of_forall fun c ↦ cdf_map_inner_cond hs0 hsi c)
  have hne : volume.real {y : (ℝ ∙ e)ᗮ | (y : E) + ν.quantile τ • e ∈ s} / volume.real s ≠ 0 :=
    div_ne_zero (ENNReal.toReal_pos (volume_hyperplaneSection_pos e he hz).ne'
      (hsb.volume_hyperplaneSection_lt_top e _).ne).ne'
      (ENNReal.toReal_pos hs0 hsi).ne'
  have hloc : ∀ᶠ y in 𝓝 τ, cdf ν (ν.quantile y) = y := by
    filter_upwards [isOpen_Ioo.mem_nhds hτ] with y hy using cdf_quantile ν hcont hy.1 hy.2
  simpa only [inv_div] using HasDerivAt.of_local_left_inverse
    ((continuousOn_quantile ν hcont (hs.strictMonoOn_cdf_map_inner_cond he hs0 hsi)).continuousAt
      (isOpen_Ioo.mem_nhds hτ)) hcdf hne hloc

/-- The quantile function of the height law of a bounded Borel set of positive volume is
integrable on the levels `Ioo 0 1`. -/
theorem integrableOn_quantile_map_inner_cond (e : E) (hsb : Bornology.IsBounded s)
    (hsm : MeasurableSet s) (hs0 : volume s ≠ 0) :
    IntegrableOn ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile (Ioo 0 1) := by
  set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
  have := cond_isProbabilityMeasure_of_finite hs0 hsb.measure_lt_top.ne
  have hm : Measurable fun x : E ↦ ⟪e, x⟫ := (continuous_const.inner continuous_id).measurable
  obtain ⟨C, hC⟩ := hsb.exists_norm_le
  have hν : Integrable id ν :=
    (integrable_map_measure aestronglyMeasurable_id hm.aemeasurable).2
      ((integrable_cond_of_norm_le hsm aestronglyMeasurable_id hC).const_inner e)
  exact (integrableOn_quantile_iff ν).2 hν

/-- **The mean height.** The average over the levels `Ioo 0 1` of the quantile function of the
height `⟪e, x⟫` of a point `x` drawn uniformly from a bounded Borel set `s` of positive volume is
the height of the centroid `∫ x, x ∂(volume[|s])` of `s`. -/
theorem setIntegral_quantile_map_inner_cond (e : E) (hsb : Bornology.IsBounded s)
    (hsm : MeasurableSet s) (hs0 : volume s ≠ 0) :
    ∫ τ in Ioo 0 1, ((volume[|s]).map fun x ↦ ⟪e, x⟫).quantile τ =
      ⟪e, ∫ x, x ∂(volume[|s])⟫ := by
  set ν := (volume[|s]).map fun x ↦ ⟪e, x⟫
  have := cond_isProbabilityMeasure_of_finite hs0 hsb.measure_lt_top.ne
  have hm : Measurable fun x : E ↦ ⟪e, x⟫ := (continuous_const.inner continuous_id).measurable
  obtain ⟨C, hC⟩ := hsb.exists_norm_le
  calc ∫ τ in Ioo 0 1, ν.quantile τ = ∫ y, y ∂ν := setIntegral_quantile_eq_integral ν
    _ = ∫ x, ⟪e, x⟫ ∂(volume[|s]) := integral_map hm.aemeasurable aestronglyMeasurable_id
    _ = ⟪e, ∫ x, x ∂(volume[|s])⟫ := integral_inner
          (integrable_cond_of_norm_le hsm aestronglyMeasurable_id hC) e

end TauCeti
