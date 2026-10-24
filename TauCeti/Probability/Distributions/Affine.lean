/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Density
public import TauCeti.Probability.Quantile
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Probability.Distributions.Dirac

/-!
# Affine images of real laws

For a measure `μ` on `ℝ` and real numbers `a`, `b`, the law of `a + b X` for `X` with law `μ` is
the pushforward `μ.map (fun x => a + b * x)`. This file computes its density and elementary
observables in terms of those of `μ`: the cumulative distribution function, integrability and
moments, and the exponential transforms. Once a location-scale identity between two families is
known as an equality of measures, these formulas transfer each observable along it.

At a nonzero slope, an original density `f` becomes
`|b|⁻¹ f ((x - a) / b)`. The measure-level change of variables is accompanied by `HasPDF`,
canonical `pdf`, and Radon–Nikodym derivative forms, so callers can use the result whether their
input is presented as a weighted Lebesgue measure, a random variable, or an absolutely continuous
law.

The cdf at a positive slope is the cdf of `μ` at the pulled-back point. At a negative slope the
map reverses order, so it is one minus the mass `μ` gives to the open half-line below the
pulled-back point: this left limit of the cdf cannot be replaced by the cdf itself when `μ` has
an atom there. At slope zero the pushforward of a probability measure is the Dirac mass at `a`,
which is Mathlib's `MeasureTheory.Measure.map_const`.

The variance, moment-generating function and characteristic function computations follow
Mathlib's `ProbabilityTheory.variance_id_map`, `ProbabilityTheory.variance_const_add` and
`ProbabilityTheory.variance_const_mul`, `ProbabilityTheory.mgf_const_add` and
`ProbabilityTheory.mgf_const_mul`, and `MeasureTheory.charFun_apply_real`, which they reduce to.

## Main results

* `TauCeti.Probability.map_affine_map_affine` — affine pushforwards compose;
* `TauCeti.Probability.support_map_affine` — a nonconstant affine pushforward transports the
  topological support;
* `TauCeti.Probability.measurable_map_affine` — affine pushforward is jointly measurable in the
  probability law, intercept, and slope;
* `TauCeti.Probability.affineDensity`,
  `TauCeti.Probability.map_affine_withDensity_volume` — the transformed density and the
  measure-level change of variables;
* `TauCeti.Probability.map_affine_eq_withDensity_pdf`, `TauCeti.Probability.hasLaw_affine`,
  `TauCeti.Probability.hasPDF_affine`, `TauCeti.Probability.pdf_affine`, and
  `TauCeti.Probability.rnDeriv_map_affine` — the corresponding random-variable and
  Radon–Nikodym interfaces;
* `TauCeti.Probability.cdf_map_affine_of_pos`, `TauCeti.Probability.cdf_map_affine_of_neg` — the
  cdf at a positive and at a negative slope;
* `TauCeti.Probability.quantile_map_affine_pos`,
  `TauCeti.Probability.quantile_map_affine_neg` and their upper-quantile counterparts — affine
  transport of lower and upper quantiles, including the reversal of the level at a negative
  slope;
* `TauCeti.Probability.memLp_id_map_affine_iff` — a nonconstant affine image has exactly the
  absolute moments of the original law;
* `TauCeti.Probability.integral_id_map_affine`, `TauCeti.Probability.variance_id_map_affine` —
  the mean `a + b E[X]` and the variance `b ^ 2 Var[X]`;
* `TauCeti.Probability.moment_id_map_affine`, `TauCeti.Probability.centralMoment_id_map_affine` —
  raw moments by the binomial expansion, and central moments scaled by `b ^ n`;
* `TauCeti.Probability.mgf_id_map_affine`, `TauCeti.Probability.integrableExpSet_id_map_affine`,
  `TauCeti.Probability.cgf_id_map_affine` — the moment-generating function `exp (a t) M(b t)`,
  its domain `{t | b t ∈ D}`, and the cumulant-generating function `a t + K(b t)` on it;
* `TauCeti.Probability.charFun_map_affine` — the characteristic function `exp (i a t) φ(b t)`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {μ : Measure ℝ} {a b : ℝ}

/-- The affine map `x ↦ a + b * x` is measurable. -/
private theorem measurable_affine (a b : ℝ) : Measurable fun x : ℝ => a + b * x := by fun_prop

/-- **Composition of affine pushforwards.** Applying `y ↦ c + d * y` after `x ↦ a + b * x` is the
single affine map with intercept `c + d * a` and slope `d * b`. -/
theorem map_affine_map_affine (a b c d : ℝ) :
    (μ.map fun x => a + b * x).map (fun y => c + d * y) =
      μ.map fun x => c + d * a + d * b * x := by
  rw [Measure.map_map (measurable_affine c d) (measurable_affine a b)]
  congr 1
  ext x
  simp only [Function.comp_apply]
  ring

/-- **Support of an affine image.** A nonconstant affine pushforward has support equal to the
affine image of the original support. -/
theorem support_map_affine (hb : b ≠ 0) :
    (μ.map fun x ↦ a + b * x).support = (fun x ↦ a + b * x) '' μ.support := by
  let e : ℝ ≃ₜ ℝ := (Homeomorph.smulOfNeZero b hb).trans (Homeomorph.addLeft a)
  have he : (e : ℝ → ℝ) = fun x ↦ a + b * x := by
    funext x
    simp [e, smul_eq_mul]
  rw [← he]
  exact μ.support_map_homeomorph e

/-- Affine pushforward is jointly measurable in the probability law, intercept, and slope. -/
@[fun_prop]
theorem measurable_map_affine :
    Measurable fun p : ProbabilityMeasure ℝ × ℝ × ℝ =>
      (p.1 : Measure ℝ).map fun x => p.2.1 + p.2.2 * x := by
  exact measurable_subtype_coe.comp
    (TauCeti.MeasureTheory.measurable_probabilityMeasure_map_of_measurable_uncurry
      (f := fun p : ℝ × ℝ => fun x => p.1 + p.2 * x) (by fun_prop))

/-! ### Densities -/

/-- The density obtained from `f` by the nonconstant affine change of variables
`x ↦ a + b * x`. For `b ≠ 0`, this is `|b|⁻¹ f ((y - a) / b)`.

At `b = 0` this function is zero; the density transport theorems below deliberately require a
nonzero slope because the affine image is then a Dirac measure rather than an absolutely
continuous law. -/
noncomputable def affineDensity (a b : ℝ) (f : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |b|⁻¹ * f ((y - a) / b)

/-- The value of the density obtained by an affine change of variables. -/
@[simp]
theorem affineDensity_apply (a b : ℝ) (f : ℝ → ℝ≥0∞) (y : ℝ) :
    affineDensity a b f y = ENNReal.ofReal |b|⁻¹ * f ((y - a) / b) :=
  affineDensity.eq_def a b f y

/-- The affine transform of a measurable density is measurable. -/
@[fun_prop]
theorem measurable_affineDensity {f : ℝ → ℝ≥0∞} (hf : Measurable f) (a b : ℝ) :
    Measurable (affineDensity a b f) := by
  unfold affineDensity
  fun_prop

private noncomputable def mulLeftCLE (b : ℝ) (hb : b ≠ 0) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 b hb)

@[simp]
private theorem mulLeftCLE_apply (b : ℝ) (hb : b ≠ 0) (x : ℝ) :
    mulLeftCLE b hb x = b * x := by
  simp [mulLeftCLE, Units.smul_def, smul_eq_mul]

@[simp]
private theorem mulLeftCLE_symm_apply (b : ℝ) (hb : b ≠ 0) (x : ℝ) :
    (mulLeftCLE b hb).symm x = x / b := by
  apply (mulLeftCLE b hb).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, mulLeftCLE_apply]
  exact (mul_div_cancel₀ x hb).symm

private theorem coe_mulLeftCLE (b : ℝ) (hb : b ≠ 0) :
    (mulLeftCLE b hb : ℝ →ₗ[ℝ] ℝ) = b • LinearMap.id := by
  ext
  simp

private theorem det_mulLeftCLE (b : ℝ) (hb : b ≠ 0) :
    LinearMap.det (mulLeftCLE b hb : ℝ →ₗ[ℝ] ℝ) = b := by
  rw [coe_mulLeftCLE, LinearMap.det_smul]
  simp

/-- **Affine change of variables for a real density.** If `b ≠ 0`, pushing a Lebesgue density
`f` forward by `x ↦ a + b * x` gives the density `|b|⁻¹ f ((y - a) / b)`. -/
theorem map_affine_withDensity_volume (f : ℝ → ℝ≥0∞) (hb : b ≠ 0) :
    (volume.withDensity f).map (fun x ↦ a + b * x) =
      volume.withDensity (affineDensity a b f) := by
  have hmap : (fun x : ℝ ↦ a + b * x) = fun x ↦ a + mulLeftCLE b hb x := by
    ext x
    rw [mulLeftCLE_apply]
  rw [hmap, Measure.map_affine_withDensity]
  refine withDensity_congr_ae (.of_forall fun y ↦ ?_)
  simp only [affineDensity]
  rw [mulLeftCLE_symm_apply, det_mulLeftCLE, abs_inv]

/-- The Radon–Nikodym derivative of a nonconstant affine image of an s-finite real measure is the
affine transform of its Radon–Nikodym derivative. -/
theorem rnDeriv_map_affine [SFinite μ] (hb : b ≠ 0) :
    (μ.map fun x ↦ a + b * x).rnDeriv volume =ᵐ[volume]
      affineDensity a b (μ.rnDeriv volume) := by
  have hmap : (fun x : ℝ ↦ a + b * x) = fun x ↦ a + mulLeftCLE b hb x := by
    ext x
    rw [mulLeftCLE_apply]
  rw [hmap]
  refine (Measure.rnDeriv_map_affine volume (mulLeftCLE b hb) a μ).trans
    (.of_forall fun y ↦ ?_)
  simp only [affineDensity_apply, mulLeftCLE_symm_apply, det_mulLeftCLE, abs_inv]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- The law of a nonconstant affine transform, expressed using the canonical density of the
original random variable. -/
theorem map_affine_eq_withDensity_pdf [HasPDF X P] (hb : b ≠ 0) :
    P.map (fun ω ↦ a + b * X ω) =
      volume.withDensity (affineDensity a b (pdf X P)) := by
  have hcomp : (fun ω ↦ a + b * X ω) = (fun x ↦ a + b * x) ∘ X := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable (measurable_affine a b).aemeasurable
    (HasPDF.aemeasurable X P volume), map_eq_withDensity_pdf X P volume,
    map_affine_withDensity_volume (a := a) (b := b) _ hb]

/-- A nonconstant affine transform has the law obtained by affinely transporting its canonical
density. -/
theorem hasLaw_affine [HasPDF X P] (hb : b ≠ 0) :
    HasLaw (fun ω ↦ a + b * X ω)
      (volume.withDensity (affineDensity a b (pdf X P))) P where
  aemeasurable := ((HasPDF.aemeasurable X P volume).const_mul b).const_add a
  map_eq := map_affine_eq_withDensity_pdf (a := a) (b := b) hb

/-- A nonconstant affine transform of a real random variable with a density again has a density. -/
theorem hasPDF_affine [HasPDF X P] (hb : b ≠ 0) :
    HasPDF (fun ω ↦ a + b * X ω) P := by
  let g := affineDensity a b (pdf X P)
  have hg : AEMeasurable g volume :=
    (measurable_affineDensity (measurable_pdf X P) a b).aemeasurable
  have hLaw : HasLaw (fun ω ↦ a + b * X ω) (volume.withDensity g) P :=
    hasLaw_affine (a := a) (b := b) (X := X) (P := P) hb
  exact hasPDF_of_hasLaw_withDensity hg hLaw

/-- The canonical density of a nonconstant affine transform is
`|b|⁻¹ pdf X P ((y - a) / b)`. -/
theorem pdf_affine [HasPDF X P] (hb : b ≠ 0) :
    pdf (fun ω ↦ a + b * X ω) P =ᵐ[volume] affineDensity a b (pdf X P) := by
  exact pdf_eq_of_hasLaw_withDensity
    (measurable_affineDensity (measurable_pdf X P) a b).aemeasurable (hasLaw_affine hb)

/-! ### Cumulative distribution functions -/

/-- At a positive slope, the cdf of the affine image is the cdf of `μ` at the pulled-back point
`(x - a) / b`. -/
theorem cdf_map_affine_of_pos [IsProbabilityMeasure μ] (hb : 0 < b) (x : ℝ) :
    cdf (μ.map fun y => a + b * y) x = cdf μ ((x - a) / b) := by
  have hpre : (fun y => a + b * y) ⁻¹' Iic x = Iic ((x - a) / b) := by
    ext y
    simp only [mem_preimage, mem_Iic, le_div_iff₀ hb]
    constructor <;> intro h <;> linarith
  rw [cdf_eq_real, cdf_eq_real, map_measureReal_apply (measurable_affine a b) measurableSet_Iic,
    hpre]

/-- At a negative slope, the cdf of the affine image is one minus the mass `μ` gives to the open
half-line below the pulled-back point `(x - a) / b`, that is, one minus the left limit of the cdf
of `μ` there. -/
theorem cdf_map_affine_of_neg [IsProbabilityMeasure μ] (hb : b < 0) (x : ℝ) :
    cdf (μ.map fun y => a + b * y) x = 1 - μ.real (Iio ((x - a) / b)) := by
  have hpre : (fun y => a + b * y) ⁻¹' Iic x = (Iio ((x - a) / b))ᶜ := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_compl_iff, mem_Iio, not_lt, div_le_iff_of_neg hb]
    constructor <;> intro h <;> linarith
  rw [cdf_eq_real, map_measureReal_apply (measurable_affine a b) measurableSet_Iic, hpre,
    measureReal_compl measurableSet_Iio, probReal_univ]

/-! ### Quantiles -/

/-- At a positive slope, the mass strictly below a point under an affine image is the mass
strictly below its pulled-back point. -/
theorem measureReal_Iio_map_affine_of_pos (hb : 0 < b) (x : ℝ) :
    (μ.map fun y => a + b * y).real (Iio x) = μ.real (Iio ((x - a) / b)) := by
  have hpre : (fun y => a + b * y) ⁻¹' Iio x = Iio ((x - a) / b) := by
    ext y
    simp only [mem_preimage, mem_Iio, lt_div_iff₀ hb]
    constructor <;> intro h <;> linarith
  rw [map_measureReal_apply (measurable_affine a b) measurableSet_Iio, hpre]

/-- At a negative slope, the mass strictly below a point under an affine image is one minus the
cdf at its pulled-back point. -/
theorem measureReal_Iio_map_affine_of_neg [IsProbabilityMeasure μ] (hb : b < 0) (x : ℝ) :
    (μ.map fun y => a + b * y).real (Iio x) = 1 - cdf μ ((x - a) / b) := by
  have hpre : (fun y => a + b * y) ⁻¹' Iio x = (Iic ((x - a) / b))ᶜ := by
    ext y
    simp only [mem_preimage, mem_Iio, mem_compl_iff, mem_Iic, not_le,
      div_lt_iff_of_neg hb]
    constructor <;> intro h <;> linarith
  rw [map_measureReal_apply (measurable_affine a b) measurableSet_Iio, hpre,
    measureReal_compl measurableSet_Iic, probReal_univ, cdf_eq_real]

/-- A positive affine map carries lower quantiles to lower quantiles. -/
@[simp]
theorem quantile_map_affine_pos [IsProbabilityMeasure μ] {u : ℝ} (hb : 0 < b)
    (h0 : 0 < u) (h1 : u < 1) :
    (μ.map fun x => a + b * x).quantile u = a + b * μ.quantile u := by
  apply le_antisymm
  · rw [Measure.quantile_le_iff _ h0 h1, cdf_map_affine_of_pos hb]
    simp only [add_sub_cancel_left, mul_div_cancel_left₀ _ hb.ne']
    exact Measure.le_cdf_quantile μ h1
  · have hcdf := Measure.le_cdf_quantile (μ.map fun x => a + b * x) h1
    rw [cdf_map_affine_of_pos hb] at hcdf
    have hq := (Measure.quantile_le_iff μ h0 h1).mpr hcdf
    have := (le_div_iff₀ hb).mp hq
    linarith

/-- A positive affine map carries upper quantiles to upper quantiles. -/
@[simp]
theorem upperQuantile_map_affine_pos [IsProbabilityMeasure μ] {u : ℝ} (hb : 0 < b)
    (h0 : 0 < u) (h1 : u < 1) :
    (μ.map fun x => a + b * x).upperQuantile u = a + b * μ.upperQuantile u := by
  apply le_antisymm
  · have hmass := Measure.measureReal_Iio_upperQuantile_le
      (μ.map fun x => a + b * x) h0 h1
    rw [measureReal_Iio_map_affine_of_pos hb] at hmass
    have hq := (Measure.le_upperQuantile_iff μ h0 h1).mpr hmass
    have := (div_le_iff₀ hb).mp hq
    linarith
  · rw [Measure.le_upperQuantile_iff _ h0 h1, measureReal_Iio_map_affine_of_pos hb]
    simp only [add_sub_cancel_left, mul_div_cancel_left₀ _ hb.ne']
    exact Measure.measureReal_Iio_upperQuantile_le μ h0 h1

/-- A negative affine map carries lower quantiles to reflected upper quantiles. The upper
quantile is necessary when the original cdf has a plateau at level `1 - u`. -/
@[simp]
theorem quantile_map_affine_neg [IsProbabilityMeasure μ] {u : ℝ} (hb : b < 0)
    (h0 : 0 < u) (h1 : u < 1) :
    (μ.map fun x => a + b * x).quantile u = a + b * μ.upperQuantile (1 - u) := by
  have h10 : 0 < 1 - u := sub_pos.mpr h1
  have h11 : 1 - u < 1 := sub_lt_self _ h0
  apply le_antisymm
  · rw [Measure.quantile_le_iff _ h0 h1, cdf_map_affine_of_neg hb]
    have hmass := Measure.measureReal_Iio_upperQuantile_le μ h10 h11
    simp only [add_sub_cancel_left, mul_div_cancel_left₀ _ hb.ne]
    linarith
  · have hcdf := Measure.le_cdf_quantile (μ.map fun x => a + b * x) h1
    rw [cdf_map_affine_of_neg hb] at hcdf
    have hmass : μ.real (Iio (((μ.map fun x => a + b * x).quantile u - a) / b)) ≤ 1 - u :=
      by linarith
    have hq := (Measure.le_upperQuantile_iff μ h10 h11).mpr hmass
    have := (div_le_iff_of_neg hb).mp hq
    linarith

/-- A negative affine map carries upper quantiles to reflected lower quantiles. -/
@[simp]
theorem upperQuantile_map_affine_neg [IsProbabilityMeasure μ] {u : ℝ} (hb : b < 0)
    (h0 : 0 < u) (h1 : u < 1) :
    (μ.map fun x => a + b * x).upperQuantile u = a + b * μ.quantile (1 - u) := by
  have h10 : 0 < 1 - u := sub_pos.mpr h1
  have h11 : 1 - u < 1 := sub_lt_self _ h0
  apply le_antisymm
  · have hmass := Measure.measureReal_Iio_upperQuantile_le
      (μ.map fun x => a + b * x) h0 h1
    rw [measureReal_Iio_map_affine_of_neg hb] at hmass
    have hcdf : 1 - u ≤ cdf μ
        (((μ.map fun x => a + b * x).upperQuantile u - a) / b) := by linarith
    have hq := (Measure.quantile_le_iff μ h10 h11).mpr hcdf
    have := (le_div_iff_of_neg hb).mp hq
    linarith
  · rw [Measure.le_upperQuantile_iff _ h0 h1, measureReal_Iio_map_affine_of_neg hb]
    have hcdf := Measure.le_cdf_quantile μ h11
    simp only [add_sub_cancel_left, mul_div_cancel_left₀ _ hb.ne]
    linarith

/-- The lower quantile of an affine image, including positive, zero, and negative slopes. -/
theorem quantile_map_affine [IsProbabilityMeasure μ] {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    (μ.map fun x => a + b * x).quantile u =
      if 0 < b then a + b * μ.quantile u
      else if b = 0 then a else a + b * μ.upperQuantile (1 - u) := by
  by_cases hb : 0 < b
  · rw [ite_eq_left hb]
    exact quantile_map_affine_pos hb h0 h1
  · by_cases hb0 : b = 0
    · subst b
      simp only [lt_self_iff_false, zero_mul, add_zero, Measure.map_const, measure_univ, one_smul]
      exact Measure.quantile_dirac a h0 h1.le
    · rw [ite_eq_right hb, ite_eq_right hb0]
      exact quantile_map_affine_neg (lt_of_le_of_ne (not_lt.mp hb) hb0) h0 h1

/-- The upper quantile of an affine image, including positive, zero, and negative slopes. -/
theorem upperQuantile_map_affine [IsProbabilityMeasure μ] {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    (μ.map fun x => a + b * x).upperQuantile u =
      if 0 < b then a + b * μ.upperQuantile u
      else if b = 0 then a else a + b * μ.quantile (1 - u) := by
  by_cases hb : 0 < b
  · rw [ite_eq_left hb]
    exact upperQuantile_map_affine_pos hb h0 h1
  · by_cases hb0 : b = 0
    · subst b
      simp only [lt_self_iff_false, zero_mul, add_zero, Measure.map_const, measure_univ, one_smul]
      exact Measure.upperQuantile_dirac a h0.le h1
    · rw [ite_eq_right hb, ite_eq_right hb0]
      exact upperQuantile_map_affine_neg (lt_of_le_of_ne (not_lt.mp hb) hb0) h0 h1

/-! ### Integrability and moments -/

/-- **Absolute moments of an affine image.** For a nonzero slope, the affine image of a finite
measure has a finite `p`-th absolute moment exactly when the original measure does. -/
theorem memLp_id_map_affine_iff [IsFiniteMeasure μ] (hb : b ≠ 0) {p : ℝ≥0∞} :
    MemLp id p (μ.map fun x => a + b * x) ↔ MemLp id p μ := by
  rw [memLp_map_measure_iff aestronglyMeasurable_id (measurable_affine a b).aemeasurable]
  refine ⟨fun h => ?_, fun h => (memLp_const a).add (h.const_mul b)⟩
  have h' := ((memLp_const (-a)).add h).const_mul b⁻¹
  refine h'.ae_eq (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Function.comp_apply, id_eq]
  field_simp
  ring

/-- **Mean of an affine image.** If `μ` is a probability measure with integrable identity, then
the mean of `a + b X` is `a + b E[X]`. -/
theorem integral_id_map_affine [IsProbabilityMeasure μ] (h : Integrable id μ) :
    ∫ x, x ∂(μ.map fun x => a + b * x) = a + b * ∫ x, x ∂μ := by
  have hb : Integrable (fun x => b * x) μ := h.const_mul b
  rw [integral_map (f := fun x => x) (measurable_affine a b).aemeasurable (by fun_prop),
    integral_add (integrable_const a) hb, integral_const, integral_const_mul]
  simp

/-- **Variance of an affine image.** The variance of `a + b X` is `b ^ 2 Var[X]`. No moment
hypothesis is needed: both sides vanish when `X` is not square-integrable and `b ≠ 0`. -/
theorem variance_id_map_affine [IsProbabilityMeasure μ] :
    Var[id; μ.map fun x => a + b * x] = b ^ 2 * Var[id; μ] := by
  rw [variance_id_map (measurable_affine a b).aemeasurable,
    variance_const_add (by fun_prop) a, variance_const_mul]
  rw [Function.id_def]

/-- **Raw moments of an affine image.** If `μ` is a finite measure with finite `n`-th
absolute moment, then the `n`-th moment of `a + b X` is the binomial expansion
`∑ k ≤ n, (n choose k) a ^ (n - k) b ^ k E[X ^ k]`. -/
theorem moment_id_map_affine [IsFiniteMeasure μ] {n : ℕ}
    (h : Integrable (fun x => |x| ^ n) μ) :
    moment id n (μ.map fun x => a + b * x) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b ^ k * moment id k μ := by
  have hk : ∀ k ∈ Finset.range (n + 1), Integrable (fun x : ℝ =>
      (n.choose k : ℝ) * a ^ (n - k) * b ^ k * x ^ k) μ := by
    intro k hk
    have habs : Integrable (fun x : ℝ => ‖x‖ ^ k) μ :=
      integrable_norm_pow_of_le (f := fun x : ℝ => x) (by fun_prop) (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk)) (by simpa only [Real.norm_eq_abs] using h)
    refine Integrable.const_mul ?_ _
    exact habs.mono' (by fun_prop) (ae_of_all _ fun x => by simp [norm_pow])
  simp only [moment_def, Pi.pow_apply, id_eq]
  rw [integral_map (f := fun x => x ^ n) (measurable_affine a b).aemeasurable (by fun_prop)]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hk]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [add_comm a, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Central moments of an affine image.** If `μ` is a probability measure with integrable
identity, then the `n`-th central moment of `a + b X` is `b ^ n` times that of `X`. -/
theorem centralMoment_id_map_affine [IsProbabilityMeasure μ] (h : Integrable id μ) (n : ℕ) :
    centralMoment id n (μ.map fun x => a + b * x) = b ^ n * centralMoment id n μ := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, id_eq]
  rw [integral_id_map_affine h, integral_map (f := fun y : ℝ => (y - (a + b * ∫ x : ℝ, x ∂μ)) ^ n)
    (measurable_affine a b).aemeasurable (by fun_prop), ← integral_const_mul (b ^ n)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [← mul_pow]
  ring

/-! ### Exponential transforms -/

/-- **Moment-generating function of an affine image.** `M_{a + bX}(t) = exp (a t) M_X(b t)`. -/
theorem mgf_id_map_affine (t : ℝ) :
    mgf id (μ.map fun x => a + b * x) t = exp (a * t) * mgf id μ (b * t) := by
  rw [mgf_map (measurable_affine a b).aemeasurable (by fun_prop), Function.id_comp,
    mgf_const_add, mgf_const_mul, mul_comm t a]
  rw [Function.id_def]

/-- **Exponential-integrability domain of an affine image.** `a + b X` has a finite exponential
moment at `t` exactly when `X` has one at `b t`. -/
theorem integrableExpSet_id_map_affine :
    integrableExpSet id (μ.map fun x => a + b * x) =
      (fun t => b * t) ⁻¹' integrableExpSet id μ := by
  ext t
  simp only [integrableExpSet, mem_preimage, mem_ofPred_eq, id_eq]
  rw [integrable_map_measure (by fun_prop) (measurable_affine a b).aemeasurable]
  have hfun : ((fun x : ℝ => exp (t * x)) ∘ fun x => a + b * x) =
      fun x => exp (a * t) * exp (b * t * x) := by
    ext x
    simp only [Function.comp_apply, ← exp_add]
    ring_nf
  rw [hfun, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (exp_pos _).ne')]

/-- **Cumulant-generating function of an affine image.** On the exponential-integrability domain,
`K_{a + bX}(t) = a t + K_X(b t)`. -/
theorem cgf_id_map_affine [NeZero μ] {t : ℝ} (ht : b * t ∈ integrableExpSet id μ) :
    cgf id (μ.map fun x => a + b * x) t = a * t + cgf id μ (b * t) := by
  rw [cgf, cgf, mgf_id_map_affine, log_mul (exp_pos _).ne' (mgf_pos' (NeZero.ne μ) ht).ne',
    log_exp]

/-- **Characteristic function of an affine image.** `φ_{a + bX}(t) = exp (i a t) φ_X(b t)`. -/
theorem charFun_map_affine (t : ℝ) :
    charFun (μ.map fun x => a + b * x) t =
      Complex.exp (a * t * Complex.I) * charFun μ (b * t) := by
  rw [charFun_apply_real, charFun_apply_real,
    integral_map (measurable_affine a b).aemeasurable (by fun_prop), ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [← Complex.exp_add]
  push_cast
  ring_nf

end TauCeti.Probability
