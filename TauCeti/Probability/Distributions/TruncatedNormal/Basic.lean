/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.ConditionalProbability
public import TauCeti.Probability.Density
public import TauCeti.Probability.Distributions.Gaussian.Quantile
public import TauCeti.Probability.Distributions.Truncation

/-!
# The truncated normal distribution

`truncatedNormalMeasure m v s` is the Gaussian law `N(m, v)` conditioned on a set `s`, that is
`ProbabilityTheory.cond (gaussianReal m v) s`. The sets of interest are intervals with extended
real bounds `l < r` and any choice of endpoint conventions. The set itself is the parameter, so
those conventions are part of the law; they matter only at the Dirac boundary `v = 0`, where the
truncation is `δ_m` or the zero measure according to whether `m ∈ s`.

At positive variance the Gaussian law has no atoms, so every set between the open and the closed
interval with bounds `l, r : EReal` gives the same truncation. Write `L` and `R` for the
Gaussian masses of `{x | x ≤ l}` and `{x | x ≤ r}`; these are `0` and `1` at the infinite bounds
and `Φ ((l - m) / √v)`, `Φ ((r - m) / √v)` at finite ones, with `Φ` the standard Gaussian cdf.
The truncation then has

* mass `R - L > 0` of the truncation set, and density `gaussianPDFReal m v x / (R - L)` on it;
* the clipped cdf `(min R (max L (cdf (gaussianReal m v) x)) - L) / (R - L)`;
* the quantile `m + √v * z (L + u * (R - L))` at every level `0 < u < 1`, where `z` is the
  standard Gaussian quantile.

The cdf and quantile are the general interval truncation formulas of
`TauCeti.Probability.Distributions.Truncation`, made explicit by the closed-form Gaussian cdf and
quantile.

## Main definitions

* `TauCeti.Probability.truncatedNormalMeasure` — the Gaussian law conditioned on a set;
* `TauCeti.Probability.truncatedNormalPDFReal`, `TauCeti.Probability.truncatedNormalPDF` — its
  real and extended densities.

## Main results

* `TauCeti.Probability.isProbabilityMeasure_truncatedNormalMeasure_iff` — normalization exactly
  when the truncation set has positive Gaussian mass, as it does for every nondegenerate interval
  at positive variance (`TauCeti.Probability.isProbabilityMeasure_truncatedNormalMeasure_of_lt`);
* `TauCeti.Probability.truncatedNormalMeasure_zero_var` — the Dirac boundary `v = 0`;
* `TauCeti.Probability.truncatedNormalMeasure_eq_preimage_Ioc` — endpoint conventions agree at
  positive variance;
* `TauCeti.Probability.truncatedNormalMeasure_eq_withDensity` and the `HasPDF` and Radon–Nikodym
  corollaries;
* `TauCeti.Probability.cdf_truncatedNormalMeasure_eq`,
  `TauCeti.Probability.quantile_truncatedNormalMeasure` — the clipped cdf and the quantile, with
  the finite-bound forms `TauCeti.Probability.cdf_truncatedNormalMeasure_eq_cdf_zero_one` and
  `TauCeti.Probability.quantile_truncatedNormalMeasure_eq_cdf_zero_one`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), Chapter 13.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {m : ℝ} {v : ℝ≥0} {s : Set ℝ} {l r : EReal}

/-- The truncated normal law: the Gaussian law `N(m, v)` conditioned on the set `s`. It is a
probability measure when `s` has positive Gaussian mass, and the zero measure otherwise. -/
def truncatedNormalMeasure (m : ℝ) (v : ℝ≥0) (s : Set ℝ) : Measure ℝ :=
  cond (gaussianReal m v) s

/-- The truncated normal law is the Gaussian law conditioned on the truncation set. -/
theorem truncatedNormalMeasure_def (m : ℝ) (v : ℝ≥0) (s : Set ℝ) :
    truncatedNormalMeasure m v s = cond (gaussianReal m v) s := by
  rw [truncatedNormalMeasure]

/-- Truncating to the whole line recovers the Gaussian law. -/
@[simp]
theorem truncatedNormalMeasure_univ (m : ℝ) (v : ℝ≥0) :
    truncatedNormalMeasure m v univ = gaussianReal m v := by
  rw [truncatedNormalMeasure_def, cond_univ]

/-- The truncated normal law vanishes exactly when the truncation set has Gaussian mass zero. -/
@[simp]
theorem truncatedNormalMeasure_eq_zero_iff :
    truncatedNormalMeasure m v s = 0 ↔ gaussianReal m v s = 0 := by
  simp [truncatedNormalMeasure_def, measure_ne_top]

/-- The truncated normal law is a probability measure when the truncation set has positive
Gaussian mass. -/
theorem isProbabilityMeasure_truncatedNormalMeasure (h : gaussianReal m v s ≠ 0) :
    IsProbabilityMeasure (truncatedNormalMeasure m v s) := by
  rw [truncatedNormalMeasure_def]
  exact cond_isProbabilityMeasure h

/-- The truncated normal law is a probability measure exactly when the truncation set has
positive Gaussian mass. -/
theorem isProbabilityMeasure_truncatedNormalMeasure_iff :
    IsProbabilityMeasure (truncatedNormalMeasure m v s) ↔ gaussianReal m v s ≠ 0 := by
  refine ⟨fun h hs => ?_, isProbabilityMeasure_truncatedNormalMeasure⟩
  rw [truncatedNormalMeasure_eq_zero_iff.2 hs] at h
  exact IsProbabilityMeasure.ne_zero (0 : Measure ℝ) rfl

/-- At the Dirac boundary `v = 0`, the truncated normal law is `δ_m` when the truncation set,
with its endpoint conventions, contains `m`, and the zero measure otherwise. -/
theorem truncatedNormalMeasure_zero_var (m : ℝ) (s : Set ℝ) [Decidable (m ∈ s)] :
    truncatedNormalMeasure m 0 s = if m ∈ s then Measure.dirac m else 0 := by
  rw [truncatedNormalMeasure_def, gaussianReal_zero_var]
  split_ifs with h
  · simp [ProbabilityTheory.cond, restrict_dirac, h]
  · exact cond_eq_zero_of_meas_eq_zero (by simp [h])

/-- At positive variance, the open interval with extended bounds `l < r` has positive Gaussian
mass. -/
theorem gaussianReal_preimage_Ioo_pos (m : ℝ) (hv : v ≠ 0) (hlr : l < r) :
    0 < gaussianReal m v (Real.toEReal ⁻¹' Ioo l r) := by
  have := (gaussianReal_absolutelyContinuous' m hv).isOpenPosMeasure
  obtain ⟨x, hlx, hxr⟩ := EReal.lt_iff_exists_real_btwn.1 hlr
  exact (isOpen_Ioo.preimage continuous_coe_real_ereal).measure_pos _ ⟨x, hlx, hxr⟩

/-- At positive variance, the truncated normal law to any set containing the open interval with
extended bounds `l < r` is a probability measure. -/
theorem isProbabilityMeasure_truncatedNormalMeasure_of_lt (hv : v ≠ 0) (hlr : l < r)
    (hs : Real.toEReal ⁻¹' Ioo l r ⊆ s) :
    IsProbabilityMeasure (truncatedNormalMeasure m v s) :=
  isProbabilityMeasure_truncatedNormalMeasure
    ((gaussianReal_preimage_Ioo_pos m hv hlr).trans_le (measure_mono hs)).ne'

/-- At positive variance, a set between the open and the closed interval with extended bounds
`l, r` agrees with the half-open interval `(l, r]` off a Gaussian-null set: the two candidate
endpoints carry no mass. -/
private theorem ae_eq_preimage_Ioc (hv : v ≠ 0) (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s)
    (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    s =ᵐ[gaussianReal m v] Real.toEReal ⁻¹' Ioc l r := by
  have := nullSingletonClass_gaussianReal (μ := m) hv
  have hnull : gaussianReal m v (Real.toEReal ⁻¹' Icc l r \ Real.toEReal ⁻¹' Ioo l r) = 0 := by
    refine measure_mono_null (t := {l.toReal, r.toReal}) ?_ ((toFinite _).measure_zero _)
    rintro x ⟨⟨hlx, hxr⟩, hx⟩
    by_contra hne
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
    exact hx ⟨hlx.lt_of_ne fun h => hne.1 (by rw [h, EReal.toReal_coe]),
      hxr.lt_of_ne fun h => hne.2 (by rw [← h, EReal.toReal_coe])⟩
  have hopen {t : Set ℝ} (h₁ : Real.toEReal ⁻¹' Ioo l r ⊆ t)
      (h₂ : t ⊆ Real.toEReal ⁻¹' Icc l r) :
      t =ᵐ[gaussianReal m v] Real.toEReal ⁻¹' Ioo l r :=
    (ae_le_set.2 (measure_mono_null (sdiff_subset_sdiff_left h₂) hnull)).antisymm h₁.eventuallyLE
  exact (hopen hs₁ hs₂).trans (hopen (preimage_mono Ioo_subset_Ioc_self)
    (preimage_mono Ioc_subset_Icc_self)).symm

/-- At positive variance the endpoint conventions do not matter: truncating to any set between
the open and the closed interval with extended bounds `l, r` gives the truncation to the
half-open interval `(l, r]`. -/
theorem truncatedNormalMeasure_eq_preimage_Ioc (hv : v ≠ 0)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    truncatedNormalMeasure m v s = truncatedNormalMeasure m v (Real.toEReal ⁻¹' Ioc l r) := by
  rw [truncatedNormalMeasure_def, truncatedNormalMeasure_def]
  exact cond_congr_ae (ae_eq_preimage_Ioc hv hs₁ hs₂)

/-- At positive variance, the Gaussian mass of a set between the open and the closed interval
with extended bounds `l ≤ r` is the difference `R - L` of the masses up to the two bounds. -/
theorem measureReal_gaussianReal_eq_sub (hv : v ≠ 0) (hlr : l ≤ r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    (gaussianReal m v).real s =
      (gaussianReal m v).real (Real.toEReal ⁻¹' Iic r) -
        (gaussianReal m v).real (Real.toEReal ⁻¹' Iic l) := by
  rw [measureReal_congr (ae_eq_preimage_Ioc hv hs₁ hs₂), ← Iic_sdiff_Iic, preimage_sdiff,
    measureReal_sdiff (preimage_mono (Iic_subset_Iic.2 hlr))
      (measurableSet_Iic.preimage measurable_coe_real_ereal)]

/-- At positive variance, the Gaussian mass up to an extended bound is strictly increasing in
the bound. -/
theorem measureReal_gaussianReal_preimage_Iic_lt (hv : v ≠ 0) (hlr : l < r) :
    (gaussianReal m v).real (Real.toEReal ⁻¹' Iic l) <
      (gaussianReal m v).real (Real.toEReal ⁻¹' Iic r) := by
  have hpos : 0 < (gaussianReal m v).real (Real.toEReal ⁻¹' Ioo l r) :=
    ENNReal.toReal_pos (gaussianReal_preimage_Ioo_pos m hv hlr).ne' (measure_ne_top _ _)
  rw [measureReal_gaussianReal_eq_sub hv hlr.le subset_rfl
    (preimage_mono Ioo_subset_Icc_self)] at hpos
  exact sub_pos.1 hpos

/-! ### Density -/

/-- The real density of the truncated normal law: the Gaussian density on the truncation set,
renormalized by the Gaussian mass of that set, and zero off it. -/
def truncatedNormalPDFReal (m : ℝ) (v : ℝ≥0) (s : Set ℝ) (x : ℝ) : ℝ :=
  s.indicator (gaussianPDFReal m v) x / (gaussianReal m v).real s

/-- The extended nonnegative density of the truncated normal law. -/
def truncatedNormalPDF (m : ℝ) (v : ℝ≥0) (s : Set ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (truncatedNormalPDFReal m v s x)

/-- The extended truncated normal density is the coercion of its real counterpart. -/
theorem truncatedNormalPDF_eq_ofReal (m : ℝ) (v : ℝ≥0) (s : Set ℝ) (x : ℝ) :
    truncatedNormalPDF m v s x = ENNReal.ofReal (truncatedNormalPDFReal m v s x) := by
  rw [truncatedNormalPDF]

/-- On the truncation set, the truncated normal density is the renormalized Gaussian density. -/
@[simp]
theorem truncatedNormalPDFReal_of_mem {x : ℝ} (hx : x ∈ s) :
    truncatedNormalPDFReal m v s x = gaussianPDFReal m v x / (gaussianReal m v).real s := by
  rw [truncatedNormalPDFReal, indicator_of_mem hx]

/-- Off the truncation set, the truncated normal density vanishes. -/
@[simp]
theorem truncatedNormalPDFReal_of_notMem {x : ℝ} (hx : x ∉ s) :
    truncatedNormalPDFReal m v s x = 0 := by
  rw [truncatedNormalPDFReal, indicator_of_notMem hx, zero_div]

/-- The truncated normal density is nonnegative. -/
theorem truncatedNormalPDFReal_nonneg (m : ℝ) (v : ℝ≥0) (s : Set ℝ) (x : ℝ) :
    0 ≤ truncatedNormalPDFReal m v s x :=
  div_nonneg (indicator_nonneg (fun y _ => gaussianPDFReal_nonneg m v y) x) measureReal_nonneg

/-- Converting the extended density to a real number recovers the real density. -/
@[simp]
theorem toReal_truncatedNormalPDF (m : ℝ) (v : ℝ≥0) (s : Set ℝ) (x : ℝ) :
    (truncatedNormalPDF m v s x).toReal = truncatedNormalPDFReal m v s x := by
  rw [truncatedNormalPDF_eq_ofReal, ENNReal.toReal_ofReal (truncatedNormalPDFReal_nonneg m v s x)]

/-- The real truncated normal density is measurable for a measurable truncation set. -/
@[fun_prop]
theorem measurable_truncatedNormalPDFReal (m : ℝ) (v : ℝ≥0) (hs : MeasurableSet s) :
    Measurable (truncatedNormalPDFReal m v s) :=
  ((measurable_gaussianPDFReal m v).indicator hs).div_const _

/-- The extended truncated normal density is measurable for a measurable truncation set. -/
@[fun_prop]
theorem measurable_truncatedNormalPDF (m : ℝ) (v : ℝ≥0) (hs : MeasurableSet s) :
    Measurable (truncatedNormalPDF m v s) :=
  (measurable_truncatedNormalPDFReal m v hs).ennreal_ofReal

/-- At positive variance, the truncated normal law to a measurable set is Lebesgue measure
weighted by its density. This includes truncation sets of Gaussian mass zero, where both sides
vanish. -/
theorem truncatedNormalMeasure_eq_withDensity (m : ℝ) (hv : v ≠ 0) (hs : MeasurableSet s) :
    truncatedNormalMeasure m v s = volume.withDensity (truncatedNormalPDF m v s) := by
  by_cases h0 : gaussianReal m v s = 0
  · have hpdf : truncatedNormalPDF m v s = 0 := by
      ext x
      simp [truncatedNormalPDF, truncatedNormalPDFReal, measureReal_def, h0]
    rw [truncatedNormalMeasure_eq_zero_iff.2 h0, hpdf, withDensity_zero]
  · have hc : 0 < (gaussianReal m v).real s := ENNReal.toReal_pos h0 (measure_ne_top _ _)
    have hpdf : truncatedNormalPDF m v s =
        s.indicator (ENNReal.ofReal ((gaussianReal m v).real s)⁻¹ • gaussianPDF m v) := by
      ext x
      by_cases hx : x ∈ s
      · rw [truncatedNormalPDF_eq_ofReal, truncatedNormalPDFReal_of_mem hx, indicator_of_mem hx,
          Pi.smul_apply, smul_eq_mul, gaussianPDF, div_eq_inv_mul,
          ENNReal.ofReal_mul (inv_nonneg.2 hc.le)]
      · simp [truncatedNormalPDF, hx]
    have hinv : ENNReal.ofReal ((gaussianReal m v).real s)⁻¹ = (gaussianReal m v s)⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hc, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [hpdf, withDensity_indicator hs, withDensity_smul _ (measurable_gaussianPDF m v), hinv,
      ← restrict_withDensity hs, ← gaussianReal_of_var_ne_zero m hv, truncatedNormalMeasure_def,
      ProbabilityTheory.cond]

/-- At positive variance, a random variable with a truncated normal law to a measurable set has a
density. -/
theorem hasPDF_of_hasLaw_truncatedNormalMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hv : v ≠ 0) (hs : MeasurableSet s)
    (hX : HasLaw X (truncatedNormalMeasure m v s) P) : HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_truncatedNormalPDF m v hs).aemeasurable
    (by rwa [truncatedNormalMeasure_eq_withDensity m hv hs] at hX)

/-- At positive variance, the canonical density of a truncated normal random variable equals its
named density almost everywhere. -/
theorem pdf_eq_truncatedNormalPDF_of_hasLaw_truncatedNormalMeasure {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} (hv : v ≠ 0) (hs : MeasurableSet s)
    (hX : HasLaw X (truncatedNormalMeasure m v s) P) :
    pdf X P volume =ᵐ[volume] truncatedNormalPDF m v s :=
  pdf_eq_of_hasLaw_withDensity (measurable_truncatedNormalPDF m v hs).aemeasurable
    (by rwa [truncatedNormalMeasure_eq_withDensity m hv hs] at hX)

/-- At positive variance, the Radon–Nikodym derivative of the truncated normal law to a measurable
set is its named density. -/
theorem rnDeriv_truncatedNormalMeasure (m : ℝ) (hv : v ≠ 0) (hs : MeasurableSet s) :
    (truncatedNormalMeasure m v s).rnDeriv volume =ᵐ[volume] truncatedNormalPDF m v s := by
  rw [truncatedNormalMeasure_eq_withDensity m hv hs]
  exact Measure.rnDeriv_withDensity volume (measurable_truncatedNormalPDF m v hs)

/-! ### Cumulative distribution function and quantile -/

/-- At positive variance, the truncated normal law is the Gaussian law conditioned between the
lower cuts at the two extended bounds, the form taken by the general truncation formulas. -/
private theorem truncatedNormalMeasure_eq_cond_sdiff (hv : v ≠ 0)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    truncatedNormalMeasure m v s =
      cond (gaussianReal m v) (Real.toEReal ⁻¹' Iic r \ Real.toEReal ⁻¹' Iic l) := by
  rw [truncatedNormalMeasure_eq_preimage_Ioc hv hs₁ hs₂, truncatedNormalMeasure_def,
    ← preimage_sdiff, Iic_sdiff_Iic]

/-- At positive variance, the cdf of a normal law truncated to an interval with extended bounds
`l < r` clips the Gaussian cdf between the masses `L` and `R` up to the two bounds, and rescales
it by `R - L`. -/
theorem cdf_truncatedNormalMeasure_eq (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) (x : ℝ) :
    cdf (truncatedNormalMeasure m v s) x =
      (min ((gaussianReal m v).real (Real.toEReal ⁻¹' Iic r))
          (max ((gaussianReal m v).real (Real.toEReal ⁻¹' Iic l)) (cdf (gaussianReal m v) x)) -
        (gaussianReal m v).real (Real.toEReal ⁻¹' Iic l)) /
      ((gaussianReal m v).real (Real.toEReal ⁻¹' Iic r) -
        (gaussianReal m v).real (Real.toEReal ⁻¹' Iic l)) := by
  rw [truncatedNormalMeasure_eq_cond_sdiff hv hs₁ hs₂]
  exact Measure.cdf_cond_sdiff _ ((IsLowerSet.Iic l).preimage EReal.coe_strictMono.monotone)
    ((IsLowerSet.Iic r).preimage EReal.coe_strictMono.monotone)
    (measurableSet_Iic.preimage measurable_coe_real_ereal)
    (measurableSet_Iic.preimage measurable_coe_real_ereal)
    (measureReal_gaussianReal_preimage_Iic_lt hv hlr) x

/-- At positive variance and every level `0 < u < 1`, the quantile of a normal law truncated to
an interval with extended bounds `l < r` is `m + √v * z (L + u * (R - L))`, where `z` is the
standard Gaussian quantile and `L`, `R` are the Gaussian masses up to the two bounds. -/
theorem quantile_truncatedNormalMeasure (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) {u : ℝ}
    (hu : u ∈ Ioo 0 1) :
    (truncatedNormalMeasure m v s).quantile u =
      m + √(v : ℝ) * (gaussianReal 0 1).quantile
        ((gaussianReal m v).real (Real.toEReal ⁻¹' Iic l) +
          u * ((gaussianReal m v).real (Real.toEReal ⁻¹' Iic r) -
            (gaussianReal m v).real (Real.toEReal ⁻¹' Iic l))) := by
  have hLR := measureReal_gaussianReal_preimage_Iic_lt (m := m) hv hlr
  have hL : 0 ≤ (gaussianReal m v).real (Real.toEReal ⁻¹' Iic l) := measureReal_nonneg
  have hR : (gaussianReal m v).real (Real.toEReal ⁻¹' Iic r) ≤ 1 := measureReal_le_one
  rw [truncatedNormalMeasure_eq_cond_sdiff hv hs₁ hs₂,
    Measure.quantile_cond_sdiff _ ((IsLowerSet.Iic l).preimage EReal.coe_strictMono.monotone)
      ((IsLowerSet.Iic r).preimage EReal.coe_strictMono.monotone)
      (measurableSet_Iic.preimage measurable_coe_real_ereal)
      (measurableSet_Iic.preimage measurable_coe_real_ereal) hLR hu]
  refine quantile_gaussianReal_eq_add_mul m v ⟨?_, ?_⟩
  · nlinarith [hu.1]
  · nlinarith [hu.2]

/-- The clipped cdf of a normal law of positive variance truncated to an interval with finite
bounds `l < r`, in terms of the standard Gaussian cdf `Φ`: with `α = (l - m) / √v` and
`β = (r - m) / √v`, it is `(min (Φ β) (max (Φ α) (Φ ((x - m) / √v))) - Φ α) / (Φ β - Φ α)`. -/
theorem cdf_truncatedNormalMeasure_eq_cdf_zero_one {l r : ℝ} (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Ioo l r ⊆ s) (hs₂ : s ⊆ Icc l r) (x : ℝ) :
    cdf (truncatedNormalMeasure m v s) x =
      (min (cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ)))
          (max (cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ)))
            (cdf (gaussianReal 0 1) ((x - m) / √(v : ℝ)))) -
        cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ))) /
      (cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ)) -
        cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ))) := by
  rw [cdf_truncatedNormalMeasure_eq (l := l) (r := r) hv (EReal.coe_lt_coe_iff.2 hlr)
      (by rwa [EReal.preimage_coe_Ioo]) (by rwa [EReal.preimage_coe_Icc]),
    EReal.preimage_coe_Iic, EReal.preimage_coe_Iic, ← cdf_eq_real, ← cdf_eq_real,
    cdf_gaussianReal_eq_cdf_zero_one m hv, cdf_gaussianReal_eq_cdf_zero_one m hv,
    cdf_gaussianReal_eq_cdf_zero_one m hv]

/-- The quantile of a normal law of positive variance truncated to an interval with finite bounds
`l < r`: with `α = (l - m) / √v`, `β = (r - m) / √v` and `Z = Φ β - Φ α`, it is
`m + √v * z (Φ α + u * Z)` at every level `0 < u < 1`. -/
theorem quantile_truncatedNormalMeasure_eq_cdf_zero_one {l r : ℝ} (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Ioo l r ⊆ s) (hs₂ : s ⊆ Icc l r) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (truncatedNormalMeasure m v s).quantile u =
      m + √(v : ℝ) * (gaussianReal 0 1).quantile
        (cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ)) +
          u * (cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ)) -
            cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ)))) := by
  rw [quantile_truncatedNormalMeasure (l := l) (r := r) hv (EReal.coe_lt_coe_iff.2 hlr)
      (by rwa [EReal.preimage_coe_Ioo]) (by rwa [EReal.preimage_coe_Icc]) hu,
    EReal.preimage_coe_Iic, EReal.preimage_coe_Iic, ← cdf_eq_real, ← cdf_eq_real,
    cdf_gaussianReal_eq_cdf_zero_one m hv, cdf_gaussianReal_eq_cdf_zero_one m hv]

end TauCeti.Probability
