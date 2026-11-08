/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FoldedNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Cdf
public import TauCeti.Probability.Distributions.NoncentralChi.Quantile
import TauCeti.Probability.Cdf.Density
import TauCeti.Probability.Distributions.Affine

/-!
# Cumulative distribution function and quantiles of folded normal laws

At positive scale `s`, the cumulative distribution function of `foldedNormalMeasure m s` vanishes on
`(-∞, 0]` and equals the Gaussian mass of `[-x, x]` for `0 ≤ x`:
`cdf (foldedNormalMeasure m s) x = Φ ((x - m) / s) + Φ ((x + m) / s) - 1`, or in error-function form
`(erf ((x - m) / (√2 * s)) + erf ((x + m) / (√2 * s))) / 2`, where `Φ = cdf (gaussianReal 0 1)`.
It is continuous on `ℝ`, strictly increasing on `[0, ∞)`, and differentiable away from the kink at
zero with derivative `foldedNormalPDFReal m s x`.

Because `foldedNormalMeasure m s` has no atom at zero, its interior quantiles on `Ioo 0 1` are
strictly positive and are characterized as the unique positive roots of this elementary Gaussian
cdf. They are strictly increasing and continuous on `Ioo 0 1`, scale linearly under positive
rescaling, specialize at `m = 0` to `s * Φ⁻¹ ((1 + u) / 2)`, and tend to `0` at `0⁺` and `⊤` at
`1⁻`.

## References

* F. C. Leone, L. S. Nelson, R. B. Nottingham, *The folded normal distribution*, Technometrics 3
  (1961), 543–550.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, second
  edition, Wiley, 1994, chapter 13.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {m s b u x : ℝ}

/-! ### Elementary Gaussian cumulative distribution function -/

/-- On `[0, ∞)` at positive scale, the folded normal cdf is the difference of standard Gaussian cdf
values at `(x - m) / s` and `(-x - m) / s`. -/
theorem cdf_foldedNormalMeasure_eq_sub_of_nonneg (hs : 0 < s) (hx : 0 ≤ x) :
    cdf (foldedNormalMeasure m s) x =
      cdf (gaussianReal 0 1) ((x - m) / s) - cdf (gaussianReal 0 1) ((-x - m) / s) := by
  have hv : (s ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (pow_pos hs 2)).ne'
  have := nullSingletonClass_gaussianReal (μ := m) hv
  rw [foldedNormalMeasure_of_scale_pos hs, Measure.cdf_map_abs_of_nonneg _ hx,
    measureReal_congr (Iio_ae_eq_Iic (a := -x)), ← cdf_eq_real,
    cdf_gaussianReal_eq_cdf_zero_one m hv x, cdf_gaussianReal_eq_cdf_zero_one m hv (-x),
    coe_toNNReal _ (sq_nonneg s), sqrt_sq hs.le]

/-- On `[0, ∞)` at positive scale, the folded normal cdf is
`Φ ((x - m) / s) + Φ ((x + m) / s) - 1`, where `Φ = cdf (gaussianReal 0 1)`. -/
theorem cdf_foldedNormalMeasure_of_nonneg (hs : 0 < s) (hx : 0 ≤ x) :
    cdf (foldedNormalMeasure m s) x =
      cdf (gaussianReal 0 1) ((x - m) / s) + cdf (gaussianReal 0 1) ((x + m) / s) - 1 := by
  have hneg : (-x - m) / s = -((x + m) / s) := by ring
  rw [cdf_foldedNormalMeasure_eq_sub_of_nonneg hs hx, hneg, cdf_gaussianReal_zero_one_neg]
  ring

/-- Error-function form of the folded normal cdf on `[0, ∞)` at positive scale. -/
theorem cdf_foldedNormalMeasure_eq_erf_of_nonneg (hs : 0 < s) (hx : 0 ≤ x) :
    cdf (foldedNormalMeasure m s) x =
      (Real.erf ((x - m) / (√2 * s)) + Real.erf ((x + m) / (√2 * s))) / 2 := by
  rw [cdf_foldedNormalMeasure_of_nonneg hs hx, cdf_gaussianReal_zero_one,
    cdf_gaussianReal_zero_one, div_div, div_div, mul_comm s √2]
  ring

/-- Below zero, the folded normal cdf at positive scale vanishes. -/
@[simp]
theorem cdf_foldedNormalMeasure_of_neg (hs : 0 < s) (hx : x < 0) :
    cdf (foldedNormalMeasure m s) x = 0 := by
  rw [foldedNormalMeasure_of_scale_pos hs, Measure.cdf_map_abs_of_neg _ hx]

/-- Piecewise elementary Gaussian formula for `cdf (foldedNormalMeasure m s)` across all `ℝ`. -/
theorem cdf_foldedNormalMeasure_eq (hs : 0 < s) (x : ℝ) :
    cdf (foldedNormalMeasure m s) x =
      if x < 0 then 0
      else cdf (gaussianReal 0 1) ((x - m) / s) + cdf (gaussianReal 0 1) ((x + m) / s) - 1 := by
  split_ifs with hx
  · exact cdf_foldedNormalMeasure_of_neg hs hx
  · exact cdf_foldedNormalMeasure_of_nonneg hs (not_lt.mp hx)

/-- At zero, the folded normal cdf at positive scale vanishes. -/
@[simp]
theorem cdf_foldedNormalMeasure_zero (hs : 0 < s) :
    cdf (foldedNormalMeasure m s) 0 = 0 := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure, cdf_noncentralChiMeasure_zero zero_le_one hs,
    ite_eq_right one_ne_zero]

/-- At positive scale, the folded normal cdf is continuous on all of `ℝ`. -/
theorem continuous_cdf_foldedNormalMeasure (hs : 0 < s) :
    Continuous (cdf (foldedNormalMeasure m s)) := by
  let _ := isProbabilityMeasure_foldedNormalMeasure m hs
  exact Measure.continuous_cdf_of_noAtoms _

/-- At positive scale, the folded normal cdf is strictly increasing on `[0, ∞)`. -/
theorem strictMonoOn_cdf_foldedNormalMeasure (hs : 0 < s) :
    StrictMonoOn (cdf (foldedNormalMeasure m s)) (Ici 0) := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  exact strictMonoOn_cdf_noncentralChiMeasure zero_le_one hs (Or.inl one_ne_zero)

/-- At positive scale, the folded normal cdf is strictly positive if and only if `0 < x`. -/
theorem cdf_foldedNormalMeasure_pos_iff (hs : 0 < s) :
    0 < cdf (foldedNormalMeasure m s) x ↔ 0 < x := by
  let _ := isProbabilityMeasure_foldedNormalMeasure m hs
  constructor
  · intro hpos
    by_contra hx
    rcases lt_or_eq_of_le (not_lt.mp hx) with hlt | rfl
    · exact (cdf_foldedNormalMeasure_of_neg hs hlt ▸ hpos).false
    · exact (cdf_foldedNormalMeasure_zero (m := m) hs ▸ hpos).false
  · intro hx
    simpa [cdf_foldedNormalMeasure_zero (m := m) hs] using
      strictMonoOn_cdf_foldedNormalMeasure (m := m) hs (le_refl 0) hx.le hx

/-- At positive scale, the folded normal cdf is strictly less than `1` everywhere on `ℝ`. -/
theorem cdf_foldedNormalMeasure_lt_one (hs : 0 < s) (x : ℝ) :
    cdf (foldedNormalMeasure m s) x < 1 :=
  Measure.cdf_lt_one_of_strictMonoOn_Ici _ (strictMonoOn_cdf_foldedNormalMeasure hs) x

/-- Away from the boundary point `0`, the folded normal cdf has derivative `foldedNormalPDFReal`. -/
theorem hasDerivAt_cdf_foldedNormalMeasure (hs : 0 < s) (hx : x ≠ 0) :
    HasDerivAt (cdf (foldedNormalMeasure m s)) (foldedNormalPDFReal m s x) x := by
  let _ := isProbabilityMeasure_foldedNormalMeasure m hs
  have hdens : foldedNormalMeasure m s =
      volume.withDensity (fun t ↦ ENNReal.ofReal (foldedNormalPDFReal m s t)) := by
    rw [foldedNormalMeasure_eq_withDensity, funext (foldedNormalPDF_eq_ofReal m s)]
  refine hasDerivAt_cdf_of_eq_withDensity hdens
    (measurable_foldedNormalPDFReal m s).aemeasurable
    (ae_of_all _ (foldedNormalPDFReal_nonneg m s)) ?_
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ (0 : ℝ)) x).congr ?_
    filter_upwards [Iio_mem_nhds hlt] with y (hy : y < 0)
    exact (foldedNormalPDFReal_of_nonpos hy.le).symm
  · exact (continuousOn_foldedNormalPDFReal m s).continuousAt (Ioi_mem_nhds hgt)

/-! ### Quantiles -/

/-- The folded normal quantile takes the junk value `0` at levels outside `(0, 1)`. -/
@[simp]
theorem quantile_foldedNormalMeasure_of_notMem_Ioo (hu : u ∉ Ioo 0 1) :
    (foldedNormalMeasure m s).quantile u = 0 := by
  by_cases hs : 0 < s
  · by_cases hu0 : u ≤ 0
    · exact Measure.quantile_of_nonpos _ hu0
    · have hu1 : 1 ≤ u := not_lt.mp fun h ↦ hu ⟨not_le.mp hu0, h⟩
      have : {x : ℝ | u ≤ cdf (foldedNormalMeasure m s) x} = ∅ :=
        eq_empty_of_forall_notMem fun x hx ↦
          (cdf_foldedNormalMeasure_lt_one hs x).not_ge (hu1.trans hx)
      rw [Measure.quantile_def, this, Real.sInf_empty]
  · rw [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs), Measure.quantile_zero]

/-- Nonnegative scaling multiplies folded normal quantiles by the scale factor, including on the
nonpositive-scale zero branch. -/
theorem quantile_foldedNormalMeasure_const_mul (hb : 0 ≤ b) (m s : ℝ) :
    (foldedNormalMeasure (b * m) (b * s)).quantile u =
      b * (foldedNormalMeasure m s).quantile u := by
  rcases hb.eq_or_lt with rfl | hb
  · simp
  by_cases hs : 0 < s
  · by_cases hu : u ∈ Ioo 0 1
    · let _ := isProbabilityMeasure_foldedNormalMeasure m hs
      rw [← foldedNormalMeasure_map_const_mul hb]
      simpa only [zero_add] using
        quantile_map_affine_pos (μ := foldedNormalMeasure m s) (a := 0) hb hu.1 hu.2
    · rw [quantile_foldedNormalMeasure_of_notMem_Ioo hu,
        quantile_foldedNormalMeasure_of_notMem_Ioo hu, mul_zero]
  · have hbs : b * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb.le (not_lt.mp hs)
    simp [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs),
      foldedNormalMeasure_of_scale_nonpos hbs]

/-- At zero location parameter and positive scale, the interior folded normal quantile is `s` times
the standard Gaussian quantile at level `(1 + u) / 2`. -/
theorem quantile_foldedNormalMeasure_zero_loc (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (foldedNormalMeasure 0 s).quantile u = s * (gaussianReal 0 1).quantile ((1 + u) / 2) := by
  have : (gaussianReal 0 1).IsNegInvariant :=
    ⟨by simpa only [Measure.neg_def, neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))⟩
  have h1 : foldedNormalMeasure 0 1 = (gaussianReal 0 1).map (|·|) := by
    simpa using foldedNormalMeasure_of_scale_pos (m := 0) one_pos
  have hscale := quantile_foldedNormalMeasure_const_mul hs.le 0 1 (u := u)
  simp only [mul_zero, mul_one] at hscale
  rw [hscale, h1, Measure.quantile_map_abs _ hu.1]

/-- Interior quantiles of a valid folded normal law are strictly positive. -/
theorem quantile_foldedNormalMeasure_pos (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    0 < (foldedNormalMeasure m s).quantile u := by
  have hcut : (if (1 : ℝ) = 0 then exp (-(‖m / s‖₊ : ℝ) ^ 2 / 2) else 0) < u := by
    simpa [one_ne_zero] using hu.1
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  exact ((quantile_noncentralChiMeasure_eq_iff zero_le_one hs hu hcut).mp rfl).1

/-- For `u ∈ Ioo 0 1`, the folded normal quantile is the unique positive root of the folded normal
cdf. -/
theorem quantile_foldedNormalMeasure_eq_iff (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (foldedNormalMeasure m s).quantile u = x ↔
      0 < x ∧ cdf (foldedNormalMeasure m s) x = u := by
  have hcut : (if (1 : ℝ) = 0 then exp (-(‖m / s‖₊ : ℝ) ^ 2 / 2) else 0) < u := by
    simpa [one_ne_zero] using hu.1
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  exact quantile_noncentralChiMeasure_eq_iff zero_le_one hs hu hcut

/-- Explicit root characterization of the interior folded normal quantile in terms of the standard
Gaussian cdf `Φ = cdf (gaussianReal 0 1)`. -/
theorem quantile_foldedNormalMeasure_eq_iff_cdf_zero_one (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (foldedNormalMeasure m s).quantile u = x ↔
      0 < x ∧
        cdf (gaussianReal 0 1) ((x - m) / s) + cdf (gaussianReal 0 1) ((x + m) / s) - 1 = u := by
  rw [quantile_foldedNormalMeasure_eq_iff hs hu]
  refine and_congr_right fun hx ↦ ?_
  rw [cdf_foldedNormalMeasure_of_nonneg hs hx.le]

/-- Evaluating the folded normal cdf at an interior quantile recovers the level `u`. -/
@[simp]
theorem cdf_quantile_foldedNormalMeasure (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    cdf (foldedNormalMeasure m s) ((foldedNormalMeasure m s).quantile u) = u :=
  ((quantile_foldedNormalMeasure_eq_iff hs hu).mp rfl).2

/-- Evaluating the folded normal quantile at the cdf of a positive point `x` recovers `x`. -/
@[simp]
theorem quantile_cdf_foldedNormalMeasure (hs : 0 < s) (hx : 0 < x) :
    (foldedNormalMeasure m s).quantile (cdf (foldedNormalMeasure m s) x) = x := by
  have hu : cdf (foldedNormalMeasure m s) x ∈ Ioo 0 1 :=
    ⟨(cdf_foldedNormalMeasure_pos_iff hs).mpr hx, cdf_foldedNormalMeasure_lt_one hs x⟩
  exact (quantile_foldedNormalMeasure_eq_iff hs hu).mpr ⟨hx, rfl⟩

/-- The folded normal quantile function is strictly increasing on `Ioo 0 1`. -/
theorem strictMonoOn_quantile_foldedNormalMeasure (hs : 0 < s) :
    StrictMonoOn (foldedNormalMeasure m s).quantile (Ioo 0 1) := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  simpa [one_ne_zero] using
    strictMonoOn_quantile_noncentralChiMeasure (δ := ‖m / s‖₊) zero_le_one hs

/-- The folded normal quantile function is continuous on `Ioo 0 1`. -/
theorem continuousOn_quantile_foldedNormalMeasure (hs : 0 < s) :
    ContinuousOn (foldedNormalMeasure m s).quantile (Ioo 0 1) := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  exact continuousOn_quantile_noncentralChiMeasure zero_le_one hs

/-- As `u → 0⁺`, folded normal quantiles tend to `0`. -/
theorem tendsto_quantile_foldedNormalMeasure_nhdsGT_zero (hs : 0 < s) :
    Tendsto (fun u ↦ ((foldedNormalMeasure m s).quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  exact tendsto_quantile_noncentralChiMeasure_nhdsGT_zero zero_le_one hs

/-- As `u → 1⁻`, folded normal quantiles tend to `⊤`. -/
theorem tendsto_quantile_foldedNormalMeasure_nhdsLT_one (hs : 0 < s) :
    Tendsto (fun u ↦ ((foldedNormalMeasure m s).quantile u : EReal)) (𝓝[<] 1) (𝓝 ⊤) := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure]
  simpa [one_ne_zero] using
    tendsto_quantile_noncentralChiMeasure_nhdsLT_one (δ := ‖m / s‖₊) zero_le_one hs

end TauCeti.Probability
