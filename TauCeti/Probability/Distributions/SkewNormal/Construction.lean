/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.SkewNormal.Basic

/-!
# The skew-normal law from two independent Gaussians

Write `φ = gaussianPDFReal 0 1` and `Φ = cdf (gaussianReal 0 1)`, and for a shape `α` put
`δ = α / √(1 + α ^ 2)`, so that `|δ| < 1`. If `Z₁` and `Z₂` are independent standard Gaussians,
then `m + s * (δ * |Z₁| + √(1 - δ ^ 2) * Z₂)` has the skew-normal law with location `m`, scale
`s > 0` and shape `α`.

Conditionally on `Z₁ = z`, the variable `δ * |z| + √(1 - δ ^ 2) * Z₂` is Gaussian with mean
`δ * |z|` and variance `1 - δ ^ 2`. Completing the square exchanges the roles of `y` and `|z|` in
the joint density, `φ(z) * N(δ * |z|, 1 - δ ^ 2)(y) = φ(y) * N(δ * y, 1 - δ ^ 2)(|z|)`, and
integrating out `z` leaves `2 * φ(y) * Φ(δ * y / √(1 - δ ^ 2)) = 2 * φ(y) * Φ(α * y)`, the
standard skew-normal density.

This presentation is the source of the skew-normal moments and transforms: it splits the law into
a scaled half-normal part and an independent Gaussian part.

## Main results

* `map_prod_gaussianReal_eq_skewNormalMeasure` — the product of two standard Gaussian laws,
  pushed forward by `z ↦ m + s * (δ * |z.1| + √(1 - δ ^ 2) * z.2)`, is `skewNormalMeasure m s α`;
* `hasLaw_skewNormalMeasure_of_indepFun` — the same statement for independent standard Gaussian
  random variables;
* `sqrt_one_sub_sq_div_sqrt_one_add_sq` and `sq_div_sqrt_one_add_sq_add_sq_sqrt_one_sub_sq` — the
  coefficients `δ` and `√(1 - δ ^ 2)` are the sine and cosine of `arctan α`.

## References

* A. Azzalini, *A class of distributions which includes the normal ones*, Scandinavian Journal of
  Statistics 12 (1985), 171–178.
* A. Azzalini and A. Capitanio, *The Skew-Normal and Related Families*, Cambridge University
  Press, 2014, Section 2.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {s : ℝ}

/-- The complementary coefficient of the skew-normal construction:
`√(1 - δ ^ 2) = 1 / √(1 + α ^ 2)` for `δ = α / √(1 + α ^ 2)`. These are the sine and cosine of
`arctan α`. -/
theorem sqrt_one_sub_sq_div_sqrt_one_add_sq (α : ℝ) :
    √(1 - (α / √(1 + α ^ 2)) ^ 2) = (√(1 + α ^ 2))⁻¹ := by
  rw [← sin_arctan, ← cos_sq', sqrt_sq (cos_arctan_pos α).le, cos_arctan, one_div]

/-- The two coefficients of the skew-normal construction, `δ = α / √(1 + α ^ 2)` and
`√(1 - δ ^ 2)`, have squares summing to `1`: they are the sine and cosine of `arctan α`. -/
theorem sq_div_sqrt_one_add_sq_add_sq_sqrt_one_sub_sq (α : ℝ) :
    (α / √(1 + α ^ 2)) ^ 2 + √(1 - (α / √(1 + α ^ 2)) ^ 2) ^ 2 = 1 := by
  rw [sqrt_one_sub_sq_div_sqrt_one_add_sq, ← sin_arctan, ← one_div, ← cos_arctan,
    sin_sq_add_cos_sq]

/-- Completing the square: the joint density of `Z₁ = z` and `δ * |z| + √w * Z₂ = y`, for
`δ ^ 2 + w = 1`, is symmetric in `y` and `|z|`. -/
private theorem gaussianPDFReal_mul_gaussianPDFReal_abs {δ : ℝ} {w : ℝ≥0} (hw : w ≠ 0)
    (hδw : δ ^ 2 + w = 1) (y z : ℝ) :
    gaussianPDFReal 0 1 z * gaussianPDFReal (δ * |z|) w y =
      gaussianPDFReal 0 1 y * gaussianPDFReal (δ * y) w |z| := by
  have hw' : (w : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hw
  simp only [gaussianPDFReal, NNReal.coe_one]
  rw [mul_mul_mul_comm, mul_mul_mul_comm _ (exp _), ← exp_add, ← exp_add]
  congr 2
  have hz : |z| ^ 2 = z ^ 2 := sq_abs z
  field_simp
  linear_combination (y ^ 2 - z ^ 2) * hδw + (1 - δ ^ 2) * hz

/-- Integrating out `z` from the joint density of `Z₁ = z` and `δ * |z| + √w * Z₂ = y` leaves
`2 * φ(y) * Φ(δ * y / √w)`. -/
private theorem integral_gaussianPDFReal_mul_gaussianPDFReal_abs {δ : ℝ} {w : ℝ≥0} (hw : w ≠ 0)
    (hδw : δ ^ 2 + w = 1) (y : ℝ) :
    ∫ z, gaussianPDFReal 0 1 z * gaussianPDFReal (δ * |z|) w y =
      2 * gaussianPDFReal 0 1 y * cdf (gaussianReal 0 1) (δ * y / √(w : ℝ)) := by
  simp_rw [gaussianPDFReal_mul_gaussianPDFReal_abs hw hδw y]
  rw [integral_const_mul, integral_comp_abs (f := gaussianPDFReal (δ * y) w),
    integral_Ioi_gaussianPDFReal_eq_cdf _ hw, sub_zero]
  ring

/-- The lower-integral form of `integral_gaussianPDFReal_mul_gaussianPDFReal_abs`. -/
private theorem lintegral_gaussianPDF_mul_gaussianPDF_abs {δ : ℝ} {w : ℝ≥0} (hw : w ≠ 0)
    (hδw : δ ^ 2 + w = 1) (y : ℝ) :
    ∫⁻ z, gaussianPDF 0 1 z * gaussianPDF (δ * |z|) w y =
      ENNReal.ofReal (2 * gaussianPDFReal 0 1 y * cdf (gaussianReal 0 1) (δ * y / √(w : ℝ))) := by
  have hint : Integrable fun z => gaussianPDFReal 0 1 z * gaussianPDFReal (δ * |z|) w y := by
    refine (integrable_gaussianPDFReal 0 1).mul_bdd (c := (√(2 * π * w))⁻¹) ?_ ?_
    · exact (measurable_uncurry_gaussianPDFReal.comp (by fun_prop :
        Measurable fun z : ℝ => (δ * |z|, w, y))).aestronglyMeasurable
    · -- A Gaussian density is bounded by its value at the mean.
      refine ae_of_all _ fun z => ?_
      rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal]
      refine mul_le_of_le_one_right (by positivity) (exp_le_one_iff.mpr ?_)
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  simp_rw [gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun z => mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)),
    integral_gaussianPDFReal_mul_gaussianPDFReal_abs hw hδw]

/-- The standard case of `map_prod_gaussianReal_eq_skewNormalMeasure`: location `0` and
scale `1`. -/
private theorem map_prod_gaussianReal_eq_skewNormalMeasure_zero_one (α : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun z : ℝ × ℝ => α / √(1 + α ^ 2) * |z.1| + √(1 - (α / √(1 + α ^ 2)) ^ 2) * z.2) =
      skewNormalMeasure 0 1 α := by
  have hδc2 := sq_div_sqrt_one_add_sq_add_sq_sqrt_one_sub_sq α
  set δ := α / √(1 + α ^ 2)
  set c := √(1 - δ ^ 2)
  have hα : 0 < √(1 + α ^ 2) := sqrt_pos.mpr (by positivity)
  have hc : c = (√(1 + α ^ 2))⁻¹ := sqrt_one_sub_sq_div_sqrt_one_add_sq α
  have hc0 : 0 < c := hc ▸ inv_pos.mpr hα
  -- The conditional law of the sum given `Z₁ = z` is `N(δ * |z|, w)` with `w = c ^ 2 = 1 - δ ^ 2`.
  set w : ℝ≥0 := ⟨c ^ 2, sq_nonneg c⟩
  have hw : (w : ℝ) = c ^ 2 := rfl
  have hw0 : w ≠ 0 := by
    rw [← NNReal.coe_ne_zero, hw]
    positivity
  have hδw : δ ^ 2 + w = 1 := by rw [hw, hδc2]
  have hδc : δ / √(w : ℝ) = α := by
    rw [hw, sqrt_sq hc0.le, hc, div_inv_eq_mul]
    exact div_mul_cancel₀ α hα.ne'
  have hF : Measurable fun z : ℝ × ℝ => δ * |z.1| + c * z.2 := by fun_prop
  have hfiber (z : ℝ) : (gaussianReal 0 1).map (fun x => δ * |z| + c * x) =
      gaussianReal (δ * |z|) w := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) c
    -- Exhibit the affine map as a composition so that `Measure.map_map` can split it.
    rw [show (fun x => δ * |z| + c * x) = (δ * |z| + ·) ∘ (c * ·) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), h, gaussianReal_map_const_add, mul_zero,
      zero_add, mul_one]
    -- `w` was introduced as the variance that `gaussianReal_map_const_mul` produces.
    rfl
  ext A hA
  rw [Measure.map_apply hF hA, Measure.prod_apply (hF hA), skewNormalMeasure_eq_withDensity,
    withDensity_apply _ hA]
  have hslice (z : ℝ) :
      gaussianReal 0 1 (Prod.mk z ⁻¹' ((fun z : ℝ × ℝ => δ * |z.1| + c * z.2) ⁻¹' A)) =
        ∫⁻ y in A, gaussianPDF (δ * |z|) w y := by
    rw [← gaussianReal_apply _ hw0, ← hfiber z, Measure.map_apply (by fun_prop) hA,
      preimage_preimage]
  simp_rw [hslice]
  have hmeas : Measurable (Function.uncurry fun z y : ℝ => gaussianPDF (δ * |z|) w y) :=
    measurable_uncurry_gaussianPDF.comp (by fun_prop :
      Measurable fun p : ℝ × ℝ => (δ * |p.1|, w, p.2))
  have hmeas' : Measurable fun z => ∫⁻ y in A, gaussianPDF (δ * |z|) w y :=
    hmeas.lintegral_prod_right'
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hmeas']
  simp_rw [Pi.mul_apply, ← lintegral_const_mul' _ _ gaussianPDF_ne_top]
  rw [lintegral_lintegral_swap ((measurable_gaussianPDF 0 1).comp measurable_fst |>.mul hmeas
    |>.aemeasurable)]
  refine setLIntegral_congr_fun hA fun y _ => ?_
  rw [lintegral_gaussianPDF_mul_gaussianPDF_abs hw0 hδw, mul_div_right_comm, hδc,
    skewNormalPDF_of_pos one_pos]
  simp

/-- **The skew-normal law from two independent Gaussians.** For `s > 0` and
`δ = α / √(1 + α ^ 2)`, the product of two standard Gaussian laws pushed forward by
`z ↦ m + s * (δ * |z.1| + √(1 - δ ^ 2) * z.2)` is the skew-normal law with location `m`, scale `s`
and shape `α`. -/
theorem map_prod_gaussianReal_eq_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun z : ℝ × ℝ =>
          m + s * (α / √(1 + α ^ 2) * |z.1| + √(1 - (α / √(1 + α ^ 2)) ^ 2) * z.2)) =
      skewNormalMeasure m s α := by
  -- Exhibit the map as an affine map after the standard construction, for `Measure.map_map`.
  rw [show (fun z : ℝ × ℝ =>
        m + s * (α / √(1 + α ^ 2) * |z.1| + √(1 - (α / √(1 + α ^ 2)) ^ 2) * z.2)) =
      (fun x => m + s * x) ∘
        (fun z : ℝ × ℝ => α / √(1 + α ^ 2) * |z.1| + √(1 - (α / √(1 + α ^ 2)) ^ 2) * z.2) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),
    map_prod_gaussianReal_eq_skewNormalMeasure_zero_one,
    map_affine_skewNormalMeasure 0 1 α hs.ne']
  simp [abs_of_pos hs, hs]

/-- **The skew-normal law from two independent Gaussians**, for random variables: if `Z₁` and
`Z₂` are independent standard Gaussians, `s > 0` and `δ = α / √(1 + α ^ 2)`, then
`m + s * (δ * |Z₁| + √(1 - δ ^ 2) * Z₂)` is skew-normal with location `m`, scale `s` and
shape `α`. -/
theorem hasLaw_skewNormalMeasure_of_indepFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z₁ Z₂ : Ω → ℝ} (h₁ : HasLaw Z₁ (gaussianReal 0 1) P)
    (h₂ : HasLaw Z₂ (gaussianReal 0 1) P) (hindep : Z₁ ⟂ᵢ[P] Z₂) (hs : 0 < s) (m α : ℝ) :
    HasLaw
      (fun ω => m + s * (α / √(1 + α ^ 2) * |Z₁ ω| + √(1 - (α / √(1 + α ^ 2)) ^ 2) * Z₂ ω))
      (skewNormalMeasure m s α) P :=
  have := h₁.isProbabilityMeasure
  (HasLaw.mk (by fun_prop) (map_prod_gaussianReal_eq_skewNormalMeasure hs m α)).fun_comp
    (hindep.hasLaw_prod h₁ h₂)

end Probability

end TauCeti
