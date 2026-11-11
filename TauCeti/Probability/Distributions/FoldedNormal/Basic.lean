/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Basic
public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.NoncentralChi.PDF
public import TauCeti.MeasureTheory.Measure.Typeclasses.Probability
import TauCeti.Probability.Distributions.Chi.Gaussian
import TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Density

/-!
# Folded normal distributions

For a real Gaussian variable `X` with mean `m` and positive standard deviation `s`, the magnitude
`|X|` has the folded normal law `foldedNormalMeasure m s`. Nonpositive scales are totalized to the
zero measure so that the Lebesgue density identity, the central half-normal specialization, and the
identification with the degree-one noncentral chi family hold across all real parameter pairs.

On the positive half-line and at positive scale, folding adds the two reflected Gaussian branches:
`foldedNormalPDFReal m s x = (φ ((x - m) / s) + φ ((x + m) / s)) / s`, which factors as the
hyperbolic-cosine kernel
`√(2 / π) / s * exp (-(x ^ 2 + m ^ 2) / (2 * s ^ 2)) * cosh (m * x / s ^ 2)`.
Reversing the sign of `m` leaves the law unchanged, setting `m = 0` recovers the half-normal law
`chiMeasure 1 s`, and rescaling `X` by `b > 0` sends `(m, s)` to `(b * m, b * s)`. Equivalently,
`foldedNormalMeasure m s` is `noncentralChiMeasure 1 ‖m / s‖₊ s`.

Within the positive-scale regime the family depends jointly weakly continuously on `(m, s)`, and as
`s → 0⁺` it converges weakly to the point mass `Measure.dirac |m|`.

## Main definitions

* `TauCeti.Probability.foldedNormalMeasure`: the folded normal law on `ℝ` with location parameter
  `m` and scale `s`, equal to `(gaussianReal m (s ^ 2).toNNReal).map (|·|)` for `0 < s` and `0` for
  `s ≤ 0`.
* `TauCeti.Probability.foldedNormalPDFReal` and `TauCeti.Probability.foldedNormalPDF`: the real and
  `ℝ≥0∞`-valued Lebesgue densities on `(0, ∞)`.

## Main results

* `TauCeti.Probability.gaussianReal_map_abs_eq_foldedNormalMeasure`: folding `gaussianReal m v` for
  `v ≠ 0` gives `foldedNormalMeasure m √v`.
* `TauCeti.Probability.foldedNormalMeasure_eq_noncentralChiMeasure` and
  `TauCeti.Probability.noncentralChiMeasure_one`: reciprocal identifications between folded normal
  laws and degree-one noncentral chi laws.
* `TauCeti.Probability.foldedNormalMeasure_eq_withDensity`: `foldedNormalMeasure m s` is Lebesgue
  measure weighted by `foldedNormalPDF m s` for all `(m, s)`.
* `TauCeti.Probability.foldedNormalMeasure_map_const_mul`: positive scaling multiplies both `m` and
  `s`.
* `TauCeti.Probability.continuous_foldedNormalMeasure` and
  `TauCeti.Probability.tendsto_foldedNormalMeasure_nhdsGT_zero_dirac`: joint weak continuity at
  positive scale and the small-scale Dirac limit at `|m|`.

## References

* F. C. Leone, L. S. Nelson, R. B. Nottingham, *The folded normal distribution*, Technometrics 3
  (1961), 543–550.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, second
  edition, Wiley, 1994, chapter 13, and vol. 2, second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {m s b x : ℝ}

/-- The folded normal law with location parameter `m` and scale `s`: the distribution of `|X|` for
`X ∼ N(m, s ^ 2)` when `0 < s`, and the zero measure when `s ≤ 0`. -/
def foldedNormalMeasure (m s : ℝ) : Measure ℝ :=
  if 0 < s then (gaussianReal m (s ^ 2).toNNReal).map (|·|) else 0

/-- At positive scale, `foldedNormalMeasure m s` is the pushforward of `gaussianReal m (s ^ 2)` by
absolute value. -/
theorem foldedNormalMeasure_of_scale_pos (hs : 0 < s) :
    foldedNormalMeasure m s = (gaussianReal m (s ^ 2).toNNReal).map (|·|) := by
  rw [foldedNormalMeasure, ite_eq_left hs]

/-- Nonpositive scale gives the zero measure. -/
@[simp]
theorem foldedNormalMeasure_of_scale_nonpos (hs : s ≤ 0) :
    foldedNormalMeasure m s = 0 := by
  rw [foldedNormalMeasure, ite_eq_right (not_lt.mpr hs)]

/-- Positive scale gives a probability measure. -/
theorem isProbabilityMeasure_foldedNormalMeasure (m : ℝ) (hs : 0 < s) :
    IsProbabilityMeasure (foldedNormalMeasure m s) := by
  rw [foldedNormalMeasure_of_scale_pos hs]
  infer_instance

/-- The folded normal measure is a probability measure if and only if its scale is positive. -/
@[simp]
theorem isProbabilityMeasure_foldedNormalMeasure_iff :
    IsProbabilityMeasure (foldedNormalMeasure m s) ↔ 0 < s := by
  refine ⟨fun hp ↦ ?_, isProbabilityMeasure_foldedNormalMeasure m⟩
  by_contra hs
  rw [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs)] at hp
  exact not_isProbabilityMeasure_zero hp

/-- Folding a real Gaussian measure with nonzero variance `v` yields the folded normal law with
scale `√v`. -/
theorem gaussianReal_map_abs_eq_foldedNormalMeasure (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal m v).map (|·|) = foldedNormalMeasure m √(v : ℝ) := by
  have hs : 0 < √(v : ℝ) := sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  rw [foldedNormalMeasure_of_scale_pos hs]
  congr 2
  apply NNReal.eq
  rw [coe_toNNReal _ (sq_nonneg _), sq_sqrt v.coe_nonneg]

/-- Negating the location parameter leaves the folded normal law unchanged. -/
@[simp]
theorem foldedNormalMeasure_neg_loc (m s : ℝ) :
    foldedNormalMeasure (-m) s = foldedNormalMeasure m s := by
  by_cases hs : 0 < s
  · rw [foldedNormalMeasure_of_scale_pos hs, foldedNormalMeasure_of_scale_pos hs,
      ← gaussianReal_map_neg, Measure.map_map continuous_abs.measurable measurable_neg]
    congr 1
    ext y
    exact abs_neg y
  · simp [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs)]

/-- Replacing the location parameter by its absolute value leaves the folded normal law
unchanged. -/
@[simp]
theorem foldedNormalMeasure_abs_loc (m s : ℝ) :
    foldedNormalMeasure |m| s = foldedNormalMeasure m s := by
  rcases le_or_gt 0 m with hm | hm
  · rw [abs_of_nonneg hm]
  · rw [abs_of_neg hm, foldedNormalMeasure_neg_loc]

/-- At zero location parameter the folded normal law is the half-normal law `chiMeasure 1 s`,
including on the nonpositive-scale zero branch. -/
@[simp]
theorem foldedNormalMeasure_zero_loc (s : ℝ) :
    foldedNormalMeasure 0 s = chiMeasure 1 s := by
  by_cases hs : 0 < s
  · have hv : (s ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (pow_pos hs 2)).ne'
    rw [foldedNormalMeasure_of_scale_pos hs, gaussianReal_map_abs hv,
      coe_toNNReal _ (sq_nonneg s), sqrt_sq hs.le]
  · simp [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs),
      chiMeasure_of_scale_nonpos (not_lt.mp hs)]

/-- Every folded normal law is a degree-one noncentral chi law with noncentrality `‖m / s‖₊` and
scale `s`, including when `s ≤ 0`. -/
theorem foldedNormalMeasure_eq_noncentralChiMeasure (m s : ℝ) :
    foldedNormalMeasure m s = noncentralChiMeasure 1 ‖m / s‖₊ s := by
  by_cases hs : 0 < s
  · have hscale : (gaussianReal (m / s) 1).map (s * ·) = gaussianReal m (s ^ 2).toNNReal := by
      rw [gaussianReal_map_const_mul, mul_div_cancel₀ m hs.ne', mul_one,
        ← Real.toNNReal_of_nonneg (sq_nonneg s)]
    rw [foldedNormalMeasure_of_scale_pos hs, ← hscale,
      Measure.map_map continuous_abs.measurable (by fun_prop),
      noncentralChiMeasure_of_scale_pos hs, ← gaussianReal_map_sq_noncentral (m / s),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    ext x
    simp [Function.comp_apply, abs_mul, abs_of_pos hs, sqrt_sq_eq_abs]
  · simp [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs),
      noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs)]

/-- Reciprocally, every degree-one noncentral chi law with noncentrality `δ` and scale `s` is the
folded normal law with location `δ * s` and scale `s`. -/
theorem noncentralChiMeasure_one (δ : ℝ≥0) (s : ℝ) :
    noncentralChiMeasure 1 δ s = foldedNormalMeasure (δ * s) s := by
  by_cases hs : 0 < s
  · have hδ : ‖(δ : ℝ)‖₊ = δ := by ext; simp
    rw [foldedNormalMeasure_eq_noncentralChiMeasure, mul_div_cancel_right₀ _ hs.ne', hδ]
  · simp [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs),
      noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs)]

/-- Multiplying by a positive constant `b` sends `foldedNormalMeasure m s` to
`foldedNormalMeasure (b * m) (b * s)` across all parameter regimes. -/
@[simp]
theorem foldedNormalMeasure_map_const_mul (hb : 0 < b) (m s : ℝ) :
    (foldedNormalMeasure m s).map (fun x ↦ b * x) = foldedNormalMeasure (b * m) (b * s) := by
  rw [foldedNormalMeasure_eq_noncentralChiMeasure, noncentralChiMeasure_map_const_mul hb,
    foldedNormalMeasure_eq_noncentralChiMeasure, mul_div_mul_left _ _ hb.ne']

/-- Taking `x ↦ |b * x|` for any nonzero `b` scales the location by `b` and the scale by `|b|`. -/
theorem foldedNormalMeasure_map_abs_const_mul (hb : b ≠ 0) (m s : ℝ) :
    (foldedNormalMeasure m s).map (fun x ↦ |b * x|) = foldedNormalMeasure (b * m) (|b| * s) := by
  have habs : 0 < |b| := abs_pos.mpr hb
  by_cases hs : 0 < s
  · rw [foldedNormalMeasure_of_scale_pos hs,
      Measure.map_map (by fun_prop) continuous_abs.measurable]
    have hcomp : ((fun x : ℝ ↦ |b * x|) ∘ (|·|)) = (fun x : ℝ ↦ |b| * x) ∘ (|·|) := by
      ext x
      simp [abs_mul]
    rw [hcomp, ← Measure.map_map (by fun_prop) continuous_abs.measurable,
      ← foldedNormalMeasure_of_scale_pos hs, foldedNormalMeasure_map_const_mul habs]
    rcases le_or_gt 0 b with hb0 | hb0
    · rw [abs_of_nonneg hb0]
    · rw [abs_of_neg hb0, neg_mul, foldedNormalMeasure_neg_loc]
  · simp [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs),
      foldedNormalMeasure_of_scale_nonpos (mul_nonpos_of_nonneg_of_nonpos habs.le (not_lt.mp hs))]

/-! ### Lebesgue density -/

/-- The real-valued density of the folded normal law `foldedNormalMeasure m s`: on `(0, ∞)` for
`0 < s`, the sum of the two reflected Gaussian branches with mean `m` and variance `s ^ 2`, and `0`
elsewhere. -/
def foldedNormalPDFReal (m s x : ℝ) : ℝ :=
  if 0 < s ∧ 0 < x then
    (√(2 * π) * s)⁻¹ *
      (exp (-(x - m) ^ 2 / (2 * s ^ 2)) + exp (-(x + m) ^ 2 / (2 * s ^ 2)))
  else 0

/-- The extended nonnegative density of the folded normal law. -/
def foldedNormalPDF (m s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (foldedNormalPDFReal m s x)

/-- The extended folded normal density is `ENNReal.ofReal` of the real density. -/
theorem foldedNormalPDF_eq_ofReal (m s x : ℝ) :
    foldedNormalPDF m s x = ENNReal.ofReal (foldedNormalPDFReal m s x) := (rfl)

/-- On the positive half-line at positive scale, `foldedNormalPDFReal` unfolds to its two-branch
Gaussian exponential sum. -/
theorem foldedNormalPDFReal_of_pos (hs : 0 < s) (hx : 0 < x) :
    foldedNormalPDFReal m s x =
      (√(2 * π) * s)⁻¹ *
        (exp (-(x - m) ^ 2 / (2 * s ^ 2)) + exp (-(x + m) ^ 2 / (2 * s ^ 2))) := by
  rw [foldedNormalPDFReal, ite_eq_left ⟨hs, hx⟩]

/-- Outside the positive-scale, positive-argument regime, the real density vanishes. -/
theorem foldedNormalPDFReal_of_not_pos (h : ¬ (0 < s ∧ 0 < x)) :
    foldedNormalPDFReal m s x = 0 := by
  rw [foldedNormalPDFReal, ite_eq_right h]

/-- Outside the positive-scale, positive-argument regime, the extended density vanishes. -/
theorem foldedNormalPDF_of_not_pos (h : ¬ (0 < s ∧ 0 < x)) :
    foldedNormalPDF m s x = 0 := by
  rw [foldedNormalPDF_eq_ofReal, foldedNormalPDFReal_of_not_pos h, ENNReal.ofReal_zero]

/-- On the nonpositive half-line, the real folded normal density vanishes. -/
@[simp]
theorem foldedNormalPDFReal_of_nonpos (hx : x ≤ 0) :
    foldedNormalPDFReal m s x = 0 :=
  foldedNormalPDFReal_of_not_pos fun h ↦ (not_lt.mpr hx) h.2

/-- On the nonpositive half-line, the extended folded normal density vanishes. -/
@[simp]
theorem foldedNormalPDF_of_nonpos (hx : x ≤ 0) :
    foldedNormalPDF m s x = 0 := by
  rw [foldedNormalPDF_eq_ofReal, foldedNormalPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- At nonpositive scale, the real folded normal density vanishes. -/
@[simp]
theorem foldedNormalPDFReal_of_scale_nonpos (hs : s ≤ 0) :
    foldedNormalPDFReal m s x = 0 :=
  foldedNormalPDFReal_of_not_pos fun h ↦ (not_lt.mpr hs) h.1

/-- At nonpositive scale, the extended folded normal density vanishes. -/
@[simp]
theorem foldedNormalPDF_of_scale_nonpos (hs : s ≤ 0) :
    foldedNormalPDF m s x = 0 := by
  rw [foldedNormalPDF_eq_ofReal, foldedNormalPDFReal_of_scale_nonpos hs, ENNReal.ofReal_zero]

/-- On the positive half-line at positive scale, `foldedNormalPDF` is `ENNReal.ofReal` of the
two-branch Gaussian exponential sum. -/
theorem foldedNormalPDF_of_pos (hs : 0 < s) (hx : 0 < x) :
    foldedNormalPDF m s x = ENNReal.ofReal ((√(2 * π) * s)⁻¹ *
      (exp (-(x - m) ^ 2 / (2 * s ^ 2)) + exp (-(x + m) ^ 2 / (2 * s ^ 2)))) := by
  rw [foldedNormalPDF_eq_ofReal, foldedNormalPDFReal_of_pos hs hx]

/-- The real folded normal density is nonnegative everywhere. -/
theorem foldedNormalPDFReal_nonneg (m s x : ℝ) : 0 ≤ foldedNormalPDFReal m s x := by
  by_cases h : 0 < s ∧ 0 < x
  · rw [foldedNormalPDFReal_of_pos h.1 h.2]
    have hs : 0 < s := h.1
    positivity
  · rw [foldedNormalPDFReal_of_not_pos h]

/-- At positive scale, the real density is strictly positive exactly on `(0, ∞)`. -/
theorem foldedNormalPDFReal_pos_iff (hs : 0 < s) :
    0 < foldedNormalPDFReal m s x ↔ 0 < x := by
  by_cases hx : 0 < x
  · rw [foldedNormalPDFReal_of_pos hs hx]
    exact iff_of_true (by positivity) hx
  · rw [foldedNormalPDFReal_of_nonpos (not_lt.mp hx)]
    exact iff_of_false (lt_irrefl 0) hx

/-- Converting `foldedNormalPDF` back to `ℝ` recovers `foldedNormalPDFReal`. -/
@[simp]
theorem toReal_foldedNormalPDF (m s x : ℝ) :
    (foldedNormalPDF m s x).toReal = foldedNormalPDFReal m s x :=
  ENNReal.toReal_ofReal (foldedNormalPDFReal_nonneg m s x)

/-- On `(0, ∞)` at positive scale, the folded normal density is the sum of `gaussianPDFReal` at `x`
and `-x`. -/
theorem foldedNormalPDFReal_eq_add_gaussianPDFReal (hs : 0 < s) (hx : 0 < x) :
    foldedNormalPDFReal m s x =
      gaussianPDFReal m (s ^ 2).toNNReal x + gaussianPDFReal m (s ^ 2).toNNReal (-x) := by
  rw [foldedNormalPDFReal_of_pos hs hx, gaussianPDFReal, gaussianPDFReal]
  simp only [coe_toNNReal _ (sq_nonneg s)]
  have hrad : √(2 * π * s ^ 2) = √(2 * π) * s := by
    rw [sqrt_mul (by positivity), sqrt_sq hs.le]
  have hneg : -(-x - m) ^ 2 = -(x + m) ^ 2 := by ring
  rw [hrad, hneg, mul_add]

/-- Standardized form of the folded normal density in terms of the standard Gaussian density `φ`. -/
theorem foldedNormalPDFReal_eq_gaussianPDFReal_zero_one (hs : 0 < s) (hx : 0 < x) :
    foldedNormalPDFReal m s x =
      (gaussianPDFReal 0 1 ((x - m) / s) + gaussianPDFReal 0 1 ((x + m) / s)) / s := by
  rw [foldedNormalPDFReal_eq_add_gaussianPDFReal hs hx,
    gaussianPDFReal_eq_gaussianPDFReal_zero_one m (s ^ 2).toNNReal x,
    gaussianPDFReal_eq_gaussianPDFReal_zero_one m (s ^ 2).toNNReal (-x)]
  simp only [coe_toNNReal _ (sq_nonneg s), sqrt_sq hs.le]
  have hneg : (-x - m) / s = -((x + m) / s) := by ring
  rw [hneg, gaussianPDFReal_zero_neg, ← add_div]

/-- Hyperbolic-cosine factorization of the folded normal density on `(0, ∞)`. -/
theorem foldedNormalPDFReal_eq_cosh (hs : 0 < s) (hx : 0 < x) :
    foldedNormalPDFReal m s x =
      √(2 / π) / s * exp (-(x ^ 2 + m ^ 2) / (2 * s ^ 2)) * cosh (m * x / s ^ 2) := by
  rw [foldedNormalPDFReal_of_pos hs hx, Real.cosh_eq]
  have he1 : -(x - m) ^ 2 / (2 * s ^ 2) = -(x ^ 2 + m ^ 2) / (2 * s ^ 2) + m * x / s ^ 2 := by
    field_simp [hs.ne']
    ring
  have he2 : -(x + m) ^ 2 / (2 * s ^ 2) = -(x ^ 2 + m ^ 2) / (2 * s ^ 2) + -(m * x / s ^ 2) := by
    field_simp [hs.ne']
    ring
  have hconst : (√(2 * π) * s)⁻¹ * 2 = √(2 / π) / s := by
    rw [sqrt_div zero_le_two, sqrt_mul zero_le_two]
    field_simp [hs.ne', (sqrt_pos.2 two_pos).ne', (sqrt_pos.2 pi_pos).ne']
    exact (sq_sqrt zero_le_two).symm
  rw [he1, he2, exp_add, exp_add, ← mul_add, ← hconst]
  ring

/-- Negating the location parameter leaves the real density unchanged. -/
@[simp]
theorem foldedNormalPDFReal_neg_loc (m s x : ℝ) :
    foldedNormalPDFReal (-m) s x = foldedNormalPDFReal m s x := by
  by_cases h : 0 < s ∧ 0 < x
  · rw [foldedNormalPDFReal_of_pos h.1 h.2, foldedNormalPDFReal_of_pos h.1 h.2]
    have h1 : -(x - -m) ^ 2 = -(x + m) ^ 2 := by ring
    have h2 : -(x + -m) ^ 2 = -(x - m) ^ 2 := by ring
    rw [h1, h2, add_comm]
  · rw [foldedNormalPDFReal_of_not_pos h, foldedNormalPDFReal_of_not_pos h]

/-- Replacing `m` by `|m|` leaves the real density unchanged. -/
@[simp]
theorem foldedNormalPDFReal_abs_loc (m s x : ℝ) :
    foldedNormalPDFReal |m| s x = foldedNormalPDFReal m s x := by
  rcases le_or_gt 0 m with hm | hm
  · rw [abs_of_nonneg hm]
  · rw [abs_of_neg hm, foldedNormalPDFReal_neg_loc]

/-- At `m = 0`, the real folded normal density specializes to the half-normal density
`chiPDFReal 1 s`. -/
@[simp]
theorem foldedNormalPDFReal_zero_loc (s x : ℝ) :
    foldedNormalPDFReal 0 s x = chiPDFReal 1 s x := by
  by_cases h : 0 < s ∧ 0 < x
  · rw [foldedNormalPDFReal_eq_cosh h.1 h.2, chiPDFReal_of_pos one_pos h.1 h.2]
    have hrpow : (2 : ℝ) ^ (1 - (1 : ℝ) / 2) = √2 := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, sqrt_eq_rpow]
    simp only [zero_pow two_ne_zero, add_zero, zero_mul, zero_div, cosh_zero, mul_one,
      sub_self, rpow_zero, Gamma_one_half_eq, hrpow, sqrt_div zero_le_two]
    field_simp [h.1.ne', (sqrt_pos.2 pi_pos).ne']
  · rw [foldedNormalPDFReal_of_not_pos h, chiPDFReal_of_not_pos fun hc ↦ h hc.2]

/-- Negating the location parameter leaves the extended density unchanged. -/
@[simp]
theorem foldedNormalPDF_neg_loc (m s x : ℝ) :
    foldedNormalPDF (-m) s x = foldedNormalPDF m s x := by
  rw [foldedNormalPDF_eq_ofReal, foldedNormalPDF_eq_ofReal, foldedNormalPDFReal_neg_loc]

/-- Replacing `m` by `|m|` leaves the extended density unchanged. -/
@[simp]
theorem foldedNormalPDF_abs_loc (m s x : ℝ) :
    foldedNormalPDF |m| s x = foldedNormalPDF m s x := by
  rw [foldedNormalPDF_eq_ofReal, foldedNormalPDF_eq_ofReal, foldedNormalPDFReal_abs_loc]

/-- At `m = 0`, the extended folded normal density specializes to `chiPDF 1 s`. -/
@[simp]
theorem foldedNormalPDF_zero_loc (s x : ℝ) :
    foldedNormalPDF 0 s x = chiPDF 1 s x := by
  rw [foldedNormalPDF_eq_ofReal, chiPDF_eq_ofReal, foldedNormalPDFReal_zero_loc]

/-- The real folded normal density is continuous on `(0, ∞)` for all parameters. -/
theorem continuousOn_foldedNormalPDFReal (m s : ℝ) :
    ContinuousOn (foldedNormalPDFReal m s) (Ioi 0) := by
  by_cases hs : 0 < s
  · refine ContinuousOn.congr ?_ fun x hx ↦ foldedNormalPDFReal_of_pos hs hx
    fun_prop
  · refine (continuousOn_const : ContinuousOn (fun _ : ℝ ↦ (0 : ℝ)) (Ioi 0)).congr fun x _ ↦ ?_
    exact foldedNormalPDFReal_of_scale_nonpos (not_lt.mp hs)

/-- The real folded normal density is jointly measurable in location, scale, and coordinate. -/
@[fun_prop]
theorem measurable_uncurry_foldedNormalPDFReal :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ foldedNormalPDFReal p.1.1 p.1.2 p.2 := by
  unfold foldedNormalPDFReal
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

/-- The real folded normal density is measurable in its sample argument. -/
@[fun_prop]
theorem measurable_foldedNormalPDFReal (m s : ℝ) :
    Measurable (foldedNormalPDFReal m s) :=
  measurable_uncurry_foldedNormalPDFReal.comp (by fun_prop : Measurable fun x : ℝ ↦ ((m, s), x))

/-- The extended folded normal density is jointly measurable in location, scale, and coordinate. -/
@[fun_prop]
theorem measurable_uncurry_foldedNormalPDF :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ foldedNormalPDF p.1.1 p.1.2 p.2 :=
  measurable_uncurry_foldedNormalPDFReal.ennreal_ofReal

/-- The extended folded normal density is measurable in its sample argument. -/
@[fun_prop]
theorem measurable_foldedNormalPDF (m s : ℝ) :
    Measurable (foldedNormalPDF m s) :=
  (measurable_foldedNormalPDFReal m s).ennreal_ofReal

/-- For every location `m` and scale `s`, `foldedNormalMeasure m s` is Lebesgue measure weighted by
`foldedNormalPDF m s`. -/
theorem foldedNormalMeasure_eq_withDensity (m s : ℝ) :
    foldedNormalMeasure m s = volume.withDensity (foldedNormalPDF m s) := by
  by_cases hs : 0 < s
  · have hv : (s ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (pow_pos hs 2)).ne'
    rw [foldedNormalMeasure_of_scale_pos hs, gaussianReal_of_var_ne_zero m hv,
      map_abs_withDensity (measurable_gaussianPDF m _)]
    apply withDensity_congr_ae
    refine .of_forall fun x ↦ ?_
    by_cases hx : 0 < x
    · rw [indicator_of_mem (mem_Ioi.mpr hx), gaussianPDF_def,
        ← ENNReal.ofReal_add (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _),
        foldedNormalPDF_eq_ofReal, foldedNormalPDFReal_eq_add_gaussianPDFReal hs hx]
    · rw [indicator_of_notMem (not_lt.mpr (not_lt.mp hx)),
        foldedNormalPDF_of_nonpos (not_lt.mp hx)]
  · have hzero : foldedNormalPDF m s = 0 :=
      funext fun x ↦ foldedNormalPDF_of_scale_nonpos (not_lt.mp hs)
    rw [foldedNormalMeasure_of_scale_nonpos (not_lt.mp hs), hzero, withDensity_zero]

/-- The degree-one noncentral chi density coincides pointwise with the folded normal density across
all noncentralities, scales, and coordinates. -/
theorem noncentralChiPDFReal_one (δ : ℝ≥0) (s x : ℝ) :
    noncentralChiPDFReal 1 δ s x = foldedNormalPDFReal (δ * s) s x := by
  by_cases hsx : 0 < s ∧ 0 < x
  swap
  · rcases not_and_or.mp hsx with hs | hx
    · rw [noncentralChiPDFReal_of_scale_nonpos (not_lt.mp hs),
        foldedNormalPDFReal_of_scale_nonpos (not_lt.mp hs)]
    · rw [noncentralChiPDFReal_of_nonpos (not_lt.mp hx),
        foldedNormalPDFReal_of_nonpos (not_lt.mp hx)]
  obtain ⟨hs, hx⟩ := hsx
  -- Both measures agree and have continuous densities on `(0, ∞)`, so the densities agree
  -- everywhere on `(0, ∞)`.
  have hmeas_eq : volume.withDensity (noncentralChiPDF 1 δ s) =
      volume.withDensity (foldedNormalPDF (δ * s) s) := by
    rw [← noncentralChiMeasure_eq_withDensity one_pos hs, noncentralChiMeasure_one,
      foldedNormalMeasure_eq_withDensity]
  have hae : noncentralChiPDF 1 δ s =ᵐ[volume] foldedNormalPDF (δ * s) s := by
    have h1 := Measure.rnDeriv_withDensity volume (measurable_noncentralChiPDF 1 δ s)
    have h2 := Measure.rnDeriv_withDensity volume (measurable_foldedNormalPDF (δ * s) s)
    rw [hmeas_eq] at h1
    exact h1.symm.trans h2
  have hae_real : noncentralChiPDFReal 1 δ s =ᵐ[volume] foldedNormalPDFReal (δ * s) s := by
    filter_upwards [hae] with y hy
    simpa only [toReal_noncentralChiPDF, toReal_foldedNormalPDF] using
      congrArg ENNReal.toReal hy
  exact volume.eqOn_open_of_ae_eq (ae_restrict_of_ae hae_real) isOpen_Ioi
    (continuousOn_noncentralChiPDFReal 1 δ s) (continuousOn_foldedNormalPDFReal _ _) hx

/-- The extended degree-one noncentral chi density coincides pointwise with `foldedNormalPDF`. -/
theorem noncentralChiPDF_one (δ : ℝ≥0) (s x : ℝ) :
    noncentralChiPDF 1 δ s x = foldedNormalPDF (δ * s) s x := by
  rw [noncentralChiPDF_eq_ofReal, foldedNormalPDF_eq_ofReal, noncentralChiPDFReal_one]

/-- Pointwise identification of the real folded normal density as a degree-one noncentral chi
density. -/
theorem foldedNormalPDFReal_eq_noncentralChiPDFReal (m s x : ℝ) :
    foldedNormalPDFReal m s x = noncentralChiPDFReal 1 ‖m / s‖₊ s x := by
  by_cases hs : 0 < s
  · rw [noncentralChiPDFReal_one, coe_nnnorm, Real.norm_eq_abs, abs_div, abs_of_pos hs,
      div_mul_cancel₀ _ hs.ne', foldedNormalPDFReal_abs_loc]
  · rw [foldedNormalPDFReal_of_scale_nonpos (not_lt.mp hs),
      noncentralChiPDFReal_of_scale_nonpos (not_lt.mp hs)]

/-- Pointwise identification of the extended folded normal density as a degree-one noncentral chi
density. -/
theorem foldedNormalPDF_eq_noncentralChiPDF (m s x : ℝ) :
    foldedNormalPDF m s x = noncentralChiPDF 1 ‖m / s‖₊ s x := by
  rw [foldedNormalPDF_eq_ofReal, noncentralChiPDF_eq_ofReal,
    foldedNormalPDFReal_eq_noncentralChiPDFReal]

/-- The folded normal family is jointly Giry measurable in location and scale, including its
nonpositive-scale zero branch. -/
@[fun_prop]
theorem measurable_foldedNormalMeasure :
    Measurable fun p : ℝ × ℝ ↦ foldedNormalMeasure p.1 p.2 := by
  simp_rw [foldedNormalMeasure_eq_withDensity]
  exact measurable_withDensity measurable_uncurry_foldedNormalPDF

/-- The Radon–Nikodym derivative of `foldedNormalMeasure m s` with respect to Lebesgue measure is
`foldedNormalPDF m s` for all parameters. -/
theorem rnDeriv_foldedNormalMeasure (m s : ℝ) :
    (foldedNormalMeasure m s).rnDeriv volume =ᵐ[volume] foldedNormalPDF m s := by
  rw [foldedNormalMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_foldedNormalPDF m s)

/-- Every folded normal measure is atomless, including on the nonpositive-scale zero branch. -/
instance nullSingletonClass_foldedNormalMeasure (m s : ℝ) :
    NullSingletonClass (foldedNormalMeasure m s) := by
  rw [foldedNormalMeasure_eq_withDensity]
  infer_instance

/-- At positive scale, the topological support of the folded normal law is `[0, ∞)`. -/
@[simp]
theorem support_foldedNormalMeasure (m : ℝ) {s : ℝ} (hs : 0 < s) :
    (foldedNormalMeasure m s).support = Ici 0 := by
  rw [foldedNormalMeasure_eq_withDensity,
    Measure.support_withDensity_eq_closure (measurable_foldedNormalPDF m s) isOpen_Ioi,
    closure_Ioi]
  ext x
  rw [Function.mem_support, foldedNormalPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff,
    foldedNormalPDFReal_pos_iff hs, mem_Ioi]

/-- Under any folded normal law, sample points are strictly positive almost everywhere. -/
theorem ae_pos_foldedNormalMeasure (m s : ℝ) :
    ∀ᵐ x ∂foldedNormalMeasure m s, 0 < x := by
  rw [foldedNormalMeasure_eq_withDensity, ae_withDensity_iff (measurable_foldedNormalPDF m s)]
  exact .of_forall fun x hx ↦ not_le.mp fun h ↦ hx (foldedNormalPDF_of_nonpos h)

/-- Under any folded normal law, sample points are nonnegative almost everywhere. -/
theorem ae_nonneg_foldedNormalMeasure (m s : ℝ) :
    ∀ᵐ x ∂foldedNormalMeasure m s, 0 ≤ x :=
  (ae_pos_foldedNormalMeasure m s).mono fun _ hx ↦ hx.le

/-! ### Weak continuity and small-scale limit -/

/-- On the valid positive-scale domain, folded normal probability measures depend jointly weakly
continuously on location and scale. -/
theorem continuous_foldedNormalMeasure :
    Continuous (Y := ProbabilityMeasure ℝ) (fun p : ℝ × Ioi (0 : ℝ) ↦
      (⟨foldedNormalMeasure p.1 p.2,
        isProbabilityMeasure_foldedNormalMeasure p.1 p.2.2⟩ : ProbabilityMeasure ℝ)) := by
  have hparam : Continuous fun p : ℝ × Ioi (0 : ℝ) ↦
      (p.1, (((p.2 : ℝ) ^ 2).toNNReal : ℝ≥0)) :=
    continuous_fst.prodMk (continuous_real_toNNReal.comp
      ((continuous_subtype_val.comp continuous_snd).pow 2))
  have h := (ProbabilityMeasure.continuous_map continuous_abs).comp
    (continuous_gaussianReal.comp hparam)
  refine h.congr fun p ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp only [Function.comp_apply, ProbabilityMeasure.toMeasure_map,
    Measure.coe_toProbabilityMeasure, ProbabilityMeasure.coe_mk,
    foldedNormalMeasure_of_scale_pos p.2.2]

/-- As the positive scale `s → 0`, `foldedNormalMeasure m s` converges weakly to the point mass at
`|m|`. -/
theorem tendsto_foldedNormalMeasure_nhdsGT_zero_dirac (m : ℝ) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun s : Ioi (0 : ℝ) ↦
        (⟨foldedNormalMeasure m s, isProbabilityMeasure_foldedNormalMeasure m s.2⟩ :
          ProbabilityMeasure ℝ))
      (comap ((↑) : Ioi (0 : ℝ) → ℝ) (𝓝 0))
      (𝓝 (Measure.dirac |m|).toProbabilityMeasure) := by
  let F : ℝ → ProbabilityMeasure ℝ :=
    fun s ↦ (gaussianReal m (s ^ 2).toNNReal).toProbabilityMeasure.map abs
  have hparam : Continuous fun s : ℝ ↦ (m, (s ^ 2).toNNReal) :=
    continuous_const.prodMk (continuous_real_toNNReal.comp (continuous_id.pow 2))
  have hcont : Continuous F :=
    (ProbabilityMeasure.continuous_map continuous_abs).comp (continuous_gaussianReal.comp hparam)
  have h0 : F 0 = (Measure.dirac |m|).toProbabilityMeasure := by
    apply ProbabilityMeasure.toMeasure_injective
    simp [F, ProbabilityMeasure.toMeasure_map]
  have hlim : Tendsto (fun s : Ioi (0 : ℝ) ↦ F s)
      (comap ((↑) : Ioi (0 : ℝ) → ℝ) (𝓝 0))
      (𝓝 (Measure.dirac |m|).toProbabilityMeasure) := by
    rw [← h0]
    exact (hcont.tendsto 0).comp tendsto_comap
  refine hlim.congr fun s ↦ ?_
  apply ProbabilityMeasure.toMeasure_injective
  simp [F, ProbabilityMeasure.toMeasure_map, foldedNormalMeasure_of_scale_pos s.2]

end TauCeti.Probability

namespace Continuous

variable {T : Type*} [TopologicalSpace T]

/-- Continuous location and positive scale parameters give a weakly continuous family of folded
normal probability measures. -/
@[fun_prop]
theorem foldedNormalMeasure {m s : T → ℝ} (hm : Continuous m) (hs : Continuous s)
    (hpos : ∀ t, 0 < s t) :
    Continuous (Y := ProbabilityMeasure ℝ) (fun t ↦
      (⟨TauCeti.Probability.foldedNormalMeasure (m t) (s t),
        TauCeti.Probability.isProbabilityMeasure_foldedNormalMeasure (m t) (hpos t)⟩ :
          ProbabilityMeasure ℝ)) :=
  TauCeti.Probability.continuous_foldedNormalMeasure.comp (hm.prodMk (hs.subtype_mk hpos))

end Continuous

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {m s c : ℝ}

/-- The absolute value of a real Gaussian variable with mean `m` and nonzero variance `v` has law
`foldedNormalMeasure m √v`. -/
theorem HasLaw.abs_gaussianReal_foldedNormalMeasure {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) P) (hv : v ≠ 0) :
    HasLaw (fun ω ↦ |X ω|) (foldedNormalMeasure m √(v : ℝ)) P :=
  (HasLaw.mk continuous_abs.measurable.aemeasurable
    (gaussianReal_map_abs_eq_foldedNormalMeasure m hv)).fun_comp hX

/-- Every random variable with a folded normal law admits a Lebesgue density. -/
theorem HasLaw.hasPDF_foldedNormalMeasure
    (hX : HasLaw X (foldedNormalMeasure m s) P) : HasPDF X P := by
  rw [foldedNormalMeasure_eq_withDensity] at hX
  exact hasPDF_of_hasLaw_withDensity (measurable_foldedNormalPDF m s).aemeasurable hX

/-- The canonical density of a folded normal variable agrees almost everywhere with
`foldedNormalPDF m s`. -/
theorem HasLaw.pdf_eq_foldedNormalPDF
    (hX : HasLaw X (foldedNormalMeasure m s) P) :
    pdf X P volume =ᵐ[volume] foldedNormalPDF m s := by
  rw [foldedNormalMeasure_eq_withDensity] at hX
  exact pdf_eq_of_hasLaw_withDensity (measurable_foldedNormalPDF m s).aemeasurable hX

/-- Multiplying a folded normal variable by `c > 0` scales both its location and scale parameters
by `c`. -/
theorem HasLaw.const_mul_foldedNormalMeasure
    (hX : HasLaw X (foldedNormalMeasure m s) P) (hc : 0 < c) :
    HasLaw (fun ω ↦ c * X ω) (foldedNormalMeasure (c * m) (c * s)) P :=
  (HasLaw.mk (by fun_prop) (foldedNormalMeasure_map_const_mul hc m s)).fun_comp hX

end ProbabilityTheory
