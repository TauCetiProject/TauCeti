/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Density
public import TauCeti.Probability.Quantile
public import TauCeti.Probability.Distributions.Gaussian.OwensT
import TauCeti.Probability.Distributions.Affine

/-!
# The skew-normal distribution

Write `φ = gaussianPDFReal 0 1` and `Φ = cdf (gaussianReal 0 1)` for the standard Gaussian density
and cumulative distribution function. The skew-normal law with location `m`, scale `s > 0` and
shape `α` has density `2 * φ(y) * Φ(α * y) / s`, where `y = (x - m) / s`. Shape `0` is the
Gaussian law with mean `m` and variance `s ^ 2`; a nonzero shape tilts the Gaussian bell towards
one side. Owen's T function `Real.owensT` gives the cumulative distribution function
`Φ(y) - 2 * T(y, α)`, so the quantile at a level `u` is the unique root of
`Φ(y) - 2 * T(y, α) = u`.

**Boundary.** For `s ≤ 0` there is no skew-normal law: `skewNormalMeasure m s α` and its density
are *defined* to vanish there (`skewNormalMeasure_of_nonpos`, `skewNormalPDFReal_of_nonpos`).
The affine transport theorems hold at every scale, and the family is measurable in its three
parameters jointly.

## Main definitions

* `TauCeti.Probability.skewNormalPDFReal` — the real-valued density;
* `TauCeti.Probability.skewNormalPDF` — its `ℝ≥0∞`-valued companion;
* `TauCeti.Probability.skewNormalMeasure` — the law, `volume.withDensity skewNormalPDF`.

## Main results

* `isProbabilityMeasure_skewNormalMeasure` — it is a probability measure when `0 < s`;
* `cdf_skewNormalMeasure_eq` — the cdf is `Φ(y) - 2 * T(y, α)`;
* `hasPDF_of_hasLaw_skewNormalMeasure`, `pdf_eq_skewNormalPDF_of_hasLaw_skewNormalMeasure` and
  `rnDeriv_skewNormalMeasure` — the density;
* `skewNormalMeasure_eq_gaussianReal` — shape `0` is the Gaussian law `N(m, s ^ 2)`;
* `map_affine_skewNormalMeasure_of_pos` and `map_affine_skewNormalMeasure_of_neg` — the affine
  image `a + b X` is skew-normal with location `a + b * m` and scale `|b| * s`, and its shape is
  reflected to `-α` when `b < 0`;
* `map_neg_skewNormalMeasure` — **shape reflection**: `-X` is skew-normal with location `-m` and
  shape `-α`;
* `skewNormalMeasure_eq_map_skewNormalMeasure_zero_one` — every skew-normal law is an affine
  image of the standard one with the same shape;
* `quantile_skewNormalMeasure_eq_iff` — the quantile at `0 < u < 1` is the unique `x` with
  `Φ(y) - 2 * T(y, α) = u`;
* `measurable_skewNormalMeasure` — the family is measurable in its three parameters.

## References

* A. Azzalini, *A class of distributions which includes the normal ones*, Scandinavian Journal of
  Statistics 12 (1985), 171–178.
* A. Azzalini and A. Capitanio, *The Skew-Normal and Related Families*, Cambridge University
  Press, 2014.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

variable {m s α x : ℝ}

/-! ### The density -/

/-- The density of the skew-normal law with location `m`, scale `s` and shape `α`, as a
real-valued function: `2 * φ(y) * Φ(α * y) / s` with `y = (x - m) / s`, where `φ` and `Φ` are the
standard Gaussian density and cdf.

For `s ≤ 0` there is no such law and the density is `0`. -/
def skewNormalPDFReal (m s α x : ℝ) : ℝ :=
  if 0 < s then
    2 * gaussianPDFReal 0 1 ((x - m) / s) * cdf (gaussianReal 0 1) (α * ((x - m) / s)) / s
  else 0

/-- The density of the skew-normal law, as a function valued in `ℝ≥0∞`. -/
def skewNormalPDF (m s α x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (skewNormalPDFReal m s α x)

/-- The `ℝ≥0∞`-valued skew-normal density is the coercion of the real-valued one. -/
theorem skewNormalPDF_eq_ofReal (m s α x : ℝ) :
    skewNormalPDF m s α x = ENNReal.ofReal (skewNormalPDFReal m s α x) := by
  rw [skewNormalPDF]

/-- Outside the valid parameter range the density vanishes. -/
@[simp]
theorem skewNormalPDFReal_of_nonpos (hs : s ≤ 0) (m α x : ℝ) : skewNormalPDFReal m s α x = 0 := by
  rw [skewNormalPDFReal, ite_eq_right (not_lt.mpr hs)]

/-- For a positive scale the density is `2 * φ(y) * Φ(α * y) / s` with `y = (x - m) / s`. -/
@[simp]
theorem skewNormalPDFReal_of_pos (hs : 0 < s) (m α x : ℝ) :
    skewNormalPDFReal m s α x =
      2 * gaussianPDFReal 0 1 ((x - m) / s) * cdf (gaussianReal 0 1) (α * ((x - m) / s)) / s := by
  rw [skewNormalPDFReal, ite_eq_left hs]

/-- The standard skew-normal density with shape `α` is `2 * φ(x) * Φ(α * x)`. -/
theorem skewNormalPDFReal_zero_one (α x : ℝ) :
    skewNormalPDFReal 0 1 α x = 2 * gaussianPDFReal 0 1 x * cdf (gaussianReal 0 1) (α * x) := by
  rw [skewNormalPDFReal_of_pos one_pos, sub_zero, div_one, div_one]

/-- Outside the valid parameter range the `ℝ≥0∞`-valued density vanishes. -/
@[simp]
theorem skewNormalPDF_of_nonpos (hs : s ≤ 0) (m α x : ℝ) : skewNormalPDF m s α x = 0 := by
  rw [skewNormalPDF_eq_ofReal, skewNormalPDFReal_of_nonpos hs, ENNReal.ofReal_zero]

/-- The skew-normal density is nonnegative at every parameter, valid or not. -/
theorem skewNormalPDFReal_nonneg (m s α x : ℝ) : 0 ≤ skewNormalPDFReal m s α x := by
  rcases le_or_gt s 0 with hs | hs
  · rw [skewNormalPDFReal_of_nonpos hs]
  · rw [skewNormalPDFReal_of_pos hs]
    have := gaussianPDFReal_nonneg 0 1 ((x - m) / s)
    have := cdf_nonneg (gaussianReal 0 1) (α * ((x - m) / s))
    positivity

/-- For a positive scale the skew-normal density is strictly positive everywhere. -/
theorem skewNormalPDFReal_pos (hs : 0 < s) (m α x : ℝ) : 0 < skewNormalPDFReal m s α x := by
  rw [skewNormalPDFReal_of_pos hs]
  have := gaussianPDFReal_pos 0 1 ((x - m) / s) one_ne_zero
  have := cdf_gaussianReal_pos 0 one_ne_zero (α * ((x - m) / s))
  positivity

/-- The two skew-normal densities agree under `ENNReal.toReal`; the density is never infinite. -/
@[simp]
theorem toReal_skewNormalPDF (m s α x : ℝ) :
    (skewNormalPDF m s α x).toReal = skewNormalPDFReal m s α x :=
  ENNReal.toReal_ofReal (skewNormalPDFReal_nonneg m s α x)

/-- The skew-normal density is measurable jointly in its location, scale, shape and the point. -/
@[fun_prop]
theorem measurable_uncurry_skewNormalPDFReal :
    Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => skewNormalPDFReal q.1.1 q.1.2.1 q.1.2.2 q.2 := by
  have hΦ : Measurable (cdf (gaussianReal 0 1)) := (monotone_cdf _).measurable
  have hφ : Measurable (gaussianPDFReal 0 1) := measurable_gaussianPDFReal 0 1
  simp only [skewNormalPDFReal]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst.snd.fst)
    (by fun_prop) measurable_const

/-- The `ℝ≥0∞`-valued skew-normal density is measurable jointly in its parameters and the
point. -/
@[fun_prop]
theorem measurable_uncurry_skewNormalPDF :
    Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => skewNormalPDF q.1.1 q.1.2.1 q.1.2.2 q.2 :=
  measurable_uncurry_skewNormalPDFReal.ennreal_ofReal

/-- The real-valued skew-normal density is measurable. -/
@[fun_prop]
theorem measurable_skewNormalPDFReal (m s α : ℝ) : Measurable (skewNormalPDFReal m s α) :=
  measurable_uncurry_skewNormalPDFReal.comp (measurable_prodMk_left (x := (m, s, α)))

/-- The `ℝ≥0∞`-valued skew-normal density is measurable. -/
@[fun_prop]
theorem measurable_skewNormalPDF (m s α : ℝ) : Measurable (skewNormalPDF m s α) :=
  (measurable_skewNormalPDFReal m s α).ennreal_ofReal

/-- The skew-normal density is integrable on the whole line for every parameter. -/
theorem integrable_skewNormalPDFReal (m s α : ℝ) : Integrable (skewNormalPDFReal m s α) := by
  rcases le_or_gt s 0 with hs | hs
  · have h : skewNormalPDFReal m s α = fun _ => 0 := funext (skewNormalPDFReal_of_nonpos hs m α)
    rw [h]
    exact integrable_zero ℝ ℝ volume
  · have h : skewNormalPDFReal m s α =
        fun x => skewNormalPDFReal 0 1 α ((x - m) / s) / s := funext fun x => by
      rw [skewNormalPDFReal_of_pos hs, skewNormalPDFReal_zero_one]
    rw [h]
    refine (((integrable_two_mul_gaussianPDFReal_mul_cdf_gaussianReal α).congr
      (.of_forall fun t => (skewNormalPDFReal_zero_one α t).symm)).comp_div hs.ne').comp_sub_right
      m |>.div_const s

/-- For a positive scale, the derivative of the skew-normal cdf `x ↦ Φ(y) - 2 * T(y, α)`, with
`y = (x - m) / s`, is the skew-normal density. -/
theorem hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT_skewNormalPDFReal (hs : 0 < s)
    (m α x : ℝ) :
    HasDerivAt (fun x => cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α)
      (skewNormalPDFReal m s α x) x := by
  have h := (hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT α ((x - m) / s)).comp x
    (((hasDerivAt_id x).sub_const m).div_const s)
  rw [skewNormalPDFReal_of_pos hs, div_eq_mul_one_div _ s]
  exact h

/-- The standardized point `(x - m) / s` tends to `-∞` with `x` when `s > 0`. -/
private theorem tendsto_div_atBot (hs : 0 < s) (m : ℝ) :
    Tendsto (fun x => (x - m) / s) atBot atBot :=
  (tendsto_atBot_add_const_right _ (-m) tendsto_id).atBot_div_const hs

/-- The mass of the skew-normal density below a point is `Φ(y) - 2 * T(y, α)`, with
`y = (x - m) / s`. -/
theorem integral_skewNormalPDFReal_Iic (hs : 0 < s) (m α x : ℝ) :
    ∫ y in Iic x, skewNormalPDFReal m s α y =
      cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α := by
  rw [integral_Iic_of_hasDerivAt_of_tendsto'
      (fun y _ => hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT_skewNormalPDFReal hs m α y)
      (integrable_skewNormalPDFReal m s α).integrableOn
      ((tendsto_cdf_gaussianReal_sub_two_mul_owensT_atBot α).comp (tendsto_div_atBot hs m)),
    sub_zero]

/-! ### The measure -/

/-- The skew-normal probability measure with location `m`, scale `s` and shape `α`: the law with
density `2 * φ(y) * Φ(α * y) / s`, where `y = (x - m) / s`.

For `s ≤ 0` this is the zero measure, not a probability measure; see
`skewNormalMeasure_of_nonpos`. -/
def skewNormalMeasure (m s α : ℝ) : Measure ℝ :=
  volume.withDensity (skewNormalPDF m s α)

/-- **The density of the skew-normal law.** The skew-normal law is
`volume.withDensity skewNormalPDF`, at every parameter. -/
theorem skewNormalMeasure_eq_withDensity (m s α : ℝ) :
    skewNormalMeasure m s α = volume.withDensity (skewNormalPDF m s α) := by
  rw [skewNormalMeasure]

/-- Outside the valid parameter range the skew-normal law is the zero measure. -/
@[simp]
theorem skewNormalMeasure_of_nonpos (hs : s ≤ 0) (m α : ℝ) : skewNormalMeasure m s α = 0 := by
  have h : skewNormalPDF m s α = 0 := funext fun x => by
    rw [skewNormalPDF_of_nonpos hs, Pi.zero_apply]
  rw [skewNormalMeasure_eq_withDensity, h, withDensity_zero]

/-- The skew-normal law of a lower half-line: the event `{X ≤ x}` has mass
`Φ(y) - 2 * T(y, α)`, with `y = (x - m) / s`. -/
theorem skewNormalMeasure_Iic (hs : 0 < s) (m α x : ℝ) :
    skewNormalMeasure m s α (Iic x) = ENNReal.ofReal
      (cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α) := by
  rw [skewNormalMeasure_eq_withDensity, withDensity_apply _ measurableSet_Iic,
    funext (skewNormalPDF_eq_ofReal m s α), ← ofReal_integral_eq_lintegral_ofReal
      (integrable_skewNormalPDFReal m s α).integrableOn
      (.of_forall (skewNormalPDFReal_nonneg m s α)), integral_skewNormalPDFReal_Iic hs]

/-- For a positive scale the skew-normal law is a probability measure. -/
theorem isProbabilityMeasure_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    IsProbabilityMeasure (skewNormalMeasure m s α) := by
  constructor
  rw [skewNormalMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have h : ∫ x, skewNormalPDFReal m s α x = 1 := by
    rw [integral_of_hasDerivAt_of_tendsto
      (hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT_skewNormalPDFReal hs m α)
      (integrable_skewNormalPDFReal m s α)
      ((tendsto_cdf_gaussianReal_sub_two_mul_owensT_atBot α).comp (tendsto_div_atBot hs m))
      ((tendsto_cdf_gaussianReal_sub_two_mul_owensT_atTop α).comp
        ((tendsto_atTop_add_const_right _ (-m) tendsto_id).atTop_div_const hs)), sub_zero]
  rw [funext (skewNormalPDF_eq_ofReal m s α), ← ofReal_integral_eq_lintegral_ofReal
    (integrable_skewNormalPDFReal m s α) (.of_forall (skewNormalPDFReal_nonneg m s α)), h,
    ENNReal.ofReal_one]

/-- **The cdf of the skew-normal law** is `Φ(y) - 2 * T(y, α)` with `y = (x - m) / s`, where
`T` is Owen's T function. -/
theorem cdf_skewNormalMeasure_eq (hs : 0 < s) (m α x : ℝ) :
    cdf (skewNormalMeasure m s α) x =
      cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α := by
  have := isProbabilityMeasure_skewNormalMeasure hs m α
  rw [cdf_eq_real, measureReal_def, skewNormalMeasure_Iic hs, ENNReal.toReal_ofReal]
  rw [← integral_skewNormalPDFReal_Iic hs]
  exact setIntegral_nonneg measurableSet_Iic fun y _ => skewNormalPDFReal_nonneg m s α y

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a skew-normal law has a density. -/
theorem hasPDF_of_hasLaw_skewNormalMeasure (hX : HasLaw X (skewNormalMeasure m s α) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_skewNormalPDF m s α).aemeasurable
    (by rwa [skewNormalMeasure_eq_withDensity] at hX)

/-- The density of a skew-normal law is `skewNormalPDF`. -/
theorem pdf_eq_skewNormalPDF_of_hasLaw_skewNormalMeasure
    (hX : HasLaw X (skewNormalMeasure m s α) P) :
    pdf X P volume =ᵐ[volume] skewNormalPDF m s α :=
  pdf_eq_of_hasLaw_withDensity (measurable_skewNormalPDF m s α).aemeasurable
    (by rwa [skewNormalMeasure_eq_withDensity] at hX)

/-- The Radon–Nikodym derivative of a skew-normal law against Lebesgue measure is
`skewNormalPDF`. -/
theorem rnDeriv_skewNormalMeasure (m s α : ℝ) :
    (skewNormalMeasure m s α).rnDeriv volume =ᵐ[volume] skewNormalPDF m s α := by
  rw [skewNormalMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity volume (measurable_skewNormalPDF m s α)

/-! ### Gaussian specialization -/

/-- **Shape zero is Gaussian.** For positive scale `s`, the skew-normal law of shape `0` is the
Gaussian law with mean `m` and variance `s ^ 2`. -/
theorem skewNormalMeasure_eq_gaussianReal (hs : 0 < s) (m : ℝ) :
    skewNormalMeasure m s 0 = gaussianReal m (s ^ 2).toNNReal := by
  have hv : ((s ^ 2).toNNReal : ℝ) = s ^ 2 := Real.coe_toNNReal _ (by positivity)
  rw [skewNormalMeasure_eq_withDensity,
    gaussianReal_of_var_ne_zero m (by rw [← NNReal.coe_ne_zero, hv]; positivity)]
  congr 1
  ext x
  rw [skewNormalPDF_eq_ofReal, gaussianPDF, skewNormalPDFReal_of_pos hs, zero_mul,
    cdf_gaussianReal_self 0 one_ne_zero, gaussianPDFReal_zero_one, gaussianPDFReal_def, hv]
  congr 1
  have hsqrt : √(2 * Real.pi * s ^ 2) = √(2 * Real.pi) * s := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hs.le]
  have hexp : -(((x - m) / s) ^ 2 / 2) = -(x - m) ^ 2 / (2 * s ^ 2) := by
    field_simp
  rw [hsqrt, hexp]
  have := Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)
  field_simp

/-! ### Affine transport and shape reflection -/

/-- **Affine transport of the skew-normal law, positive slope.** For `b > 0`, the image of the
skew-normal law with location `m`, scale `s` and shape `α` under `x ↦ a + b * x` is the
skew-normal law with location `a + b * m`, scale `b * s` and the same shape. -/
theorem map_affine_skewNormalMeasure_of_pos (m s α : ℝ) {a b : ℝ} (hb : 0 < b) :
    (skewNormalMeasure m s α).map (fun x => a + b * x) =
      skewNormalMeasure (a + b * m) (b * s) α := by
  rw [skewNormalMeasure_eq_withDensity, map_affine_withDensity_volume _ hb.ne',
    skewNormalMeasure_eq_withDensity]
  congr 1
  funext x
  rw [affineDensity_apply, skewNormalPDF, skewNormalPDF, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rcases le_or_gt s 0 with hs | hs
  · rw [skewNormalPDFReal_of_nonpos hs, skewNormalPDFReal_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos hb.le hs), mul_zero]
  have hy : ((x - a) / b - m) / s = (x - (a + b * m)) / (b * s) := by
    field_simp
    ring
  rw [skewNormalPDFReal_of_pos hs, skewNormalPDFReal_of_pos (mul_pos hb hs), hy, abs_of_pos hb]
  field_simp

/-- **Affine transport of the skew-normal law, negative slope.** For `b < 0`, the image of the
skew-normal law with location `m`, scale `s` and shape `α` under `x ↦ a + b * x` is the
skew-normal law with location `a + b * m`, scale `|b| * s` and the reflected shape `-α`. -/
theorem map_affine_skewNormalMeasure_of_neg (m s α : ℝ) {a b : ℝ} (hb : b < 0) :
    (skewNormalMeasure m s α).map (fun x => a + b * x) =
      skewNormalMeasure (a + b * m) (|b| * s) (-α) := by
  rw [skewNormalMeasure_eq_withDensity, map_affine_withDensity_volume _ hb.ne,
    skewNormalMeasure_eq_withDensity]
  congr 1
  funext x
  rw [affineDensity_apply, skewNormalPDF, skewNormalPDF, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rcases le_or_gt s 0 with hs | hs
  · rw [skewNormalPDFReal_of_nonpos hs, skewNormalPDFReal_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg b) hs), mul_zero]
  have hbs : 0 < |b| * s := mul_pos (abs_pos.mpr hb.ne) hs
  -- The standardized point changes sign, which the even density `φ` absorbs and the shape records.
  have hy : ((x - a) / b - m) / s = -((x - (a + b * m)) / (|b| * s)) := by
    have := hb.ne
    rw [abs_of_neg hb]
    field_simp
    ring
  have hφ (y : ℝ) : gaussianPDFReal 0 1 (-y) = gaussianPDFReal 0 1 y := by
    rw [gaussianPDFReal_zero_one, gaussianPDFReal_zero_one, neg_sq]
  rw [skewNormalPDFReal_of_pos hs, skewNormalPDFReal_of_pos hbs, hy, hφ, mul_neg, ← neg_mul,
    abs_of_neg hb]
  field_simp

/-- **Shape reflection.** If `X` is skew-normal with location `m`, scale `s` and shape `α`, then
`-X` is skew-normal with location `-m`, scale `s` and shape `-α`. -/
theorem map_neg_skewNormalMeasure (m s α : ℝ) :
    (skewNormalMeasure m s α).map (fun x => -x) = skewNormalMeasure (-m) s (-α) := by
  have h := map_affine_skewNormalMeasure_of_neg m s α (a := 0) (b := -1) (by norm_num)
  simp only [zero_add, neg_one_mul, abs_neg, abs_one, one_mul] at h
  exact h

/-- For a positive scale, every skew-normal law is the image of the standard skew-normal law with
the same shape under `x ↦ m + s * x`. -/
theorem skewNormalMeasure_eq_map_skewNormalMeasure_zero_one (hs : 0 < s) (m α : ℝ) :
    skewNormalMeasure m s α = (skewNormalMeasure 0 1 α).map (fun x => m + s * x) := by
  rw [map_affine_skewNormalMeasure_of_pos 0 1 α hs, mul_zero, add_zero, mul_one]

/-! ### The quantile function -/

/-- For a positive scale the skew-normal cdf is strictly increasing. -/
theorem strictMono_cdf_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    StrictMono (cdf (skewNormalMeasure m s α)) := by
  have h : cdf (skewNormalMeasure m s α) = fun x =>
      cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α :=
    funext (cdf_skewNormalMeasure_eq hs m α)
  rw [h]
  exact strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT_skewNormalPDFReal hs m α x).deriv]
    exact skewNormalPDFReal_pos hs m α x

/-- For a positive scale the skew-normal cdf is continuous. -/
theorem continuous_cdf_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    Continuous (cdf (skewNormalMeasure m s α)) := by
  have h : cdf (skewNormalMeasure m s α) = fun x =>
      cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α :=
    funext (cdf_skewNormalMeasure_eq hs m α)
  rw [h]
  exact continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT_skewNormalPDFReal hs m α x).continuousAt

/-- **The quantile function of the skew-normal law** is the Owen-T root: at a level `0 < u < 1`,
the quantile is the unique `x` with `Φ(y) - 2 * T(y, α) = u`, where `y = (x - m) / s`. -/
theorem quantile_skewNormalMeasure_eq_iff (hs : 0 < s) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (skewNormalMeasure m s α).quantile u = x ↔
      cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α = u := by
  rw [← cdf_skewNormalMeasure_eq hs]
  constructor
  · rintro rfl
    exact Measure.cdf_quantile _ (continuous_cdf_skewNormalMeasure hs m α) hu.1 hu.2
  · intro hx
    exact Measure.quantile_eq_of_cdf_eq _
      ((strictMono_cdf_skewNormalMeasure hs m α).strictMonoOn _) hx hu

/-! ### Parameter measurability -/

/-- **The skew-normal family is measurable in its parameters**, so it can be packaged as a
kernel. -/
@[fun_prop]
theorem measurable_skewNormalMeasure :
    Measurable fun p : ℝ × ℝ × ℝ => skewNormalMeasure p.1 p.2.1 p.2.2 := by
  simp only [skewNormalMeasure_eq_withDensity]
  exact measurable_withDensity (μ := volume) measurable_uncurry_skewNormalPDF

end Probability

end TauCeti
