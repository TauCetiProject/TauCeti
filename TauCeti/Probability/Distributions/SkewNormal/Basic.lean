/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Cdf
public import TauCeti.Probability.Density
public import TauCeti.Probability.Quantile
public import TauCeti.Probability.Distributions.Gaussian.OwensT
import TauCeti.Probability.Distributions.Affine

/-!
# The skew-normal distribution

Write `φ = gaussianPDFReal 0 1` and `Φ = cdf (gaussianReal 0 1)` for the standard Gaussian density
and cumulative distribution function, and `T = Real.owensT` for Owen's T function. The
skew-normal law with location `m`, scale `s > 0` and shape `α` has density

`f(x) = 2 / s * φ(y) * Φ(α * y)`, where `y = (x - m) / s`,

and it is *defined* here as `volume.withDensity` of that density. The shape `α` tilts the Gaussian
bell: `α = 0` recovers the Gaussian law with mean `m` and variance `s ^ 2`, and changing the sign
of `α` reflects the law about its location. Its cumulative distribution function is
`Φ(y) - 2 * T(y, α)`, which is continuous and strictly increasing, so each quantile is the unique
real root of `Φ(y) - 2 * T(y, α) = u`.

**Boundary.** For `s ≤ 0` there is no skew-normal law: `skewNormalMeasure m s α` and its density
are *defined* to vanish there (`skewNormalMeasure_of_nonpos`, `skewNormalPDFReal_of_nonpos`). The
density presentation and the affine transport `map_affine_skewNormalMeasure` hold at every
parameter, which makes the family measurable in its parameters with no case split.

## Main definitions

* `TauCeti.Probability.skewNormalPDFReal` — the real-valued density;
* `TauCeti.Probability.skewNormalPDF` — its `ℝ≥0∞`-valued companion;
* `TauCeti.Probability.skewNormalMeasure` — the law, as Lebesgue measure weighted by the density.

## Main results

* `isProbabilityMeasure_skewNormalMeasure` — it is a probability measure when `0 < s`;
* `hasPDF_of_hasLaw_skewNormalMeasure`, `pdf_eq_skewNormalPDF_of_hasLaw_skewNormalMeasure` and
  `rnDeriv_skewNormalMeasure` — the density interfaces;
* `cdf_skewNormalMeasure_eq` — the cdf is `Φ(y) - 2 * T(y, α)`;
* `strictMono_cdf_skewNormalMeasure` and `support_skewNormalMeasure` — the cdf is strictly
  increasing and the topological support is all of `ℝ`;
* `quantile_skewNormalMeasure_eq_iff` — the quantile at `0 < u < 1` is the unique root of
  `Φ(y) - 2 * T(y, α) = u`;
* `skewNormalMeasure_zero_shape` — at shape `0` the law is the Gaussian law `N(m, s ^ 2)`;
* `map_affine_skewNormalMeasure` and `map_neg_skewNormalMeasure` — the affine image `a + b X`
  with `b ≠ 0` has location `a + b * m`, scale `|b| * s` and shape `sign b * α`; in particular
  `-X` has location `-m` and shape `-α`;
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

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {m s α x : ℝ}

/-! ### The density -/

/-- The density of the skew-normal law with location `m`, scale `s` and shape `α`, as a
real-valued function: `2 / s * φ(y) * Φ(α * y)` with `y = (x - m) / s`, where `φ` and `Φ` are the
standard Gaussian density and cdf.

For `s ≤ 0` there is no such law and the density is `0`. -/
def skewNormalPDFReal (m s α x : ℝ) : ℝ :=
  if 0 < s then
    2 / s * gaussianPDFReal 0 1 ((x - m) / s) * cdf (gaussianReal 0 1) (α * ((x - m) / s))
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

/-- For a positive scale the density is `2 / s * φ(y) * Φ(α * y)` with `y = (x - m) / s`. -/
@[simp]
theorem skewNormalPDFReal_of_pos (hs : 0 < s) (m α x : ℝ) :
    skewNormalPDFReal m s α x =
      2 / s * gaussianPDFReal 0 1 ((x - m) / s) * cdf (gaussianReal 0 1) (α * ((x - m) / s)) := by
  rw [skewNormalPDFReal, ite_eq_left hs]

/-- Outside the valid parameter range the `ℝ≥0∞`-valued density vanishes. -/
@[simp]
theorem skewNormalPDF_of_nonpos (hs : s ≤ 0) (m α x : ℝ) : skewNormalPDF m s α x = 0 := by
  rw [skewNormalPDF_eq_ofReal, skewNormalPDFReal_of_nonpos hs, ENNReal.ofReal_zero]

/-- For a positive scale the `ℝ≥0∞`-valued density is the coercion of
`2 / s * φ(y) * Φ(α * y)` with `y = (x - m) / s`. -/
@[simp]
theorem skewNormalPDF_of_pos (hs : 0 < s) (m α x : ℝ) :
    skewNormalPDF m s α x = ENNReal.ofReal
      (2 / s * gaussianPDFReal 0 1 ((x - m) / s) * cdf (gaussianReal 0 1) (α * ((x - m) / s))) := by
  rw [skewNormalPDF_eq_ofReal, skewNormalPDFReal_of_pos hs]

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
  simp only [skewNormalPDFReal]
  have hy : Measurable fun q : (ℝ × ℝ × ℝ) × ℝ => (q.2 - q.1.1) / q.1.2.1 := by fun_prop
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst.snd.fst)
    (((measurable_const.div measurable_fst.snd.fst).mul
      ((measurable_gaussianPDFReal 0 1).comp hy)).mul
      ((monotone_cdf _).measurable.comp (measurable_fst.snd.snd.mul hy)))
    measurable_const

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
  -- The factor `Φ(α * y)` is at most `1`, leaving a rescaled Gaussian density.
  have hdom : Integrable fun x : ℝ => 2 / s * gaussianPDFReal 0 1 ((x - m) / s) :=
    (((integrable_gaussianPDFReal 0 1).comp_div hs.ne').comp_sub_right m).const_mul _
  refine hdom.mono' (measurable_skewNormalPDFReal m s α).aestronglyMeasurable
    (.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (skewNormalPDFReal_nonneg m s α x), skewNormalPDFReal_of_pos hs]
  have := gaussianPDFReal_nonneg 0 1 ((x - m) / s)
  exact mul_le_of_le_one_right (by positivity) (cdf_le_one _ _)

/-- The function `x ↦ Φ(y) - 2 * T(y, α)` with `y = (x - m) / s` has the skew-normal density as
its derivative. -/
private theorem hasDerivAt_skewNormalCdf (hs : 0 < s) (m α x : ℝ) :
    HasDerivAt
      (fun y => cdf (gaussianReal 0 1) ((y - m) / s) - 2 * Real.owensT ((y - m) / s) α)
      (skewNormalPDFReal m s α x) x := by
  have hy : HasDerivAt (fun y => (y - m) / s) (1 / s) x :=
    ((hasDerivAt_id' x).sub_const m).div_const s
  rw [skewNormalPDFReal_of_pos hs]
  refine ((hasDerivAt_cdf_gaussianReal_sub_two_mul_owensT α ((x - m) / s)).comp x hy).congr_deriv
    ?_
  ring

/-- **The skew-normal mass below a point.** The skew-normal density integrates over `(-∞, x]` to
`Φ(y) - 2 * T(y, α)` with `y = (x - m) / s`. -/
theorem integral_Iic_skewNormalPDFReal (hs : 0 < s) (m α x : ℝ) :
    ∫ y in Iic x, skewNormalPDFReal m s α y =
      cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α := by
  have hbot : Tendsto (fun x : ℝ => (x - m) / s) atBot atBot :=
    (tendsto_atBot_add_const_right _ (-m) tendsto_id).atBot_div_const hs
  rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun y _ => hasDerivAt_skewNormalCdf hs m α y)
    (integrable_skewNormalPDFReal m s α).integrableOn
    ((tendsto_cdf_gaussianReal_sub_two_mul_owensT_atBot α).comp hbot), sub_zero]

/-- For a positive scale the skew-normal density has total integral `1`. -/
theorem integral_skewNormalPDFReal (hs : 0 < s) (m α : ℝ) :
    ∫ x, skewNormalPDFReal m s α x = 1 := by
  have hbot : Tendsto (fun x : ℝ => (x - m) / s) atBot atBot :=
    (tendsto_atBot_add_const_right _ (-m) tendsto_id).atBot_div_const hs
  have htop : Tendsto (fun x : ℝ => (x - m) / s) atTop atTop :=
    (tendsto_atTop_add_const_right _ (-m) tendsto_id).atTop_div_const hs
  rw [integral_of_hasDerivAt_of_tendsto (hasDerivAt_skewNormalCdf hs m α)
    (integrable_skewNormalPDFReal m s α)
    ((tendsto_cdf_gaussianReal_sub_two_mul_owensT_atBot α).comp hbot)
    ((tendsto_cdf_gaussianReal_sub_two_mul_owensT_atTop α).comp htop), sub_zero]

/-! ### The measure -/

/-- The skew-normal law with location `m`, scale `s` and shape `α`: Lebesgue measure weighted by
`2 / s * φ(y) * Φ(α * y)` with `y = (x - m) / s`.

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

/-- The skew-normal law of a measurable set is the integral of the real density over it. -/
private theorem skewNormalMeasure_apply (m s α : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    skewNormalMeasure m s α A = ENNReal.ofReal (∫ y in A, skewNormalPDFReal m s α y) := by
  have hpdf : skewNormalPDF m s α = fun y => ENNReal.ofReal (skewNormalPDFReal m s α y) :=
    funext (skewNormalPDF_eq_ofReal m s α)
  rw [skewNormalMeasure_eq_withDensity, withDensity_apply _ hA, hpdf,
    ofReal_integral_eq_lintegral_ofReal (integrable_skewNormalPDFReal m s α).integrableOn
      (.of_forall (skewNormalPDFReal_nonneg m s α))]

/-- For a positive scale the skew-normal law is a probability measure. -/
theorem isProbabilityMeasure_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    IsProbabilityMeasure (skewNormalMeasure m s α) := by
  constructor
  rw [skewNormalMeasure_apply m s α MeasurableSet.univ, Measure.restrict_univ,
    integral_skewNormalPDFReal hs, ENNReal.ofReal_one]

/-- The skew-normal law of a lower half-line: the event `{X ≤ x}` has mass `Φ(y) - 2 * T(y, α)`
with `y = (x - m) / s`. -/
theorem skewNormalMeasure_Iic (hs : 0 < s) (m α x : ℝ) :
    skewNormalMeasure m s α (Iic x) =
      ENNReal.ofReal (cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α) := by
  rw [skewNormalMeasure_apply m s α measurableSet_Iic, integral_Iic_skewNormalPDFReal hs]

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

/-! ### The cumulative distribution function, support and quantiles -/

/-- **The cdf of the skew-normal law** through Owen's T function: it is `Φ(y) - 2 * T(y, α)` with
`y = (x - m) / s`. -/
theorem cdf_skewNormalMeasure_eq (hs : 0 < s) (m α x : ℝ) :
    cdf (skewNormalMeasure m s α) x =
      cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α := by
  have := isProbabilityMeasure_skewNormalMeasure hs m α
  rw [cdf_eq_real, measureReal_def, skewNormalMeasure_Iic hs, ENNReal.toReal_ofReal]
  rw [← integral_Iic_skewNormalPDFReal hs]
  exact setIntegral_nonneg measurableSet_Iic fun y _ => skewNormalPDFReal_nonneg m s α y

/-- The skew-normal cdf has the skew-normal density as its derivative at every point. -/
theorem hasDerivAt_cdf_skewNormalMeasure (hs : 0 < s) (m α x : ℝ) :
    HasDerivAt (cdf (skewNormalMeasure m s α)) (skewNormalPDFReal m s α x) x := by
  have h : ⇑(cdf (skewNormalMeasure m s α)) =
      fun y => cdf (gaussianReal 0 1) ((y - m) / s) - 2 * Real.owensT ((y - m) / s) α :=
    funext (cdf_skewNormalMeasure_eq hs m α)
  rw [h]
  exact hasDerivAt_skewNormalCdf hs m α x

/-- The skew-normal cdf is continuous. -/
theorem continuous_cdf_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    Continuous (cdf (skewNormalMeasure m s α)) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_cdf_skewNormalMeasure hs m α x).continuousAt

/-- The skew-normal cdf is strictly increasing, since its density is positive everywhere. -/
theorem strictMono_cdf_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    StrictMono (cdf (skewNormalMeasure m s α)) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_cdf_skewNormalMeasure hs m α)
    (skewNormalPDFReal_pos hs m α)

/-- A skew-normal law with positive scale has full topological support. -/
theorem support_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    (skewNormalMeasure m s α).support = univ := by
  have := isProbabilityMeasure_skewNormalMeasure hs m α
  exact Measure.support_eq_univ_of_strictMono_cdf _ (strictMono_cdf_skewNormalMeasure hs m α)

/-- Outside the valid parameter range the skew-normal law is zero and has empty support. -/
theorem support_skewNormalMeasure_of_nonpos (hs : s ≤ 0) (m α : ℝ) :
    (skewNormalMeasure m s α).support = ∅ := by
  rw [skewNormalMeasure_of_nonpos hs, Measure.support_zero]

/-- **The quantile function of the skew-normal law.** At a level `0 < u < 1` the quantile is the
unique real root `x` of `Φ(y) - 2 * T(y, α) = u` with `y = (x - m) / s`. -/
theorem quantile_skewNormalMeasure_eq_iff (hs : 0 < s) (m α : ℝ) {u : ℝ} (hu : u ∈ Ioo 0 1)
    (x : ℝ) :
    (skewNormalMeasure m s α).quantile u = x ↔
      cdf (gaussianReal 0 1) ((x - m) / s) - 2 * Real.owensT ((x - m) / s) α = u := by
  rw [← cdf_skewNormalMeasure_eq hs]
  constructor
  · rintro rfl
    exact Measure.cdf_quantile _ (continuous_cdf_skewNormalMeasure hs m α) hu.1 hu.2
  · rintro rfl
    exact Measure.quantile_cdf _ ((strictMono_cdf_skewNormalMeasure hs m α).strictMonoOn _) hu

/-! ### The Gaussian case, affine transport and parameter measurability -/

/-- **The Gaussian case.** At shape `0` the skew-normal law with location `m` and scale `s > 0` is
the Gaussian law with mean `m` and variance `s ^ 2`. -/
theorem skewNormalMeasure_zero_shape (hs : 0 < s) (m : ℝ) :
    skewNormalMeasure m s 0 = gaussianReal m (s ^ 2).toNNReal := by
  have hv : (s ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    positivity
  rw [skewNormalMeasure_eq_withDensity, gaussianReal_of_var_ne_zero m hv]
  congr 1
  funext x
  rw [skewNormalPDF_eq_ofReal, gaussianPDF, skewNormalPDFReal_of_pos hs, zero_mul,
    cdf_gaussianReal_zero_one, zero_div, Real.erf_zero, add_zero, gaussianPDFReal_zero_one,
    gaussianPDFReal, Real.coe_toNNReal _ (sq_nonneg s),
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.pi) (s ^ 2), Real.sqrt_sq hs.le]
  congr 1
  have hexp : -(((x - m) / s) ^ 2 / 2) = -(x - m) ^ 2 / (2 * s ^ 2) := by
    field_simp
  rw [hexp]
  field_simp

/-- **Affine transport of the skew-normal law.** For `b ≠ 0`, the image of the skew-normal law
with location `m`, scale `s` and shape `α` under `x ↦ a + b * x` is the skew-normal law with
location `a + b * m`, scale `|b| * s` and shape `sign b * α`. -/
theorem map_affine_skewNormalMeasure (m s α : ℝ) {a b : ℝ} (hb : b ≠ 0) :
    (skewNormalMeasure m s α).map (fun x => a + b * x) =
      skewNormalMeasure (a + b * m) (|b| * s) (SignType.sign b * α) := by
  rw [skewNormalMeasure_eq_withDensity, map_affine_withDensity_volume _ hb,
    skewNormalMeasure_eq_withDensity]
  congr 1
  funext x
  rw [affineDensity_apply, skewNormalPDF_eq_ofReal, skewNormalPDF_eq_ofReal,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rcases le_or_gt s 0 with hs | hs
  · rw [skewNormalPDFReal_of_nonpos hs, skewNormalPDFReal_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg b) hs), mul_zero]
  have hbs : 0 < |b| * s := mul_pos (abs_pos.mpr hb) hs
  rw [skewNormalPDFReal_of_pos hs, skewNormalPDFReal_of_pos hbs]
  set y := (x - (a + b * m)) / (|b| * s)
  rcases lt_or_gt_of_ne hb with hb' | hb'
  · -- At a negative slope the standardized point changes sign; `φ` is even.
    have hy : ((x - a) / b - m) / s = -y := by
      simp only [y, abs_of_neg hb']
      field_simp
      ring
    rw [hy, sign_neg hb', abs_of_neg hb', gaussianPDFReal_zero_one, gaussianPDFReal_zero_one,
      neg_sq, SignType.coe_neg_one, mul_neg, ← neg_mul, ← neg_one_mul α]
    field_simp
  · have hy : ((x - a) / b - m) / s = y := by
      simp only [y, abs_of_pos hb']
      field_simp
      ring
    rw [hy, sign_pos hb', abs_of_pos hb', SignType.coe_one, one_mul]
    field_simp

/-- The random-variable form of affine transport: for `b ≠ 0`, if `X` is skew-normal with
location `m`, scale `s` and shape `α`, then `a + b * X` is skew-normal with location `a + b * m`,
scale `|b| * s` and shape `sign b * α`. -/
theorem hasLaw_affine_skewNormalMeasure {a b : ℝ} (hb : b ≠ 0)
    (hX : HasLaw X (skewNormalMeasure m s α) P) :
    HasLaw (fun ω => a + b * X ω)
      (skewNormalMeasure (a + b * m) (|b| * s) (SignType.sign b * α)) P := by
  rw [← map_affine_skewNormalMeasure m s α hb]
  exact (hasLaw_map (measurable_const.add (measurable_const.mul measurable_id)).aemeasurable).comp
    hX

/-- **Shape reflection.** Negating a skew-normal variable negates its location and its shape. -/
theorem map_neg_skewNormalMeasure (m s α : ℝ) :
    (skewNormalMeasure m s α).map (fun x => -x) = skewNormalMeasure (-m) s (-α) := by
  have h := map_affine_skewNormalMeasure m s α (a := 0) (b := -1) (by norm_num)
  simpa [sign_neg (show (-1 : ℝ) < 0 by norm_num)] using h

/-- **The skew-normal family is measurable in its parameters**, so it can be packaged as a
kernel. -/
@[fun_prop]
theorem measurable_skewNormalMeasure :
    Measurable fun p : ℝ × ℝ × ℝ => skewNormalMeasure p.1 p.2.1 p.2.2 := by
  simp only [skewNormalMeasure_eq_withDensity]
  exact measurable_withDensity (μ := volume) measurable_uncurry_skewNormalPDF

end Probability

end TauCeti
