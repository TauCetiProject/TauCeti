/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Mixture.Basic
public import TauCeti.Probability.Distributions.MultivariateT.Basic

/-!
# The density of a multivariate t law

For positive degrees of freedom `ν` and positive-definite scale `S` on a `d`-dimensional
Euclidean space, the multivariate t law with location `m` has the classical density

`Γ((ν + d) / 2) / (Γ(ν / 2) (ν π)^(d/2) √(det S)) * (1 + ⟪x - m, S⁻¹ (x - m)⟫ / ν)^(-(ν + d)/2)`

with respect to Lebesgue measure. A scale that is not positive definite gives a singular law
(`TauCeti.Probability.mutuallySingular_multivariateTMeasure_volume`), so this is the full
absolutely continuous range of the family.

Conditionally on the chi-squared factor `V = v`, the defining variable `m + √(ν / V) • Z` is
Gaussian with mean `m` and covariance `(ν / v) • S`. The law is therefore a chi-squared mixture
of Gaussian laws, and its density is the mixture of their densities. Integrating out `v` is a
Gamma integral, which produces the closed form above.

## Main definitions

* `TauCeti.Probability.multivariateTPDFReal`: the real-valued density, zero outside the valid
  parameter range;
* `TauCeti.Probability.multivariateTPDF`: its `ℝ≥0∞`-valued companion.

## Main results

* `TauCeti.Probability.multivariateTMeasure_eq_withDensity`: the density presentation;
* `TauCeti.Probability.lintegral_multivariateTPDF_eq_one` and
  `TauCeti.Probability.integral_multivariateTPDFReal_eq_one`: normalization;
* `TauCeti.Probability.hasPDF_of_hasLaw_multivariateTMeasure`,
  `TauCeti.Probability.pdf_eq_multivariateTPDF_of_hasLaw_multivariateTMeasure` and
  `TauCeti.Probability.rnDeriv_multivariateTMeasure`: the density interface.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal RealInnerProductSpace MatrixOrder

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The density -/

open Classical in
/-- The density of the multivariate t law with location `m`, scale `S` and `ν` degrees of
freedom, as a real number. It is the classical formula when `0 < ν` and `S` is positive definite,
and `0` otherwise; in the excluded cases the law is zero or singular. -/
def multivariateTPDFReal (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν : ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  if 0 < ν ∧ S.PosDef then
    Real.Gamma ((ν + Fintype.card ι) / 2) /
        (Real.Gamma (ν / 2) * (ν * π) ^ ((Fintype.card ι : ℝ) / 2) * √S.det) *
      (1 + ⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫ / ν) ^ (-((ν + Fintype.card ι) / 2))
  else 0

/-- The `ℝ≥0∞`-valued companion to `TauCeti.Probability.multivariateTPDFReal`. -/
def multivariateTPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν : ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal (multivariateTPDFReal m S ν x)

variable {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} {ν : ℝ}

/-- The `ℝ≥0∞`-valued density is the `ENNReal.ofReal` lift of the real-valued one. -/
theorem multivariateTPDF_eq_ofReal (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν : ℝ)
    (x : EuclideanSpace ℝ ι) :
    multivariateTPDF m S ν x = ENNReal.ofReal (multivariateTPDFReal m S ν x) := (rfl)

/-- For positive degrees of freedom and positive-definite scale, the density is the classical
multivariate t formula. -/
@[simp]
theorem multivariateTPDFReal_of_posDef (m : EuclideanSpace ℝ ι) (hν : 0 < ν) (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) :
    multivariateTPDFReal m S ν x =
      Real.Gamma ((ν + Fintype.card ι) / 2) /
          (Real.Gamma (ν / 2) * (ν * π) ^ ((Fintype.card ι : ℝ) / 2) * √S.det) *
        (1 + ⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫ / ν) ^ (-((ν + Fintype.card ι) / 2)) := by
  rw [multivariateTPDFReal, ite_eq_left ⟨hν, hS⟩]

/-- For nonpositive degrees of freedom the density vanishes. -/
@[simp]
theorem multivariateTPDFReal_of_nonpos (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hν : ν ≤ 0)
    (x : EuclideanSpace ℝ ι) : multivariateTPDFReal m S ν x = 0 := by
  rw [multivariateTPDFReal, ite_eq_right fun h => (not_lt.mpr hν) h.1]

/-- For a scale matrix that is not positive definite the density vanishes. -/
@[simp]
theorem multivariateTPDFReal_of_not_posDef (m : EuclideanSpace ℝ ι) (ν : ℝ) (hS : ¬ S.PosDef)
    (x : EuclideanSpace ℝ ι) : multivariateTPDFReal m S ν x = 0 := by
  rw [multivariateTPDFReal, ite_eq_right fun h => hS h.2]

/-- For positive degrees of freedom and positive-definite scale, the density is positive
everywhere. -/
theorem multivariateTPDFReal_pos (m : EuclideanSpace ℝ ι) (hν : 0 < ν) (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) : 0 < multivariateTPDFReal m S ν x := by
  have hq := (Matrix.isPositive_toEuclideanLin_iff.mpr hS.inv.posSemidef).inner_nonneg_right
    (x - m)
  have hdet := hS.det_pos
  rw [multivariateTPDFReal_of_posDef m hν hS]
  positivity

/-- The real-valued density is nonnegative at every parameter. -/
theorem multivariateTPDFReal_nonneg (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν : ℝ)
    (x : EuclideanSpace ℝ ι) : 0 ≤ multivariateTPDFReal m S ν x := by
  by_cases h : 0 < ν ∧ S.PosDef
  · exact (multivariateTPDFReal_pos m h.1 h.2 x).le
  · simp [multivariateTPDFReal, h]

/-- Converting the `ℝ≥0∞`-valued density back to reals recovers the real-valued density. -/
@[simp]
theorem toReal_multivariateTPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν : ℝ)
    (x : EuclideanSpace ℝ ι) : (multivariateTPDF m S ν x).toReal = multivariateTPDFReal m S ν x :=
  ENNReal.toReal_ofReal (multivariateTPDFReal_nonneg m S ν x)

/-- The real-valued density is measurable. -/
@[fun_prop]
theorem measurable_multivariateTPDFReal (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν : ℝ) :
    Measurable (multivariateTPDFReal m S ν) := by
  by_cases h : 0 < ν ∧ S.PosDef
  · rw [funext (multivariateTPDFReal_of_posDef m h.1 h.2)]
    fun_prop
  · have hzero : multivariateTPDFReal m S ν = fun _ => 0 :=
      funext fun x => by simp [multivariateTPDFReal, h]
    rw [hzero]
    exact measurable_const

/-- The `ℝ≥0∞`-valued density is measurable. -/
@[fun_prop]
theorem measurable_multivariateTPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν : ℝ) :
    Measurable (multivariateTPDF m S ν) :=
  (measurable_multivariateTPDFReal m S ν).ennreal_ofReal

/-! ### The density of the law -/

/-- The density of the Gaussian component with covariance `(ν / v) • S`, written so that it is
jointly measurable in `(v, x)`. For `0 < v` it is `multivariateGaussianPDFReal m ((ν / v) • S)`. -/
private def componentDensity (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (ν v : ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) * ((ν / v) ^ Fintype.card ι * S.det) ^ (-(1 : ℝ) / 2) *
    exp (-((ν / v)⁻¹ * ⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫) / 2)

private theorem componentDensity_nonneg (hν : 0 < ν) (hS : S.PosDef) {v : ℝ} (hv : 0 < v)
    (x : EuclideanSpace ℝ ι) : 0 ≤ componentDensity m S ν v x := by
  have := hS.det_pos
  unfold componentDensity
  positivity

private theorem multivariateGaussian_smul_eq_withDensity (m : EuclideanSpace ℝ ι) (hν : 0 < ν)
    (hS : S.PosDef) {v : ℝ} (hv : 0 < v) :
    multivariateGaussian m ((ν / v) • S) =
      volume.withDensity fun x => ENNReal.ofReal (componentDensity m S ν v x) := by
  have hc : 0 < ν / v := div_pos hν hv
  rw [multivariateGaussian_eq_withDensity (hS.smul hc)]
  congr 1
  funext x
  rw [multivariateGaussianPDF_def, multivariateGaussianPDFReal_def]
  beta_reduce
  have hinv : ((ν / v) • S)⁻¹ = (ν / v)⁻¹ • S⁻¹ := by
    simpa [Units.smul_def] using
      Matrix.inv_smul' S (Units.mk0 _ hc.ne') hS.det_pos.ne'.isUnit
  rw [Matrix.det_smul, hinv, componentDensity]
  congr 3
  simp [inner_smul_right]

/-- On the positive half-line, the chi-squared density times the Gaussian component density is a
constant multiple of the Gamma integrand `v ^ ((ν + d) / 2 - 1) * exp (-((1 + q / ν) / 2 * v))`,
where `q` is the Mahalanobis quadratic form at `x`. -/
private theorem chiSquaredPDFReal_mul_componentDensity (m : EuclideanSpace ℝ ι) (hν : 0 < ν)
    (hS : S.PosDef) (x : EuclideanSpace ℝ ι) {v : ℝ} (hv : 0 < v) :
    chiSquaredPDFReal ν v * componentDensity m S ν v x =
      (2 * π) ^ (-(Fintype.card ι : ℝ) / 2) * ν ^ (-((Fintype.card ι : ℝ) / 2)) *
          S.det ^ (-(1 : ℝ) / 2) / (2 ^ (ν / 2) * Real.Gamma (ν / 2)) *
        (v ^ ((ν + Fintype.card ι) / 2 - 1) *
          exp (-((1 + ⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫ / ν) / 2 * v))) := by
  set q := ⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  have e1 : ((ν / v) ^ Fintype.card ι * S.det) ^ (-(1 : ℝ) / 2) =
      ν ^ (-(d / 2)) * v ^ (d / 2) * S.det ^ (-(1 : ℝ) / 2) := by
    have := hS.det_pos
    simp (disch := positivity) only [Real.mul_rpow, ← Real.rpow_natCast_mul, Real.div_rpow,
      neg_div, mul_one_div, Real.rpow_neg, ← hd_def]
    field_simp
  have e2 : v ^ (ν / 2 - 1) * v ^ (d / 2) = v ^ ((ν + d) / 2 - 1) := by
    rw [← Real.rpow_add hv]
    congr 1
    ring
  have e3 : exp (-v / 2) * exp (-((ν / v)⁻¹ * q) / 2) = exp (-((1 + q / ν) / 2 * v)) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  rw [componentDensity, chiSquaredPDFReal_of_nonneg hv.le, e1, ← e2, ← e3]
  ring

/-- Integrating out the chi-squared factor of the Gaussian component densities gives the
multivariate t density. This is a Gamma integral. -/
private theorem integral_chiSquaredPDFReal_mul_componentDensity (m : EuclideanSpace ℝ ι)
    (hν : 0 < ν) (hS : S.PosDef) (x : EuclideanSpace ℝ ι) :
    ∫ v, chiSquaredPDFReal ν v * componentDensity m S ν v x = multivariateTPDFReal m S ν x := by
  set q := ⟪x - m, S⁻¹.toEuclideanLin (x - m)⟫ with hq_def
  have hq : 0 ≤ q :=
    (Matrix.isPositive_toEuclideanLin_iff.mpr hS.inv.posSemidef).inner_nonneg_right (x - m)
  have hD := hS.det_pos
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  -- The integrand vanishes on the negative half-line, and the point `0` is Lebesgue-null.
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (s := Ioi 0)]
  swap
  · filter_upwards [Measure.ae_ne volume 0] with v hv0 hv
    simp [chiSquaredPDFReal_of_neg (lt_of_le_of_ne (not_lt.mp hv) hv0)]
  rw [setIntegral_congr_fun measurableSet_Ioi
      fun v hv => chiSquaredPDFReal_mul_componentDensity m hν hS x hv,
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) (by positivity),
    multivariateTPDFReal_of_posDef m hν hS, ← hq_def, ← hd_def, one_div_div]
  -- It remains to compare the two closed forms, written with nonnegative real powers.
  have : 0 < Real.Gamma (ν / 2) := Real.Gamma_pos_of_pos (by positivity)
  simp (disch := positivity) only [neg_div, Real.rpow_neg, Real.mul_rpow, Real.div_rpow,
    add_div ν d, Real.rpow_add, Real.sqrt_eq_rpow]
  field_simp

/-- The chi-squared mixture of the Gaussian component densities is the multivariate t density. -/
private theorem lintegral_componentDensity (m : EuclideanSpace ℝ ι) (hν : 0 < ν) (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) :
    ∫⁻ v, ENNReal.ofReal (componentDensity m S ν v x) ∂chiSquaredMeasure ν =
      multivariateTPDF m S ν x := by
  let h : ℝ → ℝ := fun v => chiSquaredPDFReal ν v * componentDensity m S ν v x
  have hint : ∫ v, h v = multivariateTPDFReal m S ν x :=
    integral_chiSquaredPDFReal_mul_componentDensity m hν hS x
  have hinteg : Integrable h := Integrable.of_integral_ne_zero
    (by rw [hint]; exact (multivariateTPDFReal_pos m hν hS x).ne')
  have hnonneg : 0 ≤ᵐ[volume] h := by
    filter_upwards [Measure.ae_ne volume 0] with v hv0
    rcases lt_or_gt_of_ne hv0 with hv | hv
    · simp [h, chiSquaredPDFReal_of_neg hv]
    · exact mul_nonneg (chiSquaredPDFReal_nonneg hν.le v) (componentDensity_nonneg hν hS hv x)
  rw [chiSquaredMeasure_eq_withDensity hν,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_chiSquaredPDF ν)
      (by unfold componentDensity; fun_prop),
    multivariateTPDF_eq_ofReal, ← hint, ofReal_integral_eq_lintegral_ofReal hinteg hnonneg]
  refine lintegral_congr fun v => ?_
  simp only [Pi.mul_apply, h, chiSquaredPDF_eq_ofReal]
  rw [ENNReal.ofReal_mul (chiSquaredPDFReal_nonneg hν.le v)]

/-- **The density of a multivariate t law.** For positive degrees of freedom and positive-definite
scale, the multivariate t law is Lebesgue measure weighted by `multivariateTPDF m S ν`. -/
theorem multivariateTMeasure_eq_withDensity (m : EuclideanSpace ℝ ι) (hν : 0 < ν)
    (hS : S.PosDef) :
    multivariateTMeasure m S ν = volume.withDensity (multivariateTPDF m S ν) := by
  have := isProbabilityMeasure_chiSquaredMeasure hν.le
  rw [multivariateTMeasure_eq_bind m hν hS.posSemidef,
    Measure.bind_eq_withDensity_of_ae_eq _ volume
      (f := fun v x => ENNReal.ofReal (componentDensity m S ν v x))
      (by unfold componentDensity; fun_prop) ?_]
  · congr 1
    funext x
    exact lintegral_componentDensity m hν hS x
  · filter_upwards [ae_pos_chiSquaredMeasure hν] with v hv
    exact multivariateGaussian_smul_eq_withDensity m hν hS hv

/-- For positive degrees of freedom and positive-definite scale, the `ℝ≥0∞`-valued density
integrates to one. -/
theorem lintegral_multivariateTPDF_eq_one (m : EuclideanSpace ℝ ι) (hν : 0 < ν)
    (hS : S.PosDef) : ∫⁻ x, multivariateTPDF m S ν x = 1 := by
  have := isProbabilityMeasure_multivariateTMeasure m hν hS.posSemidef
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← multivariateTMeasure_eq_withDensity m hν hS, measure_univ]

/-- For positive degrees of freedom and positive-definite scale, the real-valued density
integrates to one. -/
theorem integral_multivariateTPDFReal_eq_one (m : EuclideanSpace ℝ ι) (hν : 0 < ν)
    (hS : S.PosDef) : ∫ x, multivariateTPDFReal m S ν x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (.of_forall (multivariateTPDFReal_nonneg m S ν))
    (measurable_multivariateTPDFReal m S ν).aestronglyMeasurable]
  simp_rw [← multivariateTPDF_eq_ofReal]
  rw [lintegral_multivariateTPDF_eq_one m hν hS, ENNReal.toReal_one]

/-- **The Radon–Nikodym derivative of a multivariate t law** with positive-definite scale with
respect to Lebesgue measure is its density. -/
theorem rnDeriv_multivariateTMeasure (m : EuclideanSpace ℝ ι) (hν : 0 < ν) (hS : S.PosDef) :
    (multivariateTMeasure m S ν).rnDeriv volume =ᵐ[volume] multivariateTPDF m S ν := by
  rw [multivariateTMeasure_eq_withDensity m hν hS]
  exact Measure.rnDeriv_withDensity _ (measurable_multivariateTPDF m S ν)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}

/-- A random vector with a multivariate t law of positive-definite scale has a density. -/
theorem hasPDF_of_hasLaw_multivariateTMeasure (hν : 0 < ν) (hS : S.PosDef)
    (hX : HasLaw X (multivariateTMeasure m S ν) P) : HasPDF X P :=
  Probability.hasPDF_of_hasLaw_withDensity (measurable_multivariateTPDF m S ν).aemeasurable
    (by rwa [← multivariateTMeasure_eq_withDensity m hν hS])

/-- The density of a random vector with a multivariate t law of positive-definite scale is
`multivariateTPDF m S ν`. -/
theorem pdf_eq_multivariateTPDF_of_hasLaw_multivariateTMeasure (hν : 0 < ν) (hS : S.PosDef)
    (hX : HasLaw X (multivariateTMeasure m S ν) P) :
    pdf X P =ᵐ[volume] multivariateTPDF m S ν :=
  Probability.pdf_eq_of_hasLaw_withDensity (measurable_multivariateTPDF m S ν).aemeasurable
    (by rwa [← multivariateTMeasure_eq_withDensity m hν hS])

end TauCeti.Probability
