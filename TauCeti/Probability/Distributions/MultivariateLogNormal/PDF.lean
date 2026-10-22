/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.PiLp
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.MultivariateLogNormal.Basic

import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Densities of multivariate log-normal laws

For positive-definite log-covariance, the multivariate log-normal density is the Gaussian
density at the coordinatewise logarithm, divided by the product of the coordinates. It
vanishes outside the positive orthant. The exponential and logarithmic Jacobians identify
this density with the pushforward law, giving normalization, `HasPDF`, and the
Radon–Nikodym derivative against Euclidean volume.

The density formula is totalized at every covariance parameter, but the density-measure
identity requires positive definiteness. In particular, a zero log-covariance gives a Dirac
law rather than a Lebesgue density in positive dimension.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multivariate log-normal density: Gaussian density at `log x` divided by `∏ i, x i`
on the positive orthant, and zero elsewhere. It represents the law when the log-covariance
is positive definite. -/
def multivariateLogNormalPDFReal (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ :=
  if ∀ i, 0 < x i then
    multivariateGaussianPDFReal m S (WithLp.toLp 2 (fun i ↦ Real.log (x i))) / ∏ i, x i
  else 0

/-- The nonnegative extended-real multivariate log-normal density. -/
def multivariateLogNormalPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal (multivariateLogNormalPDFReal m S x)

/-- The defining branch formula of the real-valued density. -/
theorem multivariateLogNormalPDFReal_def (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    multivariateLogNormalPDFReal m S x = if ∀ i, 0 < x i then
      multivariateGaussianPDFReal m S (WithLp.toLp 2 (fun i ↦ Real.log (x i))) / ∏ i, x i
    else 0 := (rfl)

/-- The extended-real density is obtained by applying `ENNReal.ofReal`. -/
theorem multivariateLogNormalPDF_def (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    multivariateLogNormalPDF m S x = ENNReal.ofReal (multivariateLogNormalPDFReal m S x) := (rfl)

/-- The density vanishes outside the positive orthant. -/
@[simp]
theorem multivariateLogNormalPDFReal_of_not_pos (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    {x : EuclideanSpace ℝ ι} (hx : ¬ ∀ i, 0 < x i) : multivariateLogNormalPDFReal m S x = 0 := by
  simp [multivariateLogNormalPDFReal_def, hx]

/-- The extended-real density vanishes outside the positive orthant. -/
@[simp]
theorem multivariateLogNormalPDF_of_not_pos (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    {x : EuclideanSpace ℝ ι} (hx : ¬ ∀ i, 0 < x i) : multivariateLogNormalPDF m S x = 0 := by
  simp [multivariateLogNormalPDF_def, hx]

/-- The explicit density formula on the positive orthant. -/
@[simp]
theorem multivariateLogNormalPDFReal_of_pos (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    {x : EuclideanSpace ℝ ι} (hx : ∀ i, 0 < x i) :
    multivariateLogNormalPDFReal m S x =
      multivariateGaussianPDFReal m S (WithLp.toLp 2 (fun i ↦ Real.log (x i))) / ∏ i, x i := by
  simp [multivariateLogNormalPDFReal_def, hx]

/-- The real-valued density is nonnegative for every covariance parameter. -/
theorem multivariateLogNormalPDFReal_nonneg (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : 0 ≤ multivariateLogNormalPDFReal m S x := by
  by_cases hx : ∀ i, 0 < x i
  · rw [multivariateLogNormalPDFReal_of_pos m S hx]
    exact div_nonneg (multivariateGaussianPDFReal_nonneg m S _)
      (Finset.prod_nonneg fun i _ ↦ (hx i).le)
  · simp [multivariateLogNormalPDFReal_of_not_pos m S hx]

/-- With positive covariance determinant the density is positive exactly on the positive orthant. -/
@[simp]
theorem multivariateLogNormalPDFReal_pos_iff (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hdet : 0 < S.det) (x : EuclideanSpace ℝ ι) :
    0 < multivariateLogNormalPDFReal m S x ↔ ∀ i, 0 < x i := by
  by_cases hx : ∀ i, 0 < x i
  · rw [multivariateLogNormalPDFReal_of_pos m S hx]
    exact iff_of_true (div_pos (multivariateGaussianPDFReal_pos hdet m _)
      (Finset.prod_pos fun i _ ↦ hx i)) hx
  · simp [hx]

/-- With positive covariance determinant the extended-real density is positive exactly on the
positive orthant. -/
@[simp]
theorem multivariateLogNormalPDF_pos_iff (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hdet : 0 < S.det) (x : EuclideanSpace ℝ ι) :
    0 < multivariateLogNormalPDF m S x ↔ ∀ i, 0 < x i := by
  rw [multivariateLogNormalPDF_def, ENNReal.ofReal_pos, multivariateLogNormalPDFReal_pos_iff m hdet]

/-- Converting the extended-real density back to reals recovers its real-valued companion. -/
@[simp]
theorem toReal_multivariateLogNormalPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    (multivariateLogNormalPDF m S x).toReal = multivariateLogNormalPDFReal m S x := by
  rw [multivariateLogNormalPDF_def, ENNReal.toReal_ofReal
    (multivariateLogNormalPDFReal_nonneg m S x)]

/-- The extended-real density is finite everywhere. -/
@[simp]
theorem multivariateLogNormalPDF_ne_top (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : multivariateLogNormalPDF m S x ≠ ⊤ := by
  rw [multivariateLogNormalPDF_def]
  exact ENNReal.ofReal_ne_top

/-- The extended-real density is strictly below infinity at every covariance parameter. -/
theorem multivariateLogNormalPDF_lt_top (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) : multivariateLogNormalPDF m S x < ⊤ :=
  ENNReal.ofReal_lt_top

/-- The real-valued multivariate log-normal density is measurable. -/
@[fun_prop]
theorem measurable_multivariateLogNormalPDFReal (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measurable (multivariateLogNormalPDFReal m S) := by
  unfold multivariateLogNormalPDFReal
  apply Measurable.ite EuclideanSpace.measurableSet_setOf_forall_pos
  · exact ((measurable_multivariateGaussianPDFReal m S).comp (by fun_prop)).div (by fun_prop)
  · exact measurable_const

/-- The extended-real multivariate log-normal density is measurable. -/
@[fun_prop]
theorem measurable_multivariateLogNormalPDF (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measurable (multivariateLogNormalPDF m S) :=
  (measurable_multivariateLogNormalPDFReal m S).ennreal_ofReal

/-- The logarithmic Jacobian gives the density on the positive orthant. -/
theorem multivariateLogNormalPDFReal_eq_abs_det_fderiv_log (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) {x : EuclideanSpace ℝ ι} (hx : ∀ i, 0 < x i) :
    multivariateLogNormalPDFReal m S x =
      |(fderiv ℝ (fun y : EuclideanSpace ℝ ι ↦
          WithLp.toLp 2 (fun i ↦ Real.log (y i))) x).det| *
        multivariateGaussianPDFReal m S (WithLp.toLp 2 (fun i ↦ Real.log (x i))) := by
  rw [multivariateLogNormalPDFReal_of_pos m S hx, PiLp.det_fderiv_log x (fun i ↦ (hx i).ne'),
    abs_of_pos (inv_pos.mpr (Finset.prod_pos fun i _ ↦ hx i)), div_eq_mul_inv, mul_comm]

private lemma exp_jacobian_mul_pdf (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    ENNReal.ofReal (∏ i, Real.exp (x i)) *
        multivariateLogNormalPDF m S (WithLp.toLp 2 (fun i ↦ Real.exp (x i))) =
      multivariateGaussianPDF m S x := by
  rw [multivariateLogNormalPDF_def, ← ENNReal.ofReal_mul (by positivity),
    multivariateLogNormalPDFReal_of_pos m S (fun i ↦ Real.exp_pos (x i))]
  simp only [Real.log_exp, WithLp.toLp_ofLp, multivariateGaussianPDF_def]
  congr 1
  exact mul_div_cancel₀ _ (Finset.prod_ne_zero_iff.mpr fun i _ ↦ Real.exp_ne_zero (x i))

/-- A multivariate log-normal law with positive-definite log-covariance has the stated density
against Euclidean volume. -/
theorem multivariateLogNormalMeasure_eq_withDensity (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    multivariateLogNormalMeasure m S = volume.withDensity (multivariateLogNormalPDF m S) := by
  -- The proof uses Mathlib's `map_withDensity_abs_det_fderiv_eq_addHaar` and the weight-transport
  -- lemma `MeasureTheory.Measure.map_withDensity_eq_withDensity`.
  let e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun x ↦ WithLp.toLp 2 (fun i ↦ Real.exp (x i))
  have he : Measurable e := by fun_prop
  have hjac := map_withDensity_abs_det_fderiv_eq_addHaar volume (f := e)
    MeasurableSet.univ.nullMeasurableSet
    (fun x _ ↦ (PiLp.hasFDerivAt_exp x).hasFDerivWithinAt) (PiLp.exp_injective 2).injOn
  simp only [Measure.restrict_univ, Matrix.det_toEuclideanCLM_diagonal,
    abs_of_pos (Finset.prod_pos fun i _ ↦ Real.exp_pos _)] at hjac
  rw [Set.image_univ, PiLp.range_exp] at hjac
  have hmap := Measure.map_withDensity_eq_withDensity he (by fun_prop)
    (measurable_multivariateLogNormalPDF m S) hjac
    (ae_of_all _ (exp_jacobian_mul_pdf m S))
  rw [multivariateLogNormalMeasure_def, multivariateGaussian_eq_withDensity hS m, hmap,
    ← withDensity_indicator EuclideanSpace.measurableSet_setOf_forall_pos]
  apply withDensity_congr_ae
  exact ae_of_all _ fun x ↦ by
    by_cases hx : ∀ i, 0 < x i
    · simp [hx]
    · simp [hx]

/-- The extended-real density integrates to one at positive-definite log-covariance. -/
@[simp]
theorem lintegral_multivariateLogNormalPDF (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosDef) : ∫⁻ x, multivariateLogNormalPDF m S x = 1 := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ ι) ↦ μ Set.univ)
    (multivariateLogNormalMeasure_eq_withDensity m hS)
  simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    using h.symm

/-- At positive-definite log-covariance the real density is integrable. -/
theorem integrable_multivariateLogNormalPDFReal (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosDef) : Integrable (multivariateLogNormalPDFReal m S) := by
  refine ⟨(measurable_multivariateLogNormalPDFReal m S).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (multivariateLogNormalPDFReal_nonneg m S))).2 ?_⟩
  simp_rw [← multivariateLogNormalPDF_def]
  rw [lintegral_multivariateLogNormalPDF m hS]
  exact ENNReal.one_lt_top

/-- At positive-definite log-covariance the real density integrates to one. -/
@[simp]
theorem integral_multivariateLogNormalPDFReal (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosDef) : ∫ x, multivariateLogNormalPDFReal m S x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (multivariateLogNormalPDFReal_nonneg m S))
    (measurable_multivariateLogNormalPDFReal m S).aestronglyMeasurable]
  simp_rw [← multivariateLogNormalPDF_def]
  rw [lintegral_multivariateLogNormalPDF m hS, ENNReal.toReal_one]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}
  {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}

/-- A random vector with a nondegenerate multivariate log-normal law has a density. -/
theorem hasPDF_of_hasLaw_multivariateLogNormalMeasure (hS : S.PosDef)
    (hX : HasLaw X (multivariateLogNormalMeasure m S) P) : HasPDF X P :=
  hasPDF_of_hasLaw_withDensity (measurable_multivariateLogNormalPDF m S).aemeasurable
    (by rwa [← multivariateLogNormalMeasure_eq_withDensity m hS])

/-- The canonical density of such a random vector equals the named log-normal density. -/
theorem pdf_eq_multivariateLogNormalPDF_of_hasLaw_multivariateLogNormalMeasure (hS : S.PosDef)
    (hX : HasLaw X (multivariateLogNormalMeasure m S) P) :
    pdf X P =ᵐ[volume] multivariateLogNormalPDF m S :=
  pdf_eq_of_hasLaw_withDensity (measurable_multivariateLogNormalPDF m S).aemeasurable
    (by rwa [← multivariateLogNormalMeasure_eq_withDensity m hS])

/-- The Radon–Nikodym derivative against Euclidean volume is the log-normal density. -/
theorem rnDeriv_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    (hS : S.PosDef) :
    (multivariateLogNormalMeasure m S).rnDeriv volume =ᵐ[volume] multivariateLogNormalPDF m S := by
  rw [multivariateLogNormalMeasure_eq_withDensity m hS]
  exact Measure.rnDeriv_withDensity _ (measurable_multivariateLogNormalPDF m S)

end TauCeti.Probability
