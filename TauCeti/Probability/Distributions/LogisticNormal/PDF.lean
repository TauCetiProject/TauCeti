/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Density
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.LogisticNormal.Basic

import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec

/-!
# The density of the simplex logistic-normal law in a simplex chart

A logistic-normal law lives on the open standard simplex, which lies in the affine hyperplane
`∑ i, x i = 1`, so it has no density against the ambient volume. As for the Dirichlet law, its
reference measure is Lebesgue measure on the coordinates away from the reference category `r`,
pushed to the hyperplane by `dirichletChart r`, which reconstructs the coordinate at `r` as the
remaining mass.

In these coordinates the logistic chart is the softmax map
`z ↦ (e^{z_j} / (1 + ∑ₖ e^{z_k}))_j`.
Writing `p` for its value, its derivative is the matrix `diagonal p - vecMulVec p p`, whose
determinant is the product of all simplex coordinates of the chart value, including the
reference coordinate `1 - ∑ⱼ p_j`. For positive-definite log-ratio covariance `S`, the change of
variables therefore gives the chart density `φ_{m,S}(log(x_j / x_r))_j / ∏ i, x i` on the open
simplex, where `φ_{m,S}` is the multivariate Gaussian density, and zero elsewhere.

## Main declarations

* `TauCeti.Probability.det_fderiv_logisticNormalChart_coords`: the Jacobian of the logistic chart
  in simplex coordinates is the product of the simplex coordinates.
* `TauCeti.Probability.logisticNormalChartPDFReal`, `TauCeti.Probability.logisticNormalChartPDF`:
  the real and extended-real chart densities.
* `TauCeti.Probability.map_coords_logisticNormalMeasure_eq_withDensity`: the non-reference
  coordinates of a logistic-normal vector have the chart density against Lebesgue measure.
* `TauCeti.Probability.logisticNormalMeasure_eq_map_withDensity_logisticNormalChartPDF`: the law
  is the image under `dirichletChart r` of Lebesgue measure weighted by the chart density.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
* The change-of-variables proof follows `multivariateLogNormalMeasure_eq_withDensity` in
  `TauCeti/Probability/Distributions/MultivariateLogNormal/PDF.lean`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The logistic chart in simplex coordinates -/

/-- The logistic chart is recovered from its coordinates away from the reference category by the
deleted-coordinate chart of the simplex. -/
@[simp]
theorem dirichletChart_logisticNormalChart (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r}) :
    dirichletChart r (fun j : {i // i ≠ r} ↦
      Real.exp (z.ofLp j) / (1 + ∑ k, Real.exp (z.ofLp k))) =
      logisticNormalChart r z := by
  simpa only [logisticNormalChart_apply_coe] using
    (dirichletChart_eq_self_iff r _).2 (sum_logisticNormalChart r z)

/-- The coordinates of the logistic chart away from the reference category lie in the chart
region of the simplex. -/
theorem logisticNormalChart_coords_mem_dirichletChartRegion (r : ι)
    (z : EuclideanSpace ℝ {i // i ≠ r}) :
    (fun j : {i // i ≠ r} ↦ logisticNormalChart r z j) ∈ dirichletChartRegion r := by
  refine mem_dirichletChartRegion_iff.2 ⟨fun j ↦ logisticNormalChart_pos r z j, ?_⟩
  have h := sum_logisticNormalChart r z
  rw [Fintype.sum_eq_add_sum_subtype_ne _ r] at h
  linarith [logisticNormalChart_pos r z r]

/-- The coordinates of the logistic chart away from the reference category range over the whole
chart region of the simplex. -/
theorem range_logisticNormalChart_coords (r : ι) :
    range (fun y : {i // i ≠ r} → ℝ ↦
        fun j : {i // i ≠ r} ↦ logisticNormalChart r (WithLp.toLp 2 y) j) =
      dirichletChartRegion r := by
  refine Subset.antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨y, rfl⟩
    exact logisticNormalChart_coords_mem_dirichletChartRegion r _
  · refine ⟨WithLp.ofLp (logisticNormalLogRatio r (dirichletChart r x)), ?_⟩
    ext j
    beta_reduce
    rw [WithLp.toLp_ofLp, logisticNormalChart_logRatio r (dirichletChart_pos hx)
      (sum_dirichletChart r x), dirichletChart_apply_coe]

private theorem injective_logisticNormalChart_coords (r : ι) :
    Function.Injective (fun y : {i // i ≠ r} → ℝ ↦
      fun j : {i // i ≠ r} ↦ logisticNormalChart r (WithLp.toLp 2 y) j) := by
  intro y y' h
  have h' := congrArg (dirichletChart r) h
  simp only [logisticNormalChart_apply_coe, dirichletChart_logisticNormalChart] at h'
  exact WithLp.toLp_injective 2 (logisticNormalChart_injective r h')

/-- In coordinates away from the reference category, the derivative of the logistic chart at a
point with chart value `p` is the matrix `diagonal p - vecMulVec p p`. -/
theorem hasFDerivAt_logisticNormalChart_coords (r : ι) (y : {i // i ≠ r} → ℝ) :
    HasFDerivAt (fun y : {i // i ≠ r} → ℝ ↦
        fun j : {i // i ≠ r} ↦ logisticNormalChart r (WithLp.toLp 2 y) j)
      (LinearMap.toContinuousLinearMap (Matrix.toLin'
        (Matrix.diagonal (fun j : {i // i ≠ r} ↦ logisticNormalChart r (WithLp.toLp 2 y) j) -
          Matrix.vecMulVec (fun j : {i // i ≠ r} ↦ logisticNormalChart r (WithLp.toLp 2 y) j)
            (fun j : {i // i ≠ r} ↦ logisticNormalChart r (WithLp.toLp 2 y) j)))) y := by
  simp only [logisticNormalChart_apply_coe]
  refine hasFDerivAt_pi'' fun j ↦ ?_
  have hD : 1 + ∑ k, Real.exp (y k) ≠ 0 := by positivity
  have hnum : HasFDerivAt (fun y : {i // i ≠ r} → ℝ ↦ Real.exp (y j))
      (Real.exp (y j) • ContinuousLinearMap.proj j) y :=
    (hasFDerivAt_apply j y).exp
  have hden : HasFDerivAt (fun y : {i // i ≠ r} → ℝ ↦ 1 + ∑ k, Real.exp (y k))
      (∑ k, Real.exp (y k) • ContinuousLinearMap.proj k) y :=
    (HasFDerivAt.fun_sum fun k _ ↦ (hasFDerivAt_apply k y).exp).const_add 1
  refine (hnum.mul ((hasFDerivAt_inv hD).comp y hden)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.sub_mulVec, Pi.sub_apply,
    Matrix.mulVec_diagonal, add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, FunLike.coe_sum, Finset.sum_apply,
    Function.comp_apply, smul_eq_mul, Matrix.vecMulVec_mulVec, dotProduct, op_smul_eq_mul,
    div_mul_eq_mul_div, ← Finset.sum_div]
  field_simp
  ring

/-- **The Jacobian of the logistic chart.** In coordinates away from the reference category, the
Jacobian determinant of the logistic chart is the product of all coordinates of the chart value,
including the reference coordinate. -/
theorem det_fderiv_logisticNormalChart_coords (r : ι) (y : {i // i ≠ r} → ℝ) :
    (fderiv ℝ (fun y : {i // i ≠ r} → ℝ ↦
        fun j : {i // i ≠ r} ↦ logisticNormalChart r (WithLp.toLp 2 y) j) y).det =
      ∏ i, logisticNormalChart r (WithLp.toLp 2 y) i := by
  set p : {i // i ≠ r} → ℝ := fun j ↦ logisticNormalChart r (WithLp.toLp 2 y) j
  have hfac : Matrix.diagonal p - Matrix.vecMulVec p p =
      Matrix.diagonal p * (1 - Matrix.vecMulVec 1 p) := by
    rw [mul_sub, mul_one]
    congr 1
    ext i k
    simp [Matrix.diagonal_mul, Matrix.vecMulVec_apply]
  have hsum := sum_logisticNormalChart r (WithLp.toLp 2 y)
  rw [Fintype.sum_eq_add_sum_subtype_ne _ r] at hsum
  rw [(hasFDerivAt_logisticNormalChart_coords r y).fderiv, LinearMap.det_toContinuousLinearMap,
    LinearMap.det_toLin', hfac, Matrix.det_mul, Matrix.det_diagonal, TauCeti.det_one_sub_vecMulVec,
    Fintype.prod_eq_mul_prod_subtype_ne _ r, mul_comm]
  congr 1
  simp only [dotProduct, Pi.one_apply, mul_one, p]
  linarith

/-! ### The chart density -/

open Classical in
/-- The real-valued density of the simplex logistic-normal law in the chart that drops the
reference category `r`, with respect to Lebesgue measure on the remaining coordinates. On the
chart region it is the Gaussian density at the additive log ratios divided by the product of all
simplex coordinates; it vanishes elsewhere.

The formula is defined for every covariance, but it represents the law only for
positive-definite `S`. -/
def logisticNormalChartPDFReal (r : ι) (m : EuclideanSpace ℝ {i // i ≠ r})
    (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) (x : {i // i ≠ r} → ℝ) : ℝ :=
  if x ∈ dirichletChartRegion r then
    multivariateGaussianPDFReal m S (logisticNormalLogRatio r (dirichletChart r x)) /
      ∏ i, dirichletChart r x i
  else 0

open Classical in
/-- The defining branch formula of the real-valued chart density. -/
theorem logisticNormalChartPDFReal_def (r : ι) (m : EuclideanSpace ℝ {i // i ≠ r})
    (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) (x : {i // i ≠ r} → ℝ) :
    logisticNormalChartPDFReal r m S x = if x ∈ dirichletChartRegion r then
      multivariateGaussianPDFReal m S (logisticNormalLogRatio r (dirichletChart r x)) /
        ∏ i, dirichletChart r x i
    else 0 := (rfl)

/-- The extended-real chart density of the simplex logistic-normal law. -/
def logisticNormalChartPDF (r : ι) (m : EuclideanSpace ℝ {i // i ≠ r})
    (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) (x : {i // i ≠ r} → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (logisticNormalChartPDFReal r m S x)

/-- The extended-real chart density is obtained by applying `ENNReal.ofReal`. -/
theorem logisticNormalChartPDF_def (r : ι) (m : EuclideanSpace ℝ {i // i ≠ r})
    (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) (x : {i // i ≠ r} → ℝ) :
    logisticNormalChartPDF r m S x = ENNReal.ofReal (logisticNormalChartPDFReal r m S x) := (rfl)

variable {r : ι} (m : EuclideanSpace ℝ {i // i ≠ r})
  (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ)

/-- The explicit chart density on the chart region. -/
@[simp]
theorem logisticNormalChartPDFReal_of_mem {x : {i // i ≠ r} → ℝ}
    (hx : x ∈ dirichletChartRegion r) :
    logisticNormalChartPDFReal r m S x =
      multivariateGaussianPDFReal m S (logisticNormalLogRatio r (dirichletChart r x)) /
        ∏ i, dirichletChart r x i := by
  simp [logisticNormalChartPDFReal, hx]

/-- The chart density vanishes outside the chart region. -/
@[simp]
theorem logisticNormalChartPDFReal_of_notMem {x : {i // i ≠ r} → ℝ}
    (hx : x ∉ dirichletChartRegion r) : logisticNormalChartPDFReal r m S x = 0 := by
  simp [logisticNormalChartPDFReal, hx]

/-- The explicit extended-real chart density on the chart region. -/
@[simp]
theorem logisticNormalChartPDF_of_mem {x : {i // i ≠ r} → ℝ}
    (hx : x ∈ dirichletChartRegion r) :
    logisticNormalChartPDF r m S x = ENNReal.ofReal
      (multivariateGaussianPDFReal m S (logisticNormalLogRatio r (dirichletChart r x)) /
        ∏ i, dirichletChart r x i) := by
  rw [logisticNormalChartPDF_def, logisticNormalChartPDFReal_of_mem m S hx]

/-- The extended-real chart density vanishes outside the chart region. -/
@[simp]
theorem logisticNormalChartPDF_of_notMem {x : {i // i ≠ r} → ℝ}
    (hx : x ∉ dirichletChartRegion r) : logisticNormalChartPDF r m S x = 0 := by
  simp [logisticNormalChartPDF_def, hx]

/-- The real chart density is nonnegative for every covariance parameter. -/
theorem logisticNormalChartPDFReal_nonneg (x : {i // i ≠ r} → ℝ) :
    0 ≤ logisticNormalChartPDFReal r m S x := by
  by_cases hx : x ∈ dirichletChartRegion r
  · rw [logisticNormalChartPDFReal_of_mem m S hx]
    exact div_nonneg (multivariateGaussianPDFReal_nonneg m S _)
      (Finset.prod_nonneg fun i _ ↦ (dirichletChart_pos hx i).le)
  · simp [hx]

/-- With positive covariance determinant the chart density is positive exactly on the chart
region. -/
@[simp]
theorem logisticNormalChartPDFReal_pos_iff {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hdet : 0 < S.det) (x : {i // i ≠ r} → ℝ) :
    0 < logisticNormalChartPDFReal r m S x ↔ x ∈ dirichletChartRegion r := by
  by_cases hx : x ∈ dirichletChartRegion r
  · rw [logisticNormalChartPDFReal_of_mem m S hx]
    exact iff_of_true (div_pos (multivariateGaussianPDFReal_pos hdet m _)
      (Finset.prod_pos fun i _ ↦ dirichletChart_pos hx i)) hx
  · simp [hx]

/-- With positive covariance determinant the extended-real chart density is positive exactly on
the chart region. -/
@[simp]
theorem logisticNormalChartPDF_pos_iff {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hdet : 0 < S.det) (x : {i // i ≠ r} → ℝ) :
    0 < logisticNormalChartPDF r m S x ↔ x ∈ dirichletChartRegion r := by
  rw [logisticNormalChartPDF_def, ENNReal.ofReal_pos, logisticNormalChartPDFReal_pos_iff m hdet]

/-- Converting the extended-real chart density back to reals recovers the real density. -/
@[simp]
theorem toReal_logisticNormalChartPDF (x : {i // i ≠ r} → ℝ) :
    (logisticNormalChartPDF r m S x).toReal = logisticNormalChartPDFReal r m S x := by
  rw [logisticNormalChartPDF_def, ENNReal.toReal_ofReal (logisticNormalChartPDFReal_nonneg m S x)]

/-- The extended-real chart density is finite everywhere. -/
@[simp]
theorem logisticNormalChartPDF_ne_top (x : {i // i ≠ r} → ℝ) :
    logisticNormalChartPDF r m S x ≠ ⊤ :=
  ENNReal.ofReal_ne_top

/-- The real chart density is measurable. -/
@[fun_prop]
theorem measurable_logisticNormalChartPDFReal : Measurable (logisticNormalChartPDFReal r m S) := by
  classical
  unfold logisticNormalChartPDFReal
  refine Measurable.ite (measurableSet_dirichletChartRegion r) ?_ measurable_const
  exact ((measurable_multivariateGaussianPDFReal m S).comp (by fun_prop)).div (by fun_prop)

/-- The extended-real chart density is measurable. -/
@[fun_prop]
theorem measurable_logisticNormalChartPDF : Measurable (logisticNormalChartPDF r m S) :=
  (measurable_logisticNormalChartPDFReal m S).ennreal_ofReal

/-! ### The density theorem -/

private theorem jacobian_mul_logisticNormalChartPDF (y : {i // i ≠ r} → ℝ) :
    ENNReal.ofReal (∏ i, logisticNormalChart r (WithLp.toLp 2 y) i) *
        logisticNormalChartPDF r m S
          (fun j : {i // i ≠ r} ↦ logisticNormalChart r (WithLp.toLp 2 y) j) =
      multivariateGaussianPDF m S (WithLp.toLp 2 y) := by
  have hprod : 0 < ∏ i, logisticNormalChart r (WithLp.toLp 2 y) i :=
    Finset.prod_pos fun i _ ↦ logisticNormalChart_pos r _ i
  rw [logisticNormalChartPDF_def, ← ENNReal.ofReal_mul hprod.le,
    logisticNormalChartPDFReal_of_mem m S
      (logisticNormalChart_coords_mem_dirichletChartRegion r _)]
  simp only [logisticNormalChart_apply_coe]
  rw [dirichletChart_logisticNormalChart, logisticNormalLogRatio_chart,
    mul_div_cancel₀ _ hprod.ne', multivariateGaussianPDF_def]

/-- **The chart density of the logistic-normal law.** For positive-definite log-ratio
covariance, the coordinates away from the reference category of a logistic-normal vector have
density `logisticNormalChartPDF r m S` with respect to Lebesgue measure. -/
theorem map_coords_logisticNormalMeasure_eq_withDensity
    {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ} (hS : S.PosDef) :
    (logisticNormalMeasure r m S).map (fun x (j : {i // i ≠ r}) ↦ x j) =
      volume.withDensity (logisticNormalChartPDF r m S) := by
  set σ : ({i // i ≠ r} → ℝ) → {i // i ≠ r} → ℝ :=
    fun y (j : {i // i ≠ r}) ↦ logisticNormalChart r (WithLp.toLp 2 y) j
  have hσ : Measurable σ := by fun_prop
  have hcoords : Measurable fun (x : EuclideanSpace ℝ ι) (j : {i // i ≠ r}) ↦ x j := by
    fun_prop
  -- Transport the Gaussian from Euclidean space to plain coordinate vectors.
  have hgauss : (multivariateGaussian m S).map WithLp.ofLp =
      volume.withDensity fun y ↦ multivariateGaussianPDF m S (WithLp.toLp 2 y) := by
    have e := MeasurableEquiv.map_withDensity (MeasurableEquiv.toLp 2 ({i // i ≠ r} → ℝ)).symm
      volume (multivariateGaussianPDF m S)
    rwa [(EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).map_eq,
      MeasurableEquiv.coe_toLp_symm, ← multivariateGaussian_eq_withDensity hS m] at e
  -- The change of variables along the logistic chart in coordinates.
  have hjac := map_withDensity_abs_det_fderiv_eq_addHaar volume (f := σ)
    MeasurableSet.univ.nullMeasurableSet
    (fun y _ ↦ (hasFDerivAt_logisticNormalChart_coords r y).differentiableAt.hasFDerivAt
      |>.hasFDerivWithinAt) (injective_logisticNormalChart_coords r).injOn
  simp only [Measure.restrict_univ, det_fderiv_logisticNormalChart_coords,
    abs_of_pos (Finset.prod_pos fun i _ ↦ logisticNormalChart_pos r _ i), image_univ,
    σ, range_logisticNormalChart_coords] at hjac
  have hmap := Measure.map_withDensity_eq_withDensity hσ (by fun_prop)
    (measurable_logisticNormalChartPDF m S) hjac
    (ae_of_all _ (jacobian_mul_logisticNormalChartPDF m S))
  have hcomp : (fun (x : EuclideanSpace ℝ ι) (j : {i // i ≠ r}) ↦ x j) ∘ logisticNormalChart r =
      σ ∘ WithLp.ofLp := by
    ext z j
    simp [σ]
  rw [logisticNormalMeasure_def, Measure.map_map hcoords (measurable_logisticNormalChart r),
    hcomp, ← Measure.map_map hσ (by fun_prop), hgauss, hmap,
    ← withDensity_indicator (measurableSet_dirichletChartRegion r)]
  refine withDensity_congr_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ dirichletChartRegion r <;> simp [hx]

/-- **The logistic-normal law in a simplex chart.** For positive-definite log-ratio covariance,
the simplex logistic-normal law is the image under the deleted-coordinate chart of Lebesgue
measure weighted by `logisticNormalChartPDF r m S`. -/
theorem logisticNormalMeasure_eq_map_withDensity_logisticNormalChartPDF
    {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ} (hS : S.PosDef) :
    logisticNormalMeasure r m S =
      (volume.withDensity (logisticNormalChartPDF r m S)).map (dirichletChart r) := by
  rw [← map_coords_logisticNormalMeasure_eq_withDensity m hS,
    Measure.map_map measurable_dirichletChart (by fun_prop)]
  conv_lhs => rw [← Measure.map_id (μ := logisticNormalMeasure r m S)]
  refine Measure.map_congr ?_
  filter_upwards [ae_mem_simplex_logisticNormalMeasure r m S] with x hx
  exact ((dirichletChart_eq_self_iff r x).2 hx.2).symm

/-- The extended-real chart density integrates to one at positive-definite covariance. -/
@[simp]
theorem lintegral_logisticNormalChartPDF {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosDef) : ∫⁻ x, logisticNormalChartPDF r m S x = 1 := by
  have h := congrArg (fun μ : Measure ({i // i ≠ r} → ℝ) ↦ μ univ)
    (map_coords_logisticNormalMeasure_eq_withDensity m hS)
  simp only [Measure.map_apply (by fun_prop : Measurable fun (x : EuclideanSpace ℝ ι)
    (j : {i // i ≠ r}) ↦ x j) MeasurableSet.univ, preimage_univ, measure_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  exact h.symm

/-- At positive-definite covariance the real chart density is integrable. -/
theorem integrable_logisticNormalChartPDFReal {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosDef) : Integrable (logisticNormalChartPDFReal r m S) := by
  refine ⟨(measurable_logisticNormalChartPDFReal m S).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (logisticNormalChartPDFReal_nonneg m S))).2 ?_⟩
  simp_rw [← logisticNormalChartPDF_def]
  rw [lintegral_logisticNormalChartPDF m hS]
  exact ENNReal.one_lt_top

/-- At positive-definite covariance the real chart density integrates to one. -/
@[simp]
theorem integral_logisticNormalChartPDFReal {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosDef) : ∫ x, logisticNormalChartPDFReal r m S x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (logisticNormalChartPDFReal_nonneg m S))
    (measurable_logisticNormalChartPDFReal m S).aestronglyMeasurable]
  simp_rw [← logisticNormalChartPDF_def]
  rw [lintegral_logisticNormalChartPDF m hS, ENNReal.toReal_one]

/-- The Radon–Nikodym derivative of the coordinate law against Lebesgue measure is the chart
density. -/
theorem rnDeriv_map_coords_logisticNormalMeasure {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosDef) :
    ((logisticNormalMeasure r m S).map fun x (j : {i // i ≠ r}) ↦ x j).rnDeriv volume
      =ᵐ[volume] logisticNormalChartPDF r m S := by
  rw [map_coords_logisticNormalMeasure_eq_withDensity m hS]
  exact Measure.rnDeriv_withDensity _ (measurable_logisticNormalChartPDF m S)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}
  {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}

/-- The coordinates away from the reference category of a random vector with a nondegenerate
logistic-normal law have a density. -/
theorem hasPDF_coords_of_hasLaw_logisticNormalMeasure (hS : S.PosDef)
    (hX : HasLaw X (logisticNormalMeasure r m S) P) :
    HasPDF (fun ω (j : {i // i ≠ r}) ↦ X ω j) P :=
  hasPDF_of_hasLaw_withDensity (measurable_logisticNormalChartPDF m S).aemeasurable
    (by simpa only [Function.comp_def, map_coords_logisticNormalMeasure_eq_withDensity m hS] using
      HasLaw.comp ⟨(by fun_prop : Measurable fun (x : EuclideanSpace ℝ ι)
        (j : {i // i ≠ r}) ↦ x j).aemeasurable, rfl⟩ hX)

/-- The canonical density of those coordinates is the chart density. -/
theorem pdf_coords_eq_logisticNormalChartPDF_of_hasLaw_logisticNormalMeasure (hS : S.PosDef)
    (hX : HasLaw X (logisticNormalMeasure r m S) P) :
    pdf (fun ω (j : {i // i ≠ r}) ↦ X ω j) P =ᵐ[volume] logisticNormalChartPDF r m S :=
  pdf_eq_of_hasLaw_withDensity (measurable_logisticNormalChartPDF m S).aemeasurable
    (by simpa only [Function.comp_def, map_coords_logisticNormalMeasure_eq_withDensity m hS] using
      HasLaw.comp ⟨(by fun_prop : Measurable fun (x : EuclideanSpace ℝ ι)
        (j : {i // i ≠ r}) ↦ x j).aemeasurable, rfl⟩ hX)

end TauCeti.Probability
