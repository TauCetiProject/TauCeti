/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MultivariateLogNormal.PDF

/-!
# Support and singularity of multivariate log-normal laws

For every log-covariance `S`, a multivariate log-normal vector is almost surely in the
coordinatewise exponential of `m + range S`. For positive semidefinite `S`, its topological
support is the ambient closure of that image: exponentiation can introduce boundary points with
zero coordinates.
Invalid log-covariance instead gives singleton support at the exponential of `m`.

The law is absolutely continuous with respect to Euclidean volume exactly when `S` is positive
definite. Otherwise it is singular, including the invalid-covariance Dirac fallback. These
statements also cover empty coordinate types; in that case every covariance is positive definite.

The support calculation uses `support_multivariateGaussian` and continuity of exponentiation.
Singularity uses `mutuallySingular_multivariateGaussian_volume` and Mathlib's theorem that
differentiable maps preserve Lebesgue-null sets.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A multivariate log-normal vector lies almost surely in the exponential image of the
Gaussian affine range, before taking its ambient closure, including invalid covariance. -/
theorem ae_mem_exp_affineRange_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) :
    ∀ᵐ x ∂multivariateLogNormalMeasure m S,
      x ∈ (fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i))) ''
        (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
          Set (EuclideanSpace ℝ ι)) := by
  have he : Continuous (fun y : EuclideanSpace ℝ ι ↦
      WithLp.toLp 2 (fun i ↦ Real.exp (y i))) := by fun_prop
  have hclosed :=
    (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin)).closed_of_finiteDimensional
  have hmeas := (he.measurableEmbedding (PiLp.exp_injective 2)).measurableSet_image'
    hclosed.measurableSet
  by_cases hS : S.PosSemidef
  · rw [multivariateLogNormalMeasure_def]
    exact (ae_map_iff he.measurable.aemeasurable hmeas).mpr <|
      (ae_mem_affineRange_multivariateGaussian hS m).mono fun y hy ↦ ⟨y, hy, rfl⟩
  · rw [multivariateLogNormalMeasure_of_not_posSemidef m hS]
    exact (ae_dirac_iff hmeas).2 ⟨m, AffineSubspace.self_mem_mk' _ _, rfl⟩

/-- The topological support is the closure of the exponential image of `m + range S`.
The closure is in the ambient Euclidean space, so it can contain zero coordinates. -/
@[simp]
theorem support_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (multivariateLogNormalMeasure m S).support =
      closure ((fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i))) ''
        (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
          Set (EuclideanSpace ℝ ι))) := by
  apply Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_closure
    exact Filter.eventually_mem_set.mpr <|
      (ae_mem_exp_affineRange_multivariateLogNormalMeasure m S).mono
        fun _ hx ↦ subset_closure hx
  · refine closure_minimal ?_ Measure.isClosed_support
    rintro _ ⟨y, hy, rfl⟩
    rw [← support_multivariateGaussian hS m, Measure.support_eq_forall_isOpen] at hy
    rw [multivariateLogNormalMeasure_def, Measure.support_eq_forall_isOpen]
    intro U hyU hU
    have he : Continuous (fun y : EuclideanSpace ℝ ι ↦
        WithLp.toLp 2 (fun i ↦ Real.exp (y i))) := by fun_prop
    rw [Measure.map_apply he.measurable hU.measurableSet]
    exact hy _ hyU (hU.preimage he)

/-- Invalid log-covariance gives singleton support at the coordinatewise exponential of `m`. -/
theorem support_multivariateLogNormalMeasure_of_not_posSemidef (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : ¬ S.PosSemidef) :
    (multivariateLogNormalMeasure m S).support =
      {WithLp.toLp 2 (fun i ↦ Real.exp (m i))} := by
  rw [multivariateLogNormalMeasure_of_not_posSemidef m hS, Measure.support_dirac,
    closure_singleton]

/-- Every non-positive-definite log-covariance gives a law singular with respect to Euclidean
volume. This includes both singular positive semidefinite matrices and the invalid fallback. -/
theorem mutuallySingular_multivariateLogNormalMeasure_volume (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : ¬ S.PosDef) :
    multivariateLogNormalMeasure m S ⟂ₘ (volume : Measure (EuclideanSpace ℝ ι)) := by
  have hsing := mutuallySingular_multivariateGaussian_volume hS m
  let e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun y ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i))
  have he : Continuous e := by fun_prop
  have hemb := he.measurableEmbedding (PiLp.exp_injective 2)
  have hnull : volume (e '' hsing.nullSetᶜ) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun y _ ↦ (PiLp.hasFDerivAt_exp y).differentiableAt.differentiableWithinAt)
      hsing.measure_compl_nullSet
  refine ⟨(e '' hsing.nullSetᶜ)ᶜ,
    (hemb.measurableSet_image' hsing.measurableSet_nullSet.compl).compl, ?_, ?_⟩
  · rw [multivariateLogNormalMeasure_def,
      Measure.map_apply he.measurable
        (hemb.measurableSet_image' hsing.measurableSet_nullSet.compl).compl,
      preimage_compl, hemb.injective.preimage_image, compl_compl]
    exact hsing.measure_nullSet
  · simpa only [compl_compl] using hnull

/-- At every degenerate or invalid log-covariance, the Radon–Nikodym derivative against
Euclidean volume vanishes almost everywhere. -/
theorem rnDeriv_multivariateLogNormalMeasure_of_not_posDef (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : ¬ S.PosDef) :
    (multivariateLogNormalMeasure m S).rnDeriv volume =ᵐ[volume] 0 :=
  (mutuallySingular_multivariateLogNormalMeasure_volume m hS).rnDeriv_ae_eq_zero

/-- A multivariate log-normal law has a Lebesgue density exactly when its log-covariance is
positive definite, including the zero-dimensional case. -/
@[simp]
theorem absolutelyContinuous_multivariateLogNormalMeasure_iff (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) :
    multivariateLogNormalMeasure m S ≪ volume ↔ S.PosDef := by
  constructor
  · intro hac
    by_contra hS
    have hz := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hac
      (mutuallySingular_multivariateLogNormalMeasure_volume m hS)
    have := measure_univ (μ := multivariateLogNormalMeasure m S)
    simp [hz] at this
  · intro hS
    rw [multivariateLogNormalMeasure_eq_withDensity m hS]
    exact withDensity_absolutelyContinuous _ _

end TauCeti.Probability
