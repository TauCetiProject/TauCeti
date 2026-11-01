/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.PiLp
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.MultivariateLogNormal.Basic
import TauCeti.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Support and singularity of multivariate log-normal laws

For positive semidefinite log-covariance `S`, the multivariate log-normal law is concentrated
on the coordinatewise exponential of the affine space `m + range S`. Its topological support
is the ambient closure of this image. The closure matters: exponentiation can approach the
boundary of the positive orthant along unbounded sequences in the Gaussian affine space.

When `S` is not positive definite, the law is singular relative to ambient Euclidean volume.
This includes the Dirac fallback at invalid covariances. The proof transports a Gaussian
null carrier through the differentiable exponential map, which preserves volume-null sets.
No nonemptiness assumption on the finite coordinate type is needed.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A multivariate log-normal vector is almost surely the exponential of a point in the
affine range of its positive semidefinite log-covariance. -/
theorem ae_mem_exp_affineRange_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    ∀ᵐ x ∂multivariateLogNormalMeasure m S,
      x ∈ (fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i))) ''
        (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
          Set (EuclideanSpace ℝ ι)) := by
  have hf : Continuous (fun y : EuclideanSpace ℝ ι ↦
      WithLp.toLp 2 (fun i ↦ Real.exp (y i))) := by fun_prop
  have he := hf.measurableEmbedding (PiLp.exp_injective 2)
  rw [multivariateLogNormalMeasure_def]
  exact (ae_map_iff he.measurable.aemeasurable
    (he.measurableSet_image' (AffineSubspace.closed_of_finiteDimensional _).measurableSet)).2 <|
      (ae_mem_affineRange_multivariateGaussian hS m).mono fun _ hx ↦ mem_image_of_mem _ hx

/-- The topological support of a multivariate log-normal law is the closure of the
exponential image of its Gaussian affine support, including singular and zero covariances. -/
@[simp]
theorem support_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (multivariateLogNormalMeasure m S).support =
      closure ((fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i))) ''
        (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
          Set (EuclideanSpace ℝ ι))) := by
  rw [multivariateLogNormalMeasure_def,
    Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_multivariateGaussian hS]

/-- An invalid log-covariance gives singleton support at the exponential of the log-mean. -/
@[simp]
theorem support_multivariateLogNormalMeasure_of_not_posSemidef (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : ¬ S.PosSemidef) :
    (multivariateLogNormalMeasure m S).support =
      {WithLp.toLp 2 (fun i ↦ Real.exp (m i))} := by
  rw [multivariateLogNormalMeasure_of_not_posSemidef m hS,
    Measure.support_dirac, closure_singleton]

/-- A multivariate log-normal law whose log-covariance is not positive definite is singular
relative to ambient volume. The statement includes invalid covariance parameters. -/
theorem mutuallySingular_multivariateLogNormalMeasure_volume (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : ¬ S.PosDef) :
    multivariateLogNormalMeasure m S ⟂ₘ (volume : Measure (EuclideanSpace ℝ ι)) := by
  let f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι :=
    fun y ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i))
  have hf : Continuous f := by fun_prop
  have he := hf.measurableEmbedding (PiLp.exp_injective 2)
  have hsing := mutuallySingular_multivariateGaussian_volume hS m
  have hN := hsing.measurableSet_nullSet.compl
  refine ⟨(f '' hsing.nullSetᶜ)ᶜ, (he.measurableSet_image' hN).compl, ?_, ?_⟩
  · rw [multivariateLogNormalMeasure_def,
      Measure.map_apply he.measurable (he.measurableSet_image' hN).compl,
      preimage_compl, he.injective.preimage_image, compl_compl]
    exact hsing.measure_nullSet
  · rw [compl_compl]
    exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun x _ ↦ (PiLp.hasFDerivAt_exp x).differentiableAt.differentiableWithinAt)
      hsing.measure_compl_nullSet

/-- At log-covariances that are not positive definite, the ambient Radon–Nikodym derivative
vanishes almost everywhere, despite the law having total mass one. -/
theorem rnDeriv_multivariateLogNormalMeasure_of_not_posDef (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : ¬ S.PosDef) :
    (multivariateLogNormalMeasure m S).rnDeriv volume =ᵐ[volume] 0 :=
  (mutuallySingular_multivariateLogNormalMeasure_volume m hS).rnDeriv_ae_eq_zero

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

/-- A log-normal random vector with positive semidefinite log-covariance lies almost surely
in the exponential image of the corresponding Gaussian affine space. -/
theorem HasLaw.ae_mem_exp_affineRange_multivariateLogNormalMeasure
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hX : HasLaw X (multivariateLogNormalMeasure m S) P) (hS : S.PosSemidef) :
    ∀ᵐ ω ∂P, X ω ∈
      (fun y : EuclideanSpace ℝ ι ↦ WithLp.toLp 2 (fun i ↦ Real.exp (y i))) ''
        (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
          Set (EuclideanSpace ℝ ι)) := by
  have hf : Continuous (fun y : EuclideanSpace ℝ ι ↦
      WithLp.toLp 2 (fun i ↦ Real.exp (y i))) := by fun_prop
  have he := hf.measurableEmbedding (PiLp.exp_injective 2)
  exact (hX.ae_iff (measurableSet_setOfPred.mp
    (he.measurableSet_image' (AffineSubspace.closed_of_finiteDimensional _).measurableSet))).2
      (TauCeti.Probability.ae_mem_exp_affineRange_multivariateLogNormalMeasure m hS)

end ProbabilityTheory
