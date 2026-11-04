/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LogisticNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Density
public import TauCeti.Probability.Distributions.Dirichlet.Density
public import TauCeti.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Support and singularity of simplex logistic-normal laws

A logistic-normal vector lies almost surely in the logistic chart image of the affine range
of its log-ratio covariance, including invalid-covariance Dirac fallbacks. For positive
semidefinite covariance, its topological support is the ambient closure of that image:
sequences in the affine space can approach the boundary of the simplex after normalized
exponentiation.

A covariance that is not positive definite gives a law singular relative to the reference
measure obtained by pushing deleted-coordinate Lebesgue measure through `dirichletChart`.
This includes invalid-covariance Dirac fallbacks. The reference measure is on the simplex's
affine hyperplane, rather than the full ambient Euclidean space.

The support and null-set transport follow the pattern of
`TauCeti.Probability.support_multivariateLogNormalMeasure`: Gaussian support and singularity
are transported through an injective smooth coordinate map.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A logistic-normal vector lies almost surely in the chart image of the affine range of
its log-ratio covariance, including invalid-covariance Dirac fallbacks. -/
theorem ae_mem_chart_affineRange_logisticNormalMeasure (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ} :
    ∀ᵐ x ∂logisticNormalMeasure r m S,
      x ∈ logisticNormalChart r ''
        (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
          Set (EuclideanSpace ℝ {i // i ≠ r})) := by
  by_cases hS : S.PosSemidef
  · have he := (continuous_logisticNormalChart r).measurableEmbedding
      (logisticNormalChart_injective r)
    rw [logisticNormalMeasure_def]
    exact (ae_map_iff he.measurable.aemeasurable
      (he.measurableSet_image' (AffineSubspace.closed_of_finiteDimensional _).measurableSet)).2 <|
        (ae_mem_affineRange_multivariateGaussian hS m).mono fun _ hx ↦ mem_image_of_mem _ hx
  · rw [logisticNormalMeasure_of_not_posSemidef r m hS, ae_dirac_eq,
      Filter.eventually_pure]
    exact mem_image_of_mem _ (AffineSubspace.self_mem_mk' _ _)

/-- The topological support is the ambient closure of the logistic image of the Gaussian
affine support, including singular and zero covariances. -/
@[simp]
theorem support_logisticNormalMeasure (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) :
    (logisticNormalMeasure r m S).support =
      closure (logisticNormalChart r ''
        (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
          Set (EuclideanSpace ℝ {i // i ≠ r}))) := by
  rw [logisticNormalMeasure_def,
    Measure.support_map_eq_closure_image _ Measure.support_mem_ae
      (continuous_logisticNormalChart r), support_multivariateGaussian hS]

/-- An invalid log-ratio covariance gives singleton support at the chart of the mean. -/
@[simp]
theorem support_logisticNormalMeasure_of_not_posSemidef (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : ¬ S.PosSemidef) :
    (logisticNormalMeasure r m S).support = {logisticNormalChart r m} := by
  rw [logisticNormalMeasure_of_not_posSemidef r m hS, Measure.support_dirac,
    closure_singleton]

/-- At covariances that are not positive definite, the deleted-coordinate law is singular
relative to Lebesgue measure. This also covers invalid covariances. -/
theorem mutuallySingular_map_coords_logisticNormalMeasure_volume (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : ¬ S.PosDef) :
    (logisticNormalMeasure r m S).map (fun x ↦ fun j : {i // i ≠ r} ↦ x j) ⟂ₘ
      (volume : Measure ({i // i ≠ r} → ℝ)) := by
  let f : EuclideanSpace ℝ {i // i ≠ r} → EuclideanSpace ℝ {i // i ≠ r} :=
    fun z ↦ WithLp.toLp 2 (fun j ↦ logisticNormalChart r z j)
  have hf : Continuous f := by fun_prop
  have hinj : Function.Injective f := by
    intro z w h
    apply logisticNormalChart_injective r
    rw [← (dirichletChart_eq_self_iff r _).2 (sum_logisticNormalChart r z),
      ← (dirichletChart_eq_self_iff r _).2 (sum_logisticNormalChart r w)]
    exact congrArg (dirichletChart r) (congrArg (WithLp.ofLp) h)
  have he := hf.measurableEmbedding hinj
  -- Smoothness makes the image of a Gaussian volume-null carrier volume-null.
  have hdiff : Differentiable ℝ f := by
    apply (differentiable_piLp 2).2
    intro j
    simp only [f, logisticNormalChart_apply_coe]
    have hcoord (k : {i // i ≠ r}) :
        Differentiable ℝ (fun z : EuclideanSpace ℝ {i // i ≠ r} ↦ Real.exp (z k)) :=
      (PiLp.proj 2 (fun _ : {i // i ≠ r} ↦ ℝ) k).differentiable.exp
    have hden : Differentiable ℝ (fun z : EuclideanSpace ℝ {i // i ≠ r} ↦
        1 + ∑ k, Real.exp (z k)) := by
      apply (differentiable_const (1 : ℝ)).fun_add
      exact Differentiable.fun_sum fun k _ ↦ hcoord k
    simp only [div_eq_mul_inv]
    exact (hcoord j).fun_mul (hden.fun_inv (fun z ↦ by positivity))
  have hsing := mutuallySingular_multivariateGaussian_volume hS m
  have hN := hsing.measurableSet_nullSet.compl
  have hs : (multivariateGaussian m S).map f ⟂ₘ
      (volume : Measure (EuclideanSpace ℝ {i // i ≠ r})) := by
    refine ⟨(f '' hsing.nullSetᶜ)ᶜ, (he.measurableSet_image' hN).compl, ?_, ?_⟩
    · rw [Measure.map_apply he.measurable (he.measurableSet_image' hN).compl,
        preimage_compl, he.injective.preimage_image, compl_compl]
      exact hsing.measure_nullSet
    · rw [compl_compl]
      exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        hdiff.differentiableOn hsing.measure_compl_nullSet
  have hmap := (MeasurableEquiv.toLp 2 ({i // i ≠ r} → ℝ)).symm.measurableEmbedding
    |>.mutuallySingular_map hs
  simp only [MeasurableEquiv.coe_toLp_symm] at hmap
  rw [(PiLp.volume_preserving_ofLp {i // i ≠ r}).map_eq] at hmap
  rw [Measure.map_map (PiLp.volume_preserving_ofLp {i // i ≠ r}).measurable
    hf.measurable] at hmap
  rw [logisticNormalMeasure_def,
    Measure.map_map (by fun_prop) (measurable_logisticNormalChart r)]
  simpa only [Function.comp_def, f, WithLp.ofLp_toLp] using hmap

/-- A logistic-normal law with covariance that is not positive definite is singular relative
to the deleted-coordinate reference measure on the simplex's affine hyperplane. -/
theorem mutuallySingular_logisticNormalMeasure_chart_volume (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : ¬ S.PosDef) :
    logisticNormalMeasure r m S ⟂ₘ
      (volume : Measure ({i // i ≠ r} → ℝ)).map (dirichletChart r) := by
  have he := (continuous_dirichletChart (i₀ := r)).measurableEmbedding
    (dirichletChart_injective r)
  have hsing := he.mutuallySingular_map
    (mutuallySingular_map_coords_logisticNormalMeasure_volume r m hS)
  have hreconstruct : ((logisticNormalMeasure r m S).map
      (fun x ↦ fun j : {i // i ≠ r} ↦ x j)).map (dirichletChart r) =
      logisticNormalMeasure r m S := by
    rw [Measure.map_map he.measurable (by fun_prop)]
    calc
      _ = (logisticNormalMeasure r m S).map id := Measure.map_congr <|
        (ae_mem_simplex_logisticNormalMeasure r m S).mono fun x hx ↦
          (dirichletChart_eq_self_iff r x).2 hx.2
      _ = _ := Measure.map_id
  rwa [hreconstruct] at hsing

/-- For singular or invalid log-ratio covariance, the Radon–Nikodym derivative relative to
deleted-coordinate reference volume vanishes almost everywhere. -/
theorem rnDeriv_logisticNormalMeasure_of_not_posDef (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : ¬ S.PosDef) :
    (logisticNormalMeasure r m S).rnDeriv
        ((volume : Measure ({i // i ≠ r} → ℝ)).map (dirichletChart r)) =ᵐ[
          (volume : Measure ({i // i ≠ r} → ℝ)).map (dirichletChart r)] 0 :=
  (mutuallySingular_logisticNormalMeasure_chart_volume r m hS).rnDeriv_ae_eq_zero

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- A vector with logistic-normal law lies almost surely in the logistic image of the
affine range of its log-ratio covariance, including invalid-covariance Dirac fallbacks. -/
theorem ae_mem_chart_affineRange_logisticNormalMeasure
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω] {P : Measure Ω}
    {r : ι} {X : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ {i // i ≠ r}}
    {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hX : HasLaw X (logisticNormalMeasure r m S) P) :
    ∀ᵐ ω ∂P, X ω ∈ logisticNormalChart r ''
      (AffineSubspace.mk' m (LinearMap.range S.toEuclideanLin) :
        Set (EuclideanSpace ℝ {i // i ≠ r})) := by
  have he := (continuous_logisticNormalChart r).measurableEmbedding
    (logisticNormalChart_injective r)
  exact (hX.ae_iff (measurableSet_setOfPred.mp
    (he.measurableSet_image' (AffineSubspace.closed_of_finiteDimensional _).measurableSet))).2
      (TauCeti.Probability.ae_mem_chart_affineRange_logisticNormalMeasure r m)

end ProbabilityTheory.HasLaw
