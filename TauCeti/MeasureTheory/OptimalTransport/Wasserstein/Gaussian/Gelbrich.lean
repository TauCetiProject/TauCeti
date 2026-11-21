/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Gaussian.Basic
public import TauCeti.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.CovarianceBilin

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gelbrich's lower bound for the quadratic Wasserstein distance

Replacing two probability laws with finite second moments by the Gaussian laws with the same means
and covariances can only decrease their quadratic Wasserstein distance. The proof takes an optimal
coupling `π` of the two laws, replaces it with the Gaussian law on the product space with the same
mean and covariance as `π`, and observes that the marginals of that Gaussian law are the two
Gaussian laws, while the quadratic cost, an integral of the squared norm of a linear function, only
depends on the mean and covariance.

The statement is coordinate free, on any finite-dimensional real inner product space, with the
covariance of a law expressed by Mathlib's `ProbabilityTheory.covarianceBilin`. Combined with the
closed formula for the Wasserstein distance between Gaussian laws
(`TauCeti.wassersteinEDist_two_multivariateGaussian`) it gives the Bures lower bound
`‖m₁ - m₂‖² + tr S₁ + tr S₂ - 2 tr (S₁^(1/2) S₂ S₁^(1/2))^(1/2)` on the squared
distance.

## Main statements

* `TauCeti.Probability.exists_isGaussian_integral_id_eq_covarianceBilin_eq`: every finite measure
  with finite second moment has a Gaussian law with the same mean and covariance.
* `TauCeti.wassersteinEDist_two_le_of_isGaussian`: **Gelbrich's lower bound**: replacing both laws
  by Gaussian laws with the same means and covariances does not increase `W₂`.
* `TauCeti.ofReal_gaussianWassersteinSq_le_wassersteinEDist_two_rpow_two`: the Bures form of the
  bound on `EuclideanSpace ℝ ι`, when the first covariance matrix is positive definite.

## References

* M. Gelbrich, *On a formula for the L² Wasserstein metric between measures on Euclidean and
  Hilbert spaces*, Math. Nachr. 147 (1990), 185–203.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Gaussian laws with prescribed moments.** A finite measure with finite second moment on a
finite-dimensional real inner product space has a Gaussian law with the same mean and the same
covariance. -/
theorem Probability.exists_isGaussian_integral_id_eq_covarianceBilin_eq (μ : Measure E)
    [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    ∃ μ' : Measure E, IsGaussian μ' ∧ ∫ x, x ∂μ' = ∫ x, x ∂μ ∧
      covarianceBilin μ' = covarianceBilin μ := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨m, hm⟩ : ∃ m : E, m = ∫ x, x ∂μ := ⟨_, rfl⟩
  have hν2 : MemLp id 2 (μ.map (fun x => x - m)) := by
    refine (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 ?_
    exact hμ.sub (memLp_const m)
  obtain ⟨k, u, hu⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.1
    (isPositive_covarianceOperator (μ := μ.map (fun x => x - m)))
  let A : EuclideanSpace ℝ (Fin k) →L[ℝ] E :=
    ∑ i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight (u i)
  have hAe : ∀ i, A (EuclideanSpace.basisFun (Fin k) ℝ i) = u i := by
    intro i
    simp [A, EuclideanSpace.basisFun_apply, ite_smul]
  have hmap : (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => m + A x) =
      ((stdGaussian (EuclideanSpace ℝ (Fin k))).map A).map (fun x => m + x) := by
    rw [Measure.map_map (measurable_const_add m) (by fun_prop)]
    rfl
  refine ⟨(stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => m + A x), ?_, ?_, ?_⟩
  · rw [hmap]; infer_instance
  · rw [integral_map (by fun_prop) (by fun_prop),
      integral_add (integrable_const _), integral_const, ← hm]
    · simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]
    · exact IsGaussian.integrable_id.comp_measurable (by fun_prop)
  · rw [hmap, covarianceBilin_map_const_add]
    ext x y
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian]
    have h1 : ⟪covarianceOperator (μ.map (fun x => x - m)) x, y⟫ = covarianceBilin μ x y := by
      rw [covarianceOperator_inner hν2, integral_map (by fun_prop) (by fun_prop),
        covarianceBilin_apply hμ, hm]
      rfl
    have h2 : ⟪ContinuousLinearMap.adjoint A x, ContinuousLinearMap.adjoint A y⟫ =
        ⟪(∑ i, InnerProductSpace.rankOne ℝ (u i) (u i)) x, y⟫ := by
      rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_inner_mul_inner
        (ContinuousLinearMap.adjoint A x) (ContinuousLinearMap.adjoint A y)]
      simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
        hAe, sum_apply, InnerProductSpace.rankOne_apply, sum_inner, inner_smul_left]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [real_inner_comm]
    rw [← h1, hu]
    exact h2

/-- The second moment of a law with finite second moment is determined by its mean and
covariance. -/
private lemma integral_norm_sq_eq (κ : Measure V) [IsProbabilityMeasure κ] (h : MemLp id 2 κ) :
    ∫ x, ‖x‖ ^ 2 ∂κ = ‖∫ x, x ∂κ‖ ^ 2 +
      ∑ k, covarianceBilin κ (stdOrthonormalBasis ℝ V k) (stdOrthonormalBasis ℝ V k) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  set b := stdOrthonormalBasis ℝ V
  have hi : ∀ k, MemLp (fun x => ⟪b k, x⟫) 2 κ := fun k => by
    simpa using (innerSL ℝ (b k)).comp_memLp' h
  have h1 : ∀ x : V, ‖x‖ ^ 2 = ∑ k, ⟪b k, x⟫ ^ 2 := fun x => by
    rw [← b.sum_sq_norm_inner_right x]; simp
  have h2 : ∀ k, ∫ x, ⟪b k, x⟫ ^ 2 ∂κ =
      ⟪b k, ∫ x, x ∂κ⟫ ^ 2 + covarianceBilin κ (b k) (b k) := by
    intro k
    have h3 : ∫ x, ⟪b k, x⟫ ∂κ = ⟪b k, ∫ x, x ∂κ⟫ :=
      integral_inner (h.integrable (by simp)) (b k)
    rw [covarianceBilin_self h, variance_eq_sub (hi k)]
    simp only [Pi.pow_apply, h3]
    ring
  simp_rw [h1]
  rw [integral_finsetSum _ (fun k _ => (hi k).integrable_sq),
    Finset.sum_congr rfl (fun k _ => h2 k), Finset.sum_add_distrib]

/-- Pushing forward by a continuous linear map preserves equality of mean and covariance. -/
private lemma integral_id_map_eq_and_covarianceBilin_map_eq {ρ ρ' : Measure E}
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure ρ'] (hρ : MemLp id 2 ρ)
    (hρ' : MemLp id 2 ρ') (hm : ∫ x, x ∂ρ' = ∫ x, x ∂ρ)
    (hc : covarianceBilin ρ' = covarianceBilin ρ) (L : E →L[ℝ] V) :
    ∫ x, x ∂ρ'.map L = ∫ x, x ∂ρ.map L ∧
      covarianceBilin (ρ'.map L) = covarianceBilin (ρ.map L) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  refine ⟨?_, ?_⟩
  · rw [L.integral_id_map (hρ'.integrable (by simp)),
      L.integral_id_map (hρ.integrable (by simp)), hm]
  · ext u v
    rw [covarianceBilin_map hρ', covarianceBilin_map hρ, hc]

/-- `∫ ‖L z‖²` depends on a law with finite second moment only through its mean and
covariance. -/
private lemma integral_norm_sq_map_eq {ρ ρ' : Measure E} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ρ'] (hρ : MemLp id 2 ρ) (hρ' : MemLp id 2 ρ')
    (hm : ∫ x, x ∂ρ' = ∫ x, x ∂ρ) (hc : covarianceBilin ρ' = covarianceBilin ρ)
    (L : E →L[ℝ] V) : ∫ z, ‖L z‖ ^ 2 ∂ρ' = ∫ z, ‖L z‖ ^ 2 ∂ρ := by
  obtain ⟨hm', hc'⟩ := integral_id_map_eq_and_covarianceBilin_map_eq hρ hρ' hm hc L
  have hL : ∀ (κ : Measure E), ∫ z, ‖L z‖ ^ 2 ∂κ = ∫ x, ‖x‖ ^ 2 ∂κ.map L := fun κ =>
    (integral_map L.continuous.aemeasurable
      (continuous_norm.pow 2).aestronglyMeasurable).symm
  have hmem : ∀ κ : Measure E, MemLp id 2 κ → MemLp id 2 (κ.map L) := fun κ hκ =>
    (memLp_map_measure_iff aestronglyMeasurable_id L.continuous.aemeasurable).2
      (L.comp_memLp' hκ)
  rw [hL, hL, integral_norm_sq_eq _ (hmem _ hρ'), integral_norm_sq_eq _ (hmem _ hρ), hm', hc']

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The quadratic cost is integrable against a coupling of two laws with finite second moment. -/
private lemma integrable_norm_sub_sq_of_isCoupling {μ ν : Measure V} {π : Measure (V × V)}
    (hπ : IsCoupling π μ ν) (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) :
    Integrable (fun z : V × V => ‖z.1 - z.2‖ ^ 2) π := by
  have h1 : MemLp Prod.fst 2 π := hμ.comp_measurePreserving hπ.measurePreserving_fst
  have h2 : MemLp Prod.snd 2 π := hν.comp_measurePreserving hπ.measurePreserving_snd
  exact (memLp_two_iff_integrable_sq_norm (h1.aestronglyMeasurable.sub h2.aestronglyMeasurable)).1
    (h1.sub h2)

/-- Two plans with integrable quadratic cost and the same cost integral have the same `L²`
displacement. -/
private lemma eLpNorm_edist_eq_of_integral_eq {π π' : Measure (V × V)}
    (h : Integrable (fun z : V × V => ‖z.1 - z.2‖ ^ 2) π)
    (h' : Integrable (fun z : V × V => ‖z.1 - z.2‖ ^ 2) π')
    (he : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π' = ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π) :
    eLpNorm (fun z : V × V => edist z.1 z.2) 2 π' =
      eLpNorm (fun z : V × V => edist z.1 z.2) 2 π := by
  have key : ∀ σ : Measure (V × V), Integrable (fun z : V × V => ‖z.1 - z.2‖ ^ 2) σ →
      eLpNorm (fun z : V × V => edist z.1 z.2) 2 σ ^ (2 : ℝ) =
        ENNReal.ofReal (∫ z, ‖z.1 - z.2‖ ^ 2 ∂σ) := fun σ hσ => by
    have := eLpNorm_rpow_eq_lintegral (p := 2) (by norm_num) (by norm_num)
      (f := fun z : V × V => edist z.1 z.2) (μ := σ) measurable_edist.aemeasurable
    rw [ENNReal.toReal_ofNat] at this
    rw [this, ← lintegral_edist_sq_eq_ofReal_integral hσ]
    exact lintegral_congr fun z => ENNReal.rpow_two _
  refine ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0) ?_
  simp only
  rw [key π' h', key π h, he]

/-- The cost integral over a plan on `V × V` (read through `WithLp 2`) depends on a law with finite
second moment only through its mean and covariance. -/
private lemma integral_cost_map_eq {ρ ρ' : Measure (WithLp 2 (V × V))} [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ρ'] (hρ : MemLp id 2 ρ) (hρ' : MemLp id 2 ρ')
    (hm : ∫ x, x ∂ρ' = ∫ x, x ∂ρ) (hc : covarianceBilin ρ' = covarianceBilin ρ) :
    ∫ z, ‖z.1 - z.2‖ ^ 2 ∂ρ'.map (WithLp.prodContinuousLinearEquiv 2 ℝ V V) =
      ∫ z, ‖z.1 - z.2‖ ^ 2 ∂ρ.map (WithLp.prodContinuousLinearEquiv 2 ℝ V V) := by
  let T := WithLp.prodContinuousLinearEquiv 2 ℝ V V
  let D : WithLp 2 (V × V) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V V).comp T.toContinuousLinearMap -
      (ContinuousLinearMap.snd ℝ V V).comp T.toContinuousLinearMap
  have hD : ∀ w, ‖(T w).1 - (T w).2‖ ^ 2 = ‖D w‖ ^ 2 := fun w => rfl
  rw [integral_map T.continuous.aemeasurable (by fun_prop),
    integral_map T.continuous.aemeasurable (by fun_prop)]
  simp_rw [hD]
  exact integral_norm_sq_map_eq hρ hρ' hm hc D

/-- Any coupling of two laws with finite second moment can be replaced by a coupling of two Gaussian
laws with the same means and covariances and the same quadratic cost. -/
private lemma exists_isCoupling_of_isGaussian {μ ν μ' ν' : Measure V} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsGaussian μ'] [IsGaussian ν'] (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν) (hmμ : ∫ x, x ∂μ' = ∫ x, x ∂μ)
    (hcμ : covarianceBilin μ' = covarianceBilin μ)
    (hmν : ∫ x, x ∂ν' = ∫ x, x ∂ν) (hcν : covarianceBilin ν' = covarianceBilin ν)
    {π : Measure (V × V)} (hπ : IsCoupling π μ ν) :
    ∃ π' : Measure (V × V), IsCoupling π' μ' ν' ∧
      ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π' = ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have := hπ.isProbabilityMeasure
  let T := WithLp.prodContinuousLinearEquiv 2 ℝ V V
  let P1 : WithLp 2 (V × V) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V V).comp T.toContinuousLinearMap
  let P2 : WithLp 2 (V × V) →L[ℝ] V :=
    (ContinuousLinearMap.snd ℝ V V).comp T.toContinuousLinearMap
  let ρ := π.map T.symm
  have : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff T.symm.continuous.aemeasurable).2 inferInstance
  have e1 : π.map Prod.fst = μ := hπ.fst_eq
  have e2 : π.map Prod.snd = ν := hπ.snd_eq
  have hρ : MemLp id 2 ρ := by
    refine (memLp_map_measure_iff aestronglyMeasurable_id T.symm.continuous.aemeasurable).2 ?_
    refine memLp_prodLp_iff.2 ⟨?_, ?_⟩
    · exact (memLp_map_measure_iff aestronglyMeasurable_id measurable_fst.aemeasurable).1
        (e1 ▸ hμ)
    · exact (memLp_map_measure_iff aestronglyMeasurable_id measurable_snd.aemeasurable).1
        (e2 ▸ hν)
  have m1 : ρ.map P1 = μ := by
    rw [Measure.map_map P1.continuous.measurable T.symm.continuous.measurable]; exact hπ.fst_eq
  have m2 : ρ.map P2 = ν := by
    rw [Measure.map_map P2.continuous.measurable T.symm.continuous.measurable]; exact hπ.snd_eq
  obtain ⟨ρ', hG, hmρ, hcρ⟩ := Probability.exists_isGaussian_integral_id_eq_covarianceBilin_eq ρ hρ
  have := hG
  have hρ' : MemLp id 2 ρ' := IsGaussian.memLp_two_id
  have k1 : ρ'.map P1 = μ' := by
    obtain ⟨a, b⟩ := integral_id_map_eq_and_covarianceBilin_map_eq hρ hρ' hmρ hcρ P1
    rw [m1] at a b
    exact IsGaussian.ext (a.trans hmμ.symm) (b.trans hcμ.symm)
  have k2 : ρ'.map P2 = ν' := by
    obtain ⟨a, b⟩ := integral_id_map_eq_and_covarianceBilin_map_eq hρ hρ' hmρ hcρ P2
    rw [m2] at a b
    exact IsGaussian.ext (a.trans hmν.symm) (b.trans hcν.symm)
  have hρT : ρ.map T = π := by
    rw [Measure.map_map T.continuous.measurable T.symm.continuous.measurable]
    simp [Function.comp_def]
  refine ⟨ρ'.map T, ⟨?_, ?_⟩, ?_⟩
  · show (ρ'.map T).map Prod.fst = μ'
    rw [Measure.map_map measurable_fst T.continuous.measurable]; exact k1
  · show (ρ'.map T).map Prod.snd = ν'
    rw [Measure.map_map measurable_snd T.continuous.measurable]; exact k2
  · rw [← hρT]
    exact integral_cost_map_eq hρ hρ' hmρ hcρ

/-- **Gelbrich's lower bound.** Let `μ` and `ν` be probability laws with finite second moment on a
finite-dimensional real inner product space, and let `μ'` and `ν'` be Gaussian laws with the same
means and covariances as `μ` and `ν` respectively. Then `W₂(μ', ν') ≤ W₂(μ, ν)`. -/
theorem wassersteinEDist_two_le_of_isGaussian {μ ν μ' ν' : Measure V} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] [IsGaussian μ'] [IsGaussian ν'] (hμ : MemLp id 2 μ)
    (hν : MemLp id 2 ν) (hmμ : ∫ x, x ∂μ' = ∫ x, x ∂μ)
    (hcμ : covarianceBilin μ' = covarianceBilin μ)
    (hmν : ∫ x, x ∂ν' = ∫ x, x ∂ν) (hcν : covarianceBilin ν' = covarianceBilin ν) :
    wassersteinEDist 2 μ' ν' ≤ wassersteinEDist 2 μ ν := by
  obtain ⟨π, hπ, hval⟩ := exists_isCoupling_eLpNorm_eq_wassersteinEDist (p := 2) (by norm_num)
    (by norm_num) μ ν ⟨_, isCoupling_prod μ ν⟩
  obtain ⟨π', hπ', hcost⟩ := exists_isCoupling_of_isGaussian hμ hν hmμ hcμ hmν hcν hπ
  calc wassersteinEDist 2 μ' ν'
      ≤ eLpNorm (fun z : V × V => edist z.1 z.2) 2 π' := wassersteinEDist_le hπ' 2
    _ = eLpNorm (fun z : V × V => edist z.1 z.2) 2 π :=
        eLpNorm_edist_eq_of_integral_eq (integrable_norm_sub_sq_of_isCoupling hπ hμ hν)
          (integrable_norm_sub_sq_of_isCoupling hπ' IsGaussian.memLp_two_id
            IsGaussian.memLp_two_id) hcost
    _ = wassersteinEDist 2 μ ν := hval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Gelbrich's lower bound in Bures form.** For probability laws `μ` and `ν` with finite second
moment on `ℝⁿ`, and `μ` with positive-definite covariance matrix, the squared quadratic Wasserstein
distance is at least the Bures expression `TauCeti.gaussianWassersteinSq` in the means and
covariance matrices. -/
theorem ofReal_gaussianWassersteinSq_le_wassersteinEDist_two_rpow_two
    (μ ν : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp id 2 μ) (hν : MemLp id 2 ν) (hS : (covMatrix μ).PosDef) :
    ENNReal.ofReal (gaussianWassersteinSq (∫ x, x ∂μ) (∫ x, x ∂ν) (covMatrix μ) (covMatrix ν)) ≤
      wassersteinEDist 2 μ ν ^ (2 : ℝ) := by
  have hSν := posSemidef_covMatrix ν hν
  have hSμ := posSemidef_covMatrix μ hμ
  have key := wassersteinEDist_two_le_of_isGaussian (μ := μ) (ν := ν)
    (μ' := multivariateGaussian (∫ x, x ∂μ) (covMatrix μ))
    (ν' := multivariateGaussian (∫ x, x ∂ν) (covMatrix ν)) hμ hν
    integral_id_multivariateGaussian ?_ integral_id_multivariateGaussian ?_
  · rw [← wassersteinEDist_two_multivariateGaussian_rpow_two hS hSν]
    exact ENNReal.rpow_le_rpow key (by norm_num)
  · ext x y
    rw [covarianceBilin_eq_covMatrix _ IsGaussian.memLp_two_id, covarianceBilin_eq_covMatrix μ hμ,
      Probability.covMatrix_multivariateGaussian _ hSμ]
  · ext x y
    rw [covarianceBilin_eq_covMatrix _ IsGaussian.memLp_two_id, covarianceBilin_eq_covMatrix ν hν,
      Probability.covMatrix_multivariateGaussian _ hSν]

end TauCeti
