/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.CompoundPoisson.Basic
public import TauCeti.Probability.Moments.ConvolutionPower
public import TauCeti.Probability.Moments.Mixture
public import TauCeti.Probability.Moments.Covariance

/-!
# Means and covariances of compound Poisson laws

A compound Poisson sum of rate `r` and jump law `μ` has mean `r • ∫ x, x ∂μ`.
Its covariance is `r` times the jump's uncentered second moment: the randomness of the
number of jumps contributes the product of the jump means in addition to the jump covariance.
In particular, its scalar variance is `r * ∫ x, x ^ 2 ∂μ`.

The first and second moment hypotheses concern only the jump law. Polynomial absolute-moment
bounds for convolution powers justify integration over the Poisson count, so these results also
apply to jump laws without exponential moments. Rate zero is included throughout.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. I,
  third edition, Wiley, 1968, chapter XII, section 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti.Probability

section Normed

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]
  {μ : Measure E} [IsProbabilityMeasure μ]

/-- Compound Poisson laws preserve every finite jump moment of order `p ≥ 1`. -/
theorem memLp_id_compoundPoissonMeasure {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hμ : MemLp id p μ) (r : ℝ≥0) :
    MemLp id p (compoundPoissonMeasure r μ) := by
  have hp_real : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_le_toReal (by simp) hp_top).2 hp
  have hmeas : AEStronglyMeasurable id (compoundPoissonMeasure r μ) := by
    rw [compoundPoissonMeasure_eq_sum]
    exact AEStronglyMeasurable.sum_measure fun n ↦
      (μ.memLp_id_convolutionPower hμ n).aestronglyMeasurable.smul_measure _
  rw [← integrable_norm_rpow_iff hmeas (ne_of_gt (zero_lt_one.trans_le hp)) hp_top]
  simp only [id_eq]
  rw [compoundPoissonMeasure_def, Measure.integrable_bind_iff Measurable.of_discrete
    (by simpa only [compoundPoissonMeasure_def, id_eq] using
      (hmeas.norm.aemeasurable.pow_const p.toReal).aestronglyMeasurable)]
  simp only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  refine ⟨.of_forall fun n ↦ ?_, ?_⟩
  · simpa only [id_eq] using
      (μ.memLp_id_convolutionPower hμ n).integrable_norm_rpow'
  · apply ((integrable_natCast_rpow_poissonMeasure r (p := p.toReal)
      ENNReal.toReal_nonneg).mul_const
      (∫ x, ‖x‖ ^ p.toReal ∂μ)).mono' (by fun_prop)
    filter_upwards [] with n
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    exact μ.integral_norm_rpow_convolutionPower_le hp_real
      (by rwa [ENNReal.ofReal_toReal hp_top]) n

/-- A finite first jump moment gives a finite first compound Poisson moment. -/
theorem integrable_id_compoundPoissonMeasure (hμ : Integrable id μ) (r : ℝ≥0) :
    Integrable id (compoundPoissonMeasure r μ) := by
  rw [← memLp_one_iff_integrable]
  exact memLp_id_compoundPoissonMeasure le_rfl (by simp)
    (memLp_one_iff_integrable.2 hμ) r

/-- The compound Poisson mean is the rate times the jump mean, including at rate zero. -/
@[simp]
theorem integral_id_compoundPoissonMeasure [NormedSpace ℝ E] [CompleteSpace E]
    (hμ : Integrable id μ) (r : ℝ≥0) :
    ∫ x, x ∂compoundPoissonMeasure r μ = (r : ℝ) • ∫ x, x ∂μ := by
  have hint := integrable_id_compoundPoissonMeasure hμ r
  rw [compoundPoissonMeasure_def] at hint ⊢
  have hbind := Measure.integral_bind Measurable.of_discrete.aemeasurable hint
  simp only [id_eq] at hbind
  rw [hbind]
  simp_rw [μ.integral_id_convolutionPower hμ, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [integral_smul_const]
  rw [integral_natCast_poissonMeasure]

/-- A finite second jump moment gives a finite second compound Poisson moment. -/
theorem memLp_two_id_compoundPoissonMeasure (hμ : MemLp id 2 μ) (r : ℝ≥0) :
    MemLp id 2 (compoundPoissonMeasure r μ) := by
  exact memLp_id_compoundPoissonMeasure (by norm_num) (by simp) hμ r

variable [NormedSpace ℝ E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → E} {r : ℝ≥0}

/-- A compound Poisson random variable has mean equal to the rate times the jump mean. -/
theorem integral_of_hasLaw_compoundPoissonMeasure [CompleteSpace E] (hμ : Integrable id μ)
    (hX : HasLaw X (compoundPoissonMeasure r μ) P) :
    ∫ ω, X ω ∂P = (r : ℝ) • ∫ x, x ∂μ := by
  simpa only [Function.id_comp, id_eq, integral_id_compoundPoissonMeasure hμ] using
    hX.integral_comp (integrable_id_compoundPoissonMeasure hμ r).aestronglyMeasurable

end Normed

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableAdd₂ E]
  {μ : Measure E} [IsProbabilityMeasure μ]

/-- Compound Poisson laws preserve every finite moment of order `p ≥ 1` of a linear
observable. -/
theorem memLp_continuousLinearMap_compoundPoissonMeasure {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp_top : p ≠ ∞) (L : E →L[ℝ] ℝ) (hL : MemLp L p μ) (r : ℝ≥0) :
    MemLp L p (compoundPoissonMeasure r μ) := by
  have hmap : MemLp id p (μ.map L) :=
    (memLp_map_measure_iff (by fun_prop) (by fun_prop)).2 (by simpa using hL)
  apply (memLp_map_measure_iff (g := id) (f := L) (by fun_prop) (by fun_prop)).1
  have htransport := map_compoundPoissonMeasure r μ L.toAddMonoidHom L.continuous.measurable
  simp only [LinearMap.toAddMonoidHom_coe, ContinuousLinearMap.coe_coe] at htransport
  rw [htransport]
  exact memLp_id_compoundPoissonMeasure hp hp_top hmap r

/-- A finite first moment of a linear observable of the jump law gives a finite first
moment of that observable under the compound Poisson law. -/
theorem integrable_continuousLinearMap_compoundPoissonMeasure (L : E →L[ℝ] ℝ)
    (hL : Integrable L μ) (r : ℝ≥0) :
    Integrable L (compoundPoissonMeasure r μ) := by
  rw [← memLp_one_iff_integrable]
  exact memLp_continuousLinearMap_compoundPoissonMeasure le_rfl (by simp) L
    (memLp_one_iff_integrable.2 hL) r

/-- The mean of a linear observable under a compound Poisson law is the rate times its
jump mean. Only the observed first moment needs to be finite. -/
@[simp]
theorem integral_continuousLinearMap_compoundPoissonMeasure (L : E →L[ℝ] ℝ)
    (hL : Integrable L μ) (r : ℝ≥0) :
    ∫ x, L x ∂compoundPoissonMeasure r μ = (r : ℝ) * ∫ x, L x ∂μ := by
  have hint := integrable_continuousLinearMap_compoundPoissonMeasure L hL r
  rw [compoundPoissonMeasure_def] at hint ⊢
  rw [Measure.integral_bind Measurable.of_discrete.aemeasurable hint]
  simp_rw [μ.integral_continuousLinearMap_convolutionPower L hL]
  rw [integral_mul_const, integral_natCast_poissonMeasure]

/-- The covariance of two linear observables of a compound Poisson sum is the rate times
their uncentered jump cross moment. Only the two observed second moments need be finite. -/
@[simp]
theorem covariance_compoundPoissonMeasure (L M : E →L[ℝ] ℝ)
    (hL : MemLp L 2 μ) (hM : MemLp M 2 μ) (r : ℝ≥0) :
    covariance L M (compoundPoissonMeasure r μ) = (r : ℝ) * ∫ x, L x * M x ∂μ := by
  have hLcp : MemLp L 2 (compoundPoissonMeasure r μ) := by
    exact memLp_continuousLinearMap_compoundPoissonMeasure (by norm_num) (by simp) L hL r
  have hMcp : MemLp M 2 (compoundPoissonMeasure r μ) := by
    exact memLp_continuousLinearMap_compoundPoissonMeasure (by norm_num) (by simp) M hM r
  rw [compoundPoissonMeasure_def] at hLcp hMcp ⊢
  rw [covariance_bind Measurable.of_discrete (.of_forall fun n ↦ inferInstance) hLcp hMcp]
  simp_rw [μ.covariance_convolutionPower L M hL hM,
    μ.integral_continuousLinearMap_convolutionPower L (hL.integrable one_le_two),
    μ.integral_continuousLinearMap_convolutionPower M (hM.integrable one_le_two)]
  rw [integral_mul_const, covariance_mul_const_left, covariance_mul_const_right,
    covariance_self (by fun_prop)]
  rw [integral_natCast_poissonMeasure, variance_natCast_poissonMeasure,
    covariance_eq_sub hL hM]
  simp only [Pi.mul_apply]
  ring

/-- The scalar compound Poisson variance is the rate times the uncentered second jump moment. -/
@[simp]
theorem variance_id_compoundPoissonMeasure {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MemLp id 2 ν) (r : ℝ≥0) :
    variance id (compoundPoissonMeasure r ν) = (r : ℝ) * ∫ x, x ^ 2 ∂ν := by
  have h := covariance_compoundPoissonMeasure (ContinuousLinearMap.id ℝ ℝ)
    (ContinuousLinearMap.id ℝ ℝ) hν hν r
  simpa only [ContinuousLinearMap.coe_id', covariance_self aemeasurable_id, id_eq, pow_two]
    using h

/-- The compound Poisson covariance matrix is the rate times the jump's raw second-moment
matrix, rather than the jump covariance matrix. -/
@[simp]
theorem covMatrix_compoundPoissonMeasure {ι : Type*} [Fintype ι]
    {ν : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure ν] (hν : MemLp id 2 ν)
    (r : ℝ≥0) :
    covMatrix (compoundPoissonMeasure r ν) =
      (r : ℝ) • (fun i j ↦ ∫ x, x i * x j ∂ν) := by
  ext i j
  simpa only [covMatrix_apply, Pi.smul_apply, smul_eq_mul, EuclideanSpace.coe_proj] using
    covariance_compoundPoissonMeasure (EuclideanSpace.proj i) (EuclideanSpace.proj j)
      (by simpa only [id_eq] using
        hν.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i))
      (by simpa only [id_eq] using
        hν.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)) r

/-- The covariance bilinear form of a compound Poisson law is the rate times the uncentered
second-moment bilinear form of the jump law. -/
@[simp]
theorem covarianceBilin_compoundPoissonMeasure {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    [MeasurableAdd₂ F] {ν : Measure F} [IsProbabilityMeasure ν]
    (hν : MemLp id 2 ν) (r : ℝ≥0) (x y : F) :
    covarianceBilin (compoundPoissonMeasure r ν) x y =
      (r : ℝ) * ∫ z, ⟪x, z⟫ * ⟪y, z⟫ ∂ν := by
  rw [covarianceBilin_apply_eq_cov (memLp_two_id_compoundPoissonMeasure hν r)]
  exact covariance_compoundPoissonMeasure (innerSL ℝ x) (innerSL ℝ y)
    (by simpa only [id_eq] using hν.continuousLinearMap_comp (innerSL ℝ x))
    (by simpa only [id_eq] using hν.continuousLinearMap_comp (innerSL ℝ y)) r

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → E} {r : ℝ≥0}

/-- A linear observable of a compound Poisson random variable has mean equal to the rate
times its jump mean. Only the observed first moment needs to be finite. -/
theorem integral_continuousLinearMap_of_hasLaw_compoundPoissonMeasure
    (hX : HasLaw X (compoundPoissonMeasure r μ) P) (L : E →L[ℝ] ℝ)
    (hL : Integrable L μ) :
    ∫ ω, L (X ω) ∂P = (r : ℝ) * ∫ x, L x ∂μ := by
  simpa only [Function.comp_apply, integral_continuousLinearMap_compoundPoissonMeasure L hL]
    using hX.integral_comp
      (integrable_continuousLinearMap_compoundPoissonMeasure L hL r).aestronglyMeasurable

/-- Linear observables of a compound Poisson random variable have covariance given by the
uncentered second jump moment. Only the two observed second moments need be finite. -/
theorem covariance_of_hasLaw_compoundPoissonMeasure
    (hX : HasLaw X (compoundPoissonMeasure r μ) P) (L M : E →L[ℝ] ℝ)
    (hL : MemLp L 2 μ) (hM : MemLp M 2 μ) :
    covariance (fun ω ↦ L (X ω)) (fun ω ↦ M (X ω)) P =
      (r : ℝ) * ∫ x, L x * M x ∂μ := by
  rw [hX.covariance_fun_comp (f := L) (g := M) (by fun_prop) (by fun_prop),
    covariance_compoundPoissonMeasure L M hL hM]

/-- The variance of a real compound Poisson random variable is the rate times the second
raw jump moment. -/
theorem variance_of_hasLaw_compoundPoissonMeasure {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {Y : Ω → ℝ} (hν : MemLp id 2 ν) (hY : HasLaw Y (compoundPoissonMeasure r ν) P) :
    variance Y P = (r : ℝ) * ∫ x, x ^ 2 ∂ν := by
  rw [hY.variance_eq, variance_id_compoundPoissonMeasure hν]

end TauCeti.Probability
