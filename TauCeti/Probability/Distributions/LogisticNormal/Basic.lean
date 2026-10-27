/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Probability.Distributions.Dirichlet.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Simplex logistic-normal laws

The logistic-normal law is the image of a Gaussian under normalized exponentiation with one
reference coordinate fixed to zero. It lives on the same ambient Euclidean space as the Dirichlet
law. Its additive log ratios recover the original Gaussian, including singular covariances.

This file constructs the chart and its inverse on the strictly positive simplex, defines the
law, and proves probability, simplex concentration, joint parameter measurability, and the
Gaussian log-ratio law. Zero or invalid covariance gives a point mass. With one category the
law is the point mass at one.

The normalization reuses `dirichletNormalize`; Gaussian marginals use Mathlib's
`measurePreserving_eval_multivariateGaussian`.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Normalized exponentiation with reference coordinate `r` fixed to zero before exponentiating.
The input consists of the log ratios of the other coordinates to the reference coordinate. -/
def logisticNormalChart (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r}) :
    EuclideanSpace ℝ ι :=
  dirichletNormalize ((Equiv.funSplitAt r ℝ).symm (1, fun j ↦ Real.exp (z j)))

/-- A coordinate of the logistic chart, with its strictly positive normalizer displayed. -/
theorem logisticNormalChart_apply (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r}) (i : ι) :
    logisticNormalChart r z i =
      (Equiv.funSplitAt r ℝ).symm (1, fun j ↦ Real.exp (z j)) i /
        (1 + ∑ j, Real.exp (z j)) := by
  rw [logisticNormalChart, dirichletNormalize_apply,
    Fintype.sum_eq_add_sum_subtype_ne _ r]
  simp only [Equiv.funSplitAt_symm_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  simp [j.property]

/-- The reference coordinate is the reciprocal normalizer. -/
@[simp]
theorem logisticNormalChart_apply_self (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r}) :
    logisticNormalChart r z r = (1 + ∑ j, Real.exp (z j))⁻¹ := by
  simp [logisticNormalChart_apply]

/-- Away from the reference coordinate, the chart is normalized exponentiation. -/
@[simp]
theorem logisticNormalChart_apply_coe (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r})
    (j : {i // i ≠ r}) :
    logisticNormalChart r z j = Real.exp (z j) / (1 + ∑ k, Real.exp (z k)) := by
  simp [logisticNormalChart_apply, j.property]

/-- Every coordinate of the logistic chart is strictly positive. -/
theorem logisticNormalChart_pos (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r}) (i : ι) :
    0 < logisticNormalChart r z i := by
  have hD : 0 < 1 + ∑ j, Real.exp (z j) := by positivity
  rw [logisticNormalChart_apply]
  apply div_pos _ hD
  simp only [Equiv.funSplitAt_symm_apply]
  split_ifs <;> positivity

/-- The coordinates of the logistic chart sum to one. -/
@[simp]
theorem sum_logisticNormalChart (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r}) :
    ∑ i, logisticNormalChart r z i = 1 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ r]
  simp only [logisticNormalChart_apply_self, logisticNormalChart_apply_coe, ← Finset.sum_div]
  have hD : 0 < 1 + ∑ j, Real.exp (z j) := by positivity
  field_simp

/-- The logistic chart is continuous on the entire log-ratio space. -/
@[fun_prop]
theorem continuous_logisticNormalChart (r : ι) : Continuous (logisticNormalChart r) := by
  have hcoords : Continuous (fun z : EuclideanSpace ℝ {i // i ≠ r} ↦
      fun i ↦ logisticNormalChart r z i) := by
    apply continuous_pi
    intro i
    have hD : ∀ z : EuclideanSpace ℝ {i // i ≠ r},
        1 + ∑ j, Real.exp (z j) ≠ 0 := fun z ↦ by positivity
    simp_rw [logisticNormalChart_apply, Equiv.funSplitAt_symm_apply]
    split_ifs
    · exact continuous_const.div (by fun_prop) hD
    · exact (by fun_prop : Continuous (fun z : EuclideanSpace ℝ {i // i ≠ r} ↦
        Real.exp (z ⟨i, by assumption⟩))).div (by fun_prop) hD
  exact (EuclideanSpace.equiv ι ℝ).symm.continuous.comp hcoords

/-- The logistic chart is measurable. -/
@[fun_prop]
theorem measurable_logisticNormalChart (r : ι) : Measurable (logisticNormalChart r) :=
  (continuous_logisticNormalChart r).measurable

/-- Additive log ratios to the reference coordinate. This map is totalized by real division
and logarithm; the inverse identities concern the strictly positive simplex. -/
def logisticNormalLogRatio (r : ι) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ {i // i ≠ r} :=
  WithLp.toLp 2 (fun j ↦ Real.log (x j / x r))

omit [Fintype ι] [DecidableEq ι] in
/-- A coordinate of the additive log-ratio map. -/
@[simp]
theorem logisticNormalLogRatio_apply (r : ι) (x : EuclideanSpace ℝ ι)
    (j : {i // i ≠ r}) : logisticNormalLogRatio r x j = Real.log (x j / x r) := (rfl)

omit [Fintype ι] [DecidableEq ι] in
/-- The totalized additive log-ratio map is measurable. -/
@[fun_prop]
theorem measurable_logisticNormalLogRatio (r : ι) : Measurable (logisticNormalLogRatio r) := by
  unfold logisticNormalLogRatio
  fun_prop

/-- Taking additive log ratios undoes the logistic chart. -/
@[simp]
theorem logisticNormalLogRatio_chart (r : ι) (z : EuclideanSpace ℝ {i // i ≠ r}) :
    logisticNormalLogRatio r (logisticNormalChart r z) = z := by
  ext j
  have hD : 1 + ∑ k, Real.exp (z k) ≠ 0 := by positivity
  simp [logisticNormalLogRatio_apply, hD]

/-- The logistic chart recovers every strictly positive vector whose coordinates sum to one. -/
theorem logisticNormalChart_logRatio (r : ι) {x : EuclideanSpace ℝ ι}
    (hx : ∀ i, 0 < x i) (hsum : ∑ i, x i = 1) :
    logisticNormalChart r (logisticNormalLogRatio r x) = x := by
  have heq : (Equiv.funSplitAt r ℝ).symm
      (1, fun j : {i // i ≠ r} ↦ Real.exp (logisticNormalLogRatio r x j)) =
      fun i ↦ (x r)⁻¹ * x i := by
    ext i
    simp only [Equiv.funSplitAt_symm_apply, logisticNormalLogRatio_apply]
    split_ifs with hi
    · subst i
      simp [(hx r).ne']
    · rw [Real.exp_log (div_pos (hx i) (hx r))]
      ring
  rw [logisticNormalChart, heq, dirichletNormalize_const_mul (inv_ne_zero (hx r).ne')]
  ext i
  simp [dirichletNormalize_apply, hsum]

/-- The logistic chart is injective. -/
theorem logisticNormalChart_injective (r : ι) : Function.Injective (logisticNormalChart r) :=
  Function.LeftInverse.injective (logisticNormalLogRatio_chart r)

/-- The image of the logistic chart is exactly the strictly positive standard simplex. -/
theorem range_logisticNormalChart (r : ι) :
    range (logisticNormalChart r) =
      {x : EuclideanSpace ℝ ι | (∀ i, 0 < x i) ∧ ∑ i, x i = 1} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨logisticNormalChart_pos r z, sum_logisticNormalChart r z⟩
  · rintro ⟨hx, hsum⟩
    exact ⟨logisticNormalLogRatio r x, logisticNormalChart_logRatio r hx hsum⟩

/-- The simplex logistic-normal law with Gaussian log-ratio mean `m`, covariance `S`, and
reference category `r`. Invalid covariance inherits the Gaussian point-mass fallback. -/
def logisticNormalMeasure (r : ι) (m : EuclideanSpace ℝ {i // i ≠ r})
    (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) : Measure (EuclideanSpace ℝ ι) :=
  (multivariateGaussian m S).map (logisticNormalChart r)

/-- The defining Gaussian pushforward of the simplex logistic-normal law. -/
theorem logisticNormalMeasure_def (r : ι) (m : EuclideanSpace ℝ {i // i ≠ r})
    (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) :
    logisticNormalMeasure r m S = (multivariateGaussian m S).map (logisticNormalChart r) := (rfl)

instance isProbabilityMeasure_logisticNormalMeasure (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) :
    IsProbabilityMeasure (logisticNormalMeasure r m S) := by
  rw [logisticNormalMeasure_def]
  infer_instance

/-- A zero covariance gives a point mass at the chart of the mean. -/
@[simp]
theorem logisticNormalMeasure_zero (r : ι) (m : EuclideanSpace ℝ {i // i ≠ r}) :
    logisticNormalMeasure r m 0 = Measure.dirac (logisticNormalChart r m) := by
  simp [logisticNormalMeasure_def, multivariateGaussian]

/-- An invalid covariance gives the same point-mass fallback as its Gaussian source. -/
theorem logisticNormalMeasure_of_not_posSemidef (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : ¬ S.PosSemidef) :
    logisticNormalMeasure r m S = Measure.dirac (logisticNormalChart r m) := by
  rw [logisticNormalMeasure_def, multivariateGaussian_of_not_posSemidef m hS,
    Measure.map_dirac' (measurable_logisticNormalChart r)]

/-- Logistic-normal vectors lie on the strictly positive simplex, for every covariance. -/
theorem ae_mem_simplex_logisticNormalMeasure (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) :
    ∀ᵐ x ∂logisticNormalMeasure r m S, (∀ i, 0 < x i) ∧ ∑ i, x i = 1 := by
  rw [logisticNormalMeasure_def]
  refine (ae_map_iff (measurable_logisticNormalChart r).aemeasurable
    (EuclideanSpace.measurableSet_setOf_forall_pos.inter
      (measurableSet_eq_fun (by fun_prop) measurable_const))).mpr ?_
  exact ae_of_all _ fun z ↦ ⟨logisticNormalChart_pos r z, sum_logisticNormalChart r z⟩

/-- Taking all additive log ratios recovers the source Gaussian, including its fallbacks. -/
@[simp]
theorem map_logRatio_logisticNormalMeasure (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) :
    (logisticNormalMeasure r m S).map (logisticNormalLogRatio r) = multivariateGaussian m S := by
  rw [logisticNormalMeasure_def, Measure.map_map (measurable_logisticNormalLogRatio r)
    (measurable_logisticNormalChart r)]
  simp only [Function.comp_def, logisticNormalLogRatio_chart, Measure.map_id']

/-- Each additive log ratio has the corresponding scalar Gaussian law. -/
theorem map_logRatio_eval_logisticNormalMeasure (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ r}) :
    (logisticNormalMeasure r m S).map (fun x ↦ Real.log (x j / x r)) =
      gaussianReal (m j) (S j j).toNNReal := by
  rw [← (measurePreserving_eval_multivariateGaussian (μ := m) hS (i := j)).map_eq,
    ← map_logRatio_logisticNormalMeasure r m S,
    Measure.map_map (by fun_prop) (measurable_logisticNormalLogRatio r)]
  rfl

/-- Joint Giry measurability in the Gaussian mean and all raw covariance coordinates. -/
@[fun_prop]
theorem measurable_logisticNormalMeasure (r : ι) :
    Measurable (fun p : EuclideanSpace ℝ {i // i ≠ r} ×
        ({i // i ≠ r} → {i // i ≠ r} → ℝ) ↦
      logisticNormalMeasure r p.1 (Matrix.of p.2)) := by
  simp only [logisticNormalMeasure_def]
  exact (Measure.measurable_map _ (measurable_logisticNormalChart r)).comp
    (ProbabilityTheory.measurable_multivariateGaussian.comp
      (measurable_fst.prodMk (by fun_prop)))

/-- With one category, the logistic-normal law is the point mass at the unique simplex point. -/
@[simp]
theorem logisticNormalMeasure_of_subsingleton [Subsingleton ι] (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) :
    logisticNormalMeasure r m S = Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ (1 : ℝ))) := by
  have : IsEmpty {i // i ≠ r} := ⟨fun i ↦ i.property (Subsingleton.elim _ _)⟩
  have hchart : logisticNormalChart r = fun _ ↦ WithLp.toLp 2 (fun _ : ι ↦ (1 : ℝ)) := by
    ext z i
    have hi : i = r := Subsingleton.elim _ _
    subst i
    simp
  simp [logisticNormalMeasure_def, hchart]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

/-- Normalized exponentiation of Gaussian log ratios has the simplex logistic-normal law. -/
theorem logisticNormalChart_multivariateGaussian {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} {r : ι}
    {X : Ω → EuclideanSpace ℝ {i // i ≠ r}} {m : EuclideanSpace ℝ {i // i ≠ r}}
    {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ} (hX : HasLaw X (multivariateGaussian m S) P) :
    HasLaw (fun ω ↦ TauCeti.Probability.logisticNormalChart r (X ω))
      (TauCeti.Probability.logisticNormalMeasure r m S) P := by
  simpa only [TauCeti.Probability.logisticNormalMeasure_def, Function.comp_def] using
    HasLaw.comp ⟨(TauCeti.Probability.measurable_logisticNormalChart r).aemeasurable, rfl⟩ hX

end ProbabilityTheory.HasLaw
