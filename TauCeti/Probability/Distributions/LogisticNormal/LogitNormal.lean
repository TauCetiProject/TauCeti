/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogisticNormal.Basic
public import TauCeti.Probability.Distributions.LogitNormal.Basic

/-!
# Two-category logistic-normal laws

With two categories, normalized exponentiation is the scalar sigmoid in the non-reference
coordinate and its complement in the reference coordinate. Consequently the non-reference
coordinate of a simplex logistic-normal vector has the scalar logit-normal law. Conversely,
completing a scalar logit-normal variable by its complement recovers the entire simplex law.
These measure identities transfer the scalar density, CDF, moments, and quantile theory to the
two-category simplex law, including its zero-covariance boundary.

The scalar Gaussian marginal uses Mathlib's `measurePreserving_eval_multivariateGaussian`.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For two categories, the logistic chart consists of a sigmoid and its complement.
The subtype index `j` selects the non-reference category. -/
theorem logisticNormalChart_eq_of_card_eq_two (hι : Fintype.card ι = 2) (r : ι)
    (j : {i // i ≠ r}) (z : EuclideanSpace ℝ {i // i ≠ r}) :
    logisticNormalChart r z =
      WithLp.toLp 2 (fun i ↦ if i = r then 1 - Real.sigmoid (z j) else Real.sigmoid (z j)) := by
  have : Subsingleton {i // i ≠ r} := Fintype.card_le_one_iff_subsingleton.mp (by
    have := Fintype.card_subtype_lt (p := fun i ↦ i ≠ r) (x := r) (by simp)
    omega)
  have hsum : ∑ k, Real.exp (z k) = Real.exp (z j) := Fintype.sum_subsingleton _ j
  ext i
  by_cases hi : i = r
  · subst i
    simp only [logisticNormalChart_apply_self, hsum, ↓reduceIte]
    rw [← Real.sigmoid_neg, Real.sigmoid_def, neg_neg]
  · have hij : (⟨i, hi⟩ : {i // i ≠ r}) = j := Subsingleton.elim _ _
    have hi' : i = (j : ι) := congrArg Subtype.val hij
    subst i
    have hs : Real.exp (z j) / (1 + Real.exp (z j)) = Real.sigmoid (z j) := by
      rw [Real.sigmoid_def, Real.exp_neg]
      have hd : 1 + Real.exp (z j) ≠ 0 := by positivity
      field_simp
      ring
    simpa only [PiLp.toLp_apply, ite_eq_right j.property,
      logisticNormalChart_apply_coe, hsum] using hs

/-- The non-reference coordinate of a two-category logistic-normal vector has the scalar
logit-normal law. Positive semidefinite covariance includes the zero-covariance Dirac case. -/
@[simp]
theorem map_eval_logisticNormalMeasure_of_card_eq_two (hι : Fintype.card ι = 2) (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ r}) :
    (logisticNormalMeasure r m S).map (fun x ↦ x j) =
      logitNormalMeasure (m j) (S j j).toNNReal := by
  rw [logisticNormalMeasure_def, logitNormalMeasure_def,
    ← (measurePreserving_eval_multivariateGaussian (μ := m) hS (i := j)).map_eq,
    Measure.map_map (by fun_prop) (measurable_logisticNormalChart r),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp [logisticNormalChart_eq_of_card_eq_two hι r j, j.property]

/-- Completing a scalar logit-normal variable by its complement gives the two-category
simplex logistic-normal law, with the complement in the reference category. -/
theorem map_logitNormalMeasure_eq_logisticNormalMeasure (hι : Fintype.card ι = 2) (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hS : S.PosSemidef) (j : {i // i ≠ r}) :
    (logitNormalMeasure (m j) (S j j).toNNReal).map
        (fun x ↦ WithLp.toLp 2 (fun i ↦ if i = r then 1 - x else x)) =
      logisticNormalMeasure r m S := by
  rw [logitNormalMeasure_def,
    ← (measurePreserving_eval_multivariateGaussian (μ := m) hS (i := j)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop), logisticNormalMeasure_def]
  congr 1
  funext z
  exact (logisticNormalChart_eq_of_card_eq_two hι r j z).symm

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- The non-reference coordinate of a two-category logistic-normal random vector has the
scalar logit-normal law, including at zero covariance. -/
theorem eval_logisticNormalMeasure_of_card_eq_two {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} {r : ι} {X : Ω → EuclideanSpace ℝ ι}
    {m : EuclideanSpace ℝ {i // i ≠ r}} {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hX : HasLaw X (logisticNormalMeasure r m S) P) (hι : Fintype.card ι = 2)
    (hS : S.PosSemidef) (j : {i // i ≠ r}) :
    HasLaw (fun ω ↦ X ω j) (logitNormalMeasure (m j) (S j j).toNNReal) P := by
  exact HasLaw.comp ⟨by fun_prop, map_eval_logisticNormalMeasure_of_card_eq_two hι r m hS j⟩ hX

/-- A scalar logit-normal random variable and its complement form a two-category simplex
logistic-normal vector. -/
theorem complement_logitNormalMeasure {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} {r : ι} {X : Ω → ℝ}
    {m : EuclideanSpace ℝ {i // i ≠ r}} {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    {j : {i // i ≠ r}} (hX : HasLaw X (logitNormalMeasure (m j) (S j j).toNNReal) P)
    (hι : Fintype.card ι = 2) (hS : S.PosSemidef) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun i ↦ if i = r then 1 - X ω else X ω))
      (logisticNormalMeasure r m S) P := by
  exact HasLaw.comp (Y := fun x : ℝ ↦ WithLp.toLp 2 (fun i ↦ if i = r then 1 - x else x))
    ⟨by fun_prop, map_logitNormalMeasure_eq_logisticNormalMeasure hι r m hS j⟩ hX

end ProbabilityTheory.HasLaw
