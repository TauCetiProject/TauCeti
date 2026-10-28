/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogisticNormal.Basic

/-!
# Moments of simplex logistic-normal laws

All natural mixed moments of a simplex logistic-normal vector are integrable and are Gaussian
integrals of products of powers of the logistic chart. The mean and covariance are expressed by
these Gaussian integrals; no elementary closed forms are asserted. Every real linear observable
has exponential moments at every real parameter because the simplex is bounded.

The statements hold for every covariance parameter, including singular covariances and the
invalid-covariance point-mass fallback. They also include the one-category law. The proofs use
`ae_mem_simplex_logisticNormalMeasure` and the defining Gaussian pushforward, together with
Mathlib's coordinatewise `MemLp` criterion and covariance identity.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ)

/-- Each logistic-normal coordinate lies in `(0, 1]`, including in the one-category case. -/
theorem ae_mem_Ioc_eval_logisticNormalMeasure (i : ι) :
    ∀ᵐ x ∂logisticNormalMeasure r m S, x i ∈ Ioc 0 1 := by
  filter_upwards [ae_mem_simplex_logisticNormalMeasure r m S] with x hx
  exact ⟨hx.1 i, hx.2 ▸ Finset.single_le_sum (fun j _ ↦ (hx.1 j).le) (Finset.mem_univ i)⟩

/-- Every coordinate has finite moments of every order, and is essentially bounded. -/
theorem memLp_eval_logisticNormalMeasure (i : ι) (p : ℝ≥0∞) :
    MemLp (fun x ↦ x i) p (logisticNormalMeasure r m S) :=
  memLp_of_bounded ((ae_mem_Ioc_eval_logisticNormalMeasure r m S i).mono
    fun _ hx ↦ ⟨hx.1.le, hx.2⟩) (by fun_prop) p

/-- Logistic-normal vectors have finite moments of every order, and are essentially bounded. -/
theorem memLp_id_logisticNormalMeasure (p : ℝ≥0∞) :
    MemLp id p (logisticNormalMeasure r m S) :=
  MemLp.of_eval_piLp fun i ↦ memLp_eval_logisticNormalMeasure r m S i p

/-- Every natural mixed moment is integrable, including the constant zeroth moment. -/
theorem integrable_prod_pow_logisticNormalMeasure (k : ι → ℕ) :
    Integrable (fun x ↦ ∏ i, x i ^ k i) (logisticNormalMeasure r m S) := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  filter_upwards [ae_mem_simplex_logisticNormalMeasure r m S] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ ↦ pow_nonneg (hx.1 i).le _)]
  exact Finset.prod_le_one₀ (fun i _ ↦ pow_nonneg (hx.1 i).le _) fun i _ ↦
    pow_le_one₀ (hx.1 i).le
      (hx.2 ▸ Finset.single_le_sum (fun j _ ↦ (hx.1 j).le) (Finset.mem_univ i))

/-- Natural mixed moments are Gaussian integrals of products of powers of the logistic chart. -/
theorem integral_prod_pow_logisticNormalMeasure (k : ι → ℕ) :
    ∫ x, ∏ i, x i ^ k i ∂logisticNormalMeasure r m S =
      ∫ z, ∏ i, logisticNormalChart r z i ^ k i ∂multivariateGaussian m S := by
  rw [logisticNormalMeasure_def, integral_map (by fun_prop) (by fun_prop)]

/-- The Bochner mean is the Gaussian integral of the logistic chart. -/
theorem integral_id_logisticNormalMeasure :
    ∫ x, x ∂logisticNormalMeasure r m S =
      ∫ z, logisticNormalChart r z ∂multivariateGaussian m S := by
  rw [logisticNormalMeasure_def, integral_map (by fun_prop) (by fun_prop)]

/-- Each coordinate mean is the Gaussian integral of the corresponding chart coordinate. -/
theorem integral_eval_logisticNormalMeasure (i : ι) :
    ∫ x, x i ∂logisticNormalMeasure r m S =
      ∫ z, logisticNormalChart r z i ∂multivariateGaussian m S := by
  rw [logisticNormalMeasure_def, integral_map (by fun_prop) (by fun_prop)]

/-- Coordinate covariances are Gaussian second chart moments minus products of first moments. -/
theorem covariance_eval_logisticNormalMeasure (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; logisticNormalMeasure r m S] =
      (∫ z, logisticNormalChart r z i * logisticNormalChart r z j ∂multivariateGaussian m S) -
        (∫ z, logisticNormalChart r z i ∂multivariateGaussian m S) *
          (∫ z, logisticNormalChart r z j ∂multivariateGaussian m S) := by
  rw [covariance_eq_sub (memLp_eval_logisticNormalMeasure r m S i 2)
    (memLp_eval_logisticNormalMeasure r m S j 2), integral_eval_logisticNormalMeasure,
    integral_eval_logisticNormalMeasure]
  congr 1
  rw [logisticNormalMeasure_def, integral_map (by fun_prop) (by fun_prop)]
  rfl

/-- A coordinate variance is its second Gaussian chart moment minus the square of its mean. -/
theorem variance_eval_logisticNormalMeasure (i : ι) :
    variance (fun x ↦ x i) (logisticNormalMeasure r m S) =
      (∫ z, logisticNormalChart r z i ^ 2 ∂multivariateGaussian m S) -
        (∫ z, logisticNormalChart r z i ∂multivariateGaussian m S) ^ 2 := by
  rw [← covariance_self (by fun_prop), covariance_eval_logisticNormalMeasure]
  simp only [sq]

/-- The covariance matrix is assembled from first and second Gaussian chart moments. -/
theorem covMatrix_logisticNormalMeasure :
    covMatrix (logisticNormalMeasure r m S) =
      Matrix.of (fun i j ↦
        (∫ z, logisticNormalChart r z i * logisticNormalChart r z j ∂multivariateGaussian m S) -
          (∫ z, logisticNormalChart r z i ∂multivariateGaussian m S) *
            (∫ z, logisticNormalChart r z j ∂multivariateGaussian m S)) := by
  ext i j
  simpa only [covMatrix_apply, Matrix.of_apply] using
    covariance_eval_logisticNormalMeasure r m S i j

/-- Every real linear observable has all exponential moments, including at degenerate parameters. -/
@[simp]
theorem integrableExpSet_inner_logisticNormalMeasure (θ : EuclideanSpace ℝ ι) :
    integrableExpSet (fun x ↦ ⟪θ, x⟫) (logisticNormalMeasure r m S) = univ := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
  refine integrable_exp_mul_of_mem_Icc
    (a := -(∑ i, |θ i|)) (b := ∑ i, |θ i|) (by fun_prop) ?_
  filter_upwards [ae_mem_simplex_logisticNormalMeasure r m S] with x hx
  apply abs_le.mp
  calc
    |⟪θ, x⟫| = |∑ i, θ i * x i| := by
      simp [PiLp.inner_apply, mul_comm]
    _ ≤ ∑ i, |θ i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |θ i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_pos (hx.1 i)]
      exact mul_le_of_le_one_right (abs_nonneg _) (hx.2 ▸
        Finset.single_le_sum (fun j _ ↦ (hx.1 j).le) (Finset.mem_univ i))

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    {P : Measure Ω} {r : ι} {m : EuclideanSpace ℝ {i // i ≠ r}}
    {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ} {X : Ω → EuclideanSpace ℝ ι}

/-- A variable with simplex logistic-normal law has every natural mixed moment integrable. -/
theorem integrable_prod_pow_logisticNormalMeasure
    (hX : HasLaw X (TauCeti.Probability.logisticNormalMeasure r m S) P) (k : ι → ℕ) :
    Integrable (fun ω ↦ ∏ i, X ω i ^ k i) P :=
  hX.integrable_fun_comp (TauCeti.Probability.integrable_prod_pow_logisticNormalMeasure r m S k)

/-- Mixed moments of a logistic-normal variable are Gaussian chart integrals. -/
theorem integral_prod_pow_logisticNormalMeasure
    (hX : HasLaw X (TauCeti.Probability.logisticNormalMeasure r m S) P) (k : ι → ℕ) :
    ∫ ω, ∏ i, X ω i ^ k i ∂P =
      ∫ z, ∏ i, TauCeti.Probability.logisticNormalChart r z i ^ k i ∂multivariateGaussian m S := by
  rw [← Function.comp_def (f := fun x : EuclideanSpace ℝ ι ↦ ∏ i, x i ^ k i),
    hX.integral_comp (by fun_prop),
    TauCeti.Probability.integral_prod_pow_logisticNormalMeasure]

end ProbabilityTheory.HasLaw
