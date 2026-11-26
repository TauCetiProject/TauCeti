/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Analysis.Matrix.Exponential.EuclideanCLM
public import TauCeti.Analysis.Normed.Algebra.MatrixExponential
public import TauCeti.Analysis.ODE.Propagator.Liouville
public import TauCeti.Examples.Analysis.ODE.Propagator.Basic
import TauCeti.Analysis.Normed.Algebra.NilpotentExponential
import Mathlib.Tactic.FinCases

/-!
# Checks for Liouville's formula

* **Diagonal coefficient.** For `P = diag(p₁, p₂)` on `Fin 2 → ℝ` with `p₁, p₂` integrable,
  `TauCeti.det_toMatrix'_propagator` gives `det N_P(t, s) = e^{∫_s^t (p₁ + p₂)}`
  (`TauCeti.Examples.Propagator.det_propagator_diagonal`).
* **The time-ordered example.** For the coefficient `P` equal to `A = [[0, 1], [0, 0]]` on
  `(-∞, 1)` and to `B = [[0, 0], [1, 0]]` on `[1, ∞)`, the propagator `N_P(2, 0) = [[1, 1], [1, 2]]`
  has determinant `1` (`TauCeti.Examples.Propagator.det_propagator_coeff_two_zero`), and Liouville's
  formula gives `e^{tr A + tr B} = e^0`
  (`TauCeti.Examples.Propagator.det_propagator_coeff_two_zero_eq_exp`).
* **Constant coefficients.** For a constant coefficient `A`, `N_A(t, s) = exp ((t - s) A)`, and
  both Liouville's formula `det N_A(t, s) = e^{∫_s^t tr A}` and `Matrix.det_exp` at `(t - s) A`
  give `det N_A(t, s) = e^{(t - s) tr A}`
  (`TauCeti.Examples.Propagator.det_propagator_const_eq_det_exp`). For `A = [[1, 1], [0, 1]]`,
  `exp (t A) = e^t [[1, t], [0, 1]]` (`TauCeti.Examples.Propagator.exp_smul_jordan`) has
  determinant `e^{2t} = e^{t tr A}` (`TauCeti.Examples.Propagator.det_propagator_jordan`), while
  the sum of the entries (`e^{3t}`) or `det A` (`e^t`) in place of the trace gives a different value
  for `t ≠ 0` (`TauCeti.Examples.Propagator.det_propagator_jordan_ne`).
-/

public section

open MeasureTheory Set NormedSpace

namespace TauCeti.Examples.Propagator

/-- **Liouville's formula for a diagonal coefficient.** For `p₁, p₂` integrable on `[a, b]` and
`s, t ∈ [a, b]`, the propagator of `diag(p₁, p₂)` on `Fin 2 → ℝ` has determinant
`exp (∫ s..t, (p₁ + p₂))`. -/
theorem det_propagator_diagonal {p₁ p₂ : ℝ → ℝ} {a b s t : ℝ}
    (h₁ : IntegrableOn p₁ (Icc a b)) (h₂ : IntegrableOn p₂ (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    (LinearMap.toMatrix' (propagator (fun r ↦ LinearMap.toContinuousLinearMap
      (Matrix.toLin' !![p₁ r, 0; 0, p₂ r])) t s : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ)).det =
      Real.exp (∫ r in s..t, (p₁ r + p₂ r)) := by
  have hP : IntegrableOn (fun r ↦ LinearMap.toContinuousLinearMap
      (Matrix.toLin' !![p₁ r, 0; 0, p₂ r])) (Icc a b) := by
    have : (fun r ↦ LinearMap.toContinuousLinearMap (Matrix.toLin' !![p₁ r, 0; 0, p₂ r])) =
        fun r ↦ p₁ r • LinearMap.toContinuousLinearMap (Matrix.toLin' !![(1 : ℝ), 0; 0, 0]) +
          p₂ r • LinearMap.toContinuousLinearMap (Matrix.toLin' !![(0 : ℝ), 0; 0, 1]) := by
      funext r
      ext v i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [this]
    exact (h₁.smul_const _).add (h₂.smul_const _)
  rw [det_toMatrix'_propagator hP hs ht, ← Real.exp_eq_exp_ℝ]
  simp [LinearMap.toMatrix'_toLin', Matrix.trace_fin_two]

/-! ### The time-ordered example -/

/-- The coefficient of the time-ordered example is trace free: `tr A = tr B = 0`. -/
theorem trace_coeff (r : ℝ) :
    LinearMap.trace ℝ _
      (coeff r : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = 0 := by
  by_cases hr : r ∈ Iio 1
  · simp [coeff, indicator_of_mem hr, Matrix.trace_fin_two]
  · simp [coeff, indicator_of_notMem hr, Matrix.trace_fin_two]

/-- **The time-ordered example, computed.** `det N_P(2, 0) = det [[1, 1], [1, 2]] = 1`. -/
theorem det_propagator_coeff_two_zero :
    LinearMap.det (propagator coeff 2 0 :
      EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = 1 := by
  rw [← ContinuousLinearMap.det, propagator_coeff_two_zero, Matrix.det_toEuclideanCLM,
    Matrix.det_fin_two_of]
  norm_num

/-- **The time-ordered example, by Liouville's formula.** `det N_P(2, 0) = e^{tr A + tr B}`, and
`tr A + tr B = 0`. -/
theorem det_propagator_coeff_two_zero_eq_exp :
    LinearMap.det (propagator coeff 2 0 :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) =
      Real.exp (LinearMap.trace ℝ _ (opA : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) +
        LinearMap.trace ℝ _ (opB : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _)) ∧
    LinearMap.trace ℝ _ (opA : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) +
        LinearMap.trace ℝ _ (opB : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) = 0 := by
  have h : LinearMap.trace ℝ _ (opA : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) +
      LinearMap.trace ℝ _ (opB : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) = 0 := by
    simp [Matrix.trace_fin_two]
  refine ⟨?_, h⟩
  rw [det_propagator integrableOn_coeff ⟨le_rfl, zero_le_two⟩ ⟨zero_le_two, le_rfl⟩, h]
  simp only [trace_coeff, intervalIntegral.integral_zero, exp_zero, Real.exp_zero]

/-! ### Constant coefficients -/

/-- A constant matrix coefficient `A` has propagator the operator of `exp ((t - s) A)`. -/
private theorem propagator_const_toEuclideanCLM {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t s : ℝ) :
    propagator (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) A) t s =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (exp ((t - s) • A)) := by
  simp only [propagator_const, RCLike.ofReal_real_eq_id, id_eq, map_smul,
    Matrix.toEuclideanCLM_exp]

/-- **Constant coefficients agree with `Matrix.det_exp`.** For a constant coefficient `A`,
Liouville's formula gives `det N_A(t, s) = e^{∫_s^t tr A}`, while
`N_A(t, s) = exp ((t - s) A)` (`TauCeti.propagator_const`) gives
`det N_A(t, s) = det (exp ((t - s) A))`, which is `e^{(t - s) tr A}` by `Matrix.det_exp`. -/
theorem det_propagator_const_eq_det_exp {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (t s : ℝ) :
    LinearMap.det (propagator (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) A) t s :
        EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) =
      exp (∫ _ in s..t, LinearMap.trace ℝ _
        (Matrix.toEuclideanCLM (𝕜 := ℝ) A : EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n)) ∧
    LinearMap.det (propagator (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) A) t s :
        EuclideanSpace ℝ n →ₗ[ℝ] EuclideanSpace ℝ n) = (exp ((t - s) • A)).det ∧
    (exp ((t - s) • A)).det = Real.exp ((t - s) * A.trace) := by
  refine ⟨det_propagator (a := min s t) (b := max s t) continuousOn_const.integrableOn_Icc
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩, ?_, ?_⟩
  · rw [propagator_const_toEuclideanCLM, ← ContinuousLinearMap.det, Matrix.det_toEuclideanCLM]
  · rw [Matrix.det_exp, Matrix.trace_smul, smul_eq_mul, Real.exp_eq_exp_ℝ]

/-- The matrix `[[1, 1], [0, 1]]`. -/
abbrev jordan : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- **The exponential of `t [[1, 1], [0, 1]]`** is `e^t [[1, t], [0, 1]]`. -/
theorem exp_smul_jordan (t : ℝ) : exp (t • jordan) = Real.exp t • !![1, t; 0, 1] := by
  have hsplit : t • jordan = t • (1 : Matrix (Fin 2) (Fin 2) ℝ) + !![0, t; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hsq : (!![0, t; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq]
  rw [hsplit, Matrix.exp_add_of_commute _ _ ((Commute.one_left _).smul_left t),
    Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal]
  rw [exp_eq_one_add_of_sq_eq_zero ℝ hsq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Real.exp_eq_exp_ℝ]

/-- **Liouville's formula for `A = [[1, 1], [0, 1]]`.** `N_A(t, 0) = e^t [[1, t], [0, 1]]`, and
`det N_A(t, 0) = e^{2t} = e^{t tr A}`. -/
theorem det_propagator_jordan (t : ℝ) :
    propagator (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) jordan) t 0 =
        Matrix.toEuclideanCLM (𝕜 := ℝ) (Real.exp t • !![1, t; 0, 1]) ∧
      LinearMap.det (propagator (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) jordan) t 0 :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) = Real.exp (2 * t) ∧
      Real.exp (2 * t) = Real.exp (t * jordan.trace) := by
  have hN : propagator (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) jordan) t 0 =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (Real.exp t • !![1, t; 0, 1]) := by
    rw [propagator_const_toEuclideanCLM, sub_zero, exp_smul_jordan]
  refine ⟨hN, ?_, by rw [Matrix.trace_fin_two_of]; ring_nf⟩
  rw [← ContinuousLinearMap.det, hN, Matrix.det_toEuclideanCLM]
  simp [Matrix.det_fin_two_of, ← Real.exp_add, two_mul]

/-- **The trace is the right invariant.** For `t ≠ 0`, `det N_A(t, 0) = e^{2t}` differs from
`e^{3t}`, where `3` is the sum of the entries of `A = [[1, 1], [0, 1]]`, and from `e^t`, where
`1 = det A`. -/
theorem det_propagator_jordan_ne {t : ℝ} (ht : t ≠ 0) :
    LinearMap.det (propagator (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) jordan) t 0 :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ≠
        Real.exp (t * ∑ i, ∑ j, jordan i j) ∧
      LinearMap.det (propagator (fun _ ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) jordan) t 0 :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ≠
        Real.exp (t * jordan.det) := by
  have hsum : ∑ i, ∑ j, jordan i j = 3 := by norm_num [Fin.sum_univ_two]
  have hdet : jordan.det = 1 := by simp [Matrix.det_fin_two_of]
  rw [(det_propagator_jordan t).2.1, hsum, hdet]
  simp only [Ne, Real.exp_eq_exp]
  constructor <;> intro h <;> apply ht <;> linarith

end TauCeti.Examples.Propagator
