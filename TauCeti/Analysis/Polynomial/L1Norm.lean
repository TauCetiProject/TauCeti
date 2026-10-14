/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# The coefficient l¹-norm of a polynomial

This file defines the coefficient l¹-norm (also called the coefficient length) of a
polynomial and develops its basic estimates. In particular, it is subadditive and
submultiplicative, controls evaluation, and behaves predictably under translation and Hasse
differentiation. These bounds are useful when constructing auxiliary polynomials with controlled
coefficients.

## Main definitions

* `Polynomial.l1Norm`: the sum of the norms of the nonzero coefficients.

## Main results

* `Polynomial.l1Norm_add_le` and `Polynomial.l1Norm_mul_le`: the triangle and product bounds.
* `Polynomial.norm_eval_le_l1Norm_mul`: the evaluation bound.
* `Polynomial.l1Norm_comp_X_add_C_le`: the translation bound.
* `Polynomial.l1Norm_hasseDeriv_le`: the Hasse derivative bound.

## References

* J.-H. Evertse, *Diophantine Approximation*, Chapter 6, Section 6.2.
-/

public section

namespace Polynomial

variable {R : Type*} [SeminormedRing R]

/-- The coefficient l¹-norm of a polynomial, namely the sum of the norms of its nonzero
coefficients. This is also called the coefficient length. -/
noncomputable def l1Norm (P : R[X]) : ℝ := P.sum fun _ a ↦ ‖a‖

/-- The coefficient l¹-norm is the sum over the support. -/
theorem l1Norm_eq_sum_support (P : R[X]) :
    P.l1Norm = ∑ i ∈ P.support, ‖P.coeff i‖ := by
  rw [l1Norm, sum_def]

/-- The coefficient l¹-norm is the sum through the natural degree. -/
theorem l1Norm_eq_sum_range (P : R[X]) :
    P.l1Norm = ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ := by
  rw [l1Norm, sum_eq_of_subset]
  · exact fun _ ↦ norm_zero
  · intro i hi
    exact Finset.mem_range.2 (Nat.lt_succ_iff.2 (le_natDegree_of_mem_supp i hi))

/-- The zero polynomial has coefficient l¹-norm zero. -/
@[simp]
theorem l1Norm_zero : (0 : R[X]).l1Norm = 0 := by
  simp [l1Norm]

/-- The coefficient l¹-norm is nonnegative. -/
theorem l1Norm_nonneg (P : R[X]) : 0 ≤ P.l1Norm := by
  simp only [l1Norm_eq_sum_support]
  positivity

/-- The coefficient l¹-norm of a constant polynomial is the norm of its value. -/
@[simp]
theorem l1Norm_C (a : R) : (C a).l1Norm = ‖a‖ := by
  simp [l1Norm]

/-- The coefficient l¹-norm of a monomial is the norm of its coefficient. -/
@[simp]
theorem l1Norm_monomial (n : ℕ) (a : R) : (monomial n a).l1Norm = ‖a‖ := by
  simp [l1Norm]

/-- The unit polynomial has coefficient l¹-norm one when the coefficient norm preserves one. -/
@[simp]
theorem l1Norm_one [NormOneClass R] : (1 : R[X]).l1Norm = 1 := by
  rw [show (1 : R[X]) = C 1 by simp, l1Norm_C, norm_one]

/-- The polynomial `X` has coefficient l¹-norm one when the coefficient norm preserves one. -/
@[simp]
theorem l1Norm_X [NormOneClass R] : (X : R[X]).l1Norm = 1 := by
  rw [← monomial_one_one_eq_X, l1Norm_monomial, norm_one]

/-- Negating a polynomial does not change its coefficient l¹-norm. -/
@[simp]
theorem l1Norm_neg (P : R[X]) : (-P).l1Norm = P.l1Norm := by
  simp only [l1Norm_eq_sum_range, natDegree_neg, coeff_neg, norm_neg]

/-- The norm of each coefficient is at most the coefficient l¹-norm. -/
theorem norm_coeff_le_l1Norm (P : R[X]) (i : ℕ) : ‖P.coeff i‖ ≤ P.l1Norm := by
  rw [l1Norm_eq_sum_support]
  by_cases hi : i ∈ P.support
  · exact Finset.single_le_sum (fun j _ ↦ norm_nonneg (P.coeff j)) hi
  · rw [notMem_support_iff.mp hi, norm_zero]
    exact P.l1Norm_nonneg

/-- The coefficient sup norm is at most the coefficient l¹-norm. -/
theorem supNorm_le_l1Norm (P : R[X]) : P.supNorm ≤ P.l1Norm := by
  obtain ⟨i, hi⟩ := P.exists_eq_supNorm
  rw [hi]
  exact P.norm_coeff_le_l1Norm i

/-- The coefficient l¹-norm is at most the number of possible coefficients times the sup norm. -/
theorem l1Norm_le_natDegree_add_one_mul_supNorm (P : R[X]) :
    P.l1Norm ≤ (P.natDegree + 1) * P.supNorm := by
  rw [l1Norm_eq_sum_range]
  calc
    ∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖ ≤
        ∑ _i ∈ Finset.range (P.natDegree + 1), P.supNorm :=
      Finset.sum_le_sum fun i _ ↦ P.le_supNorm i
    _ = (P.natDegree + 1) * P.supNorm := by simp

/-- Over a normed ring, the coefficient l¹-norm vanishes exactly for the zero polynomial. -/
theorem l1Norm_eq_zero_iff {A : Type*} [NormedRing A] (P : A[X]) : P.l1Norm = 0 ↔ P = 0 := by
  constructor
  · intro hP
    exact ext fun i ↦ norm_eq_zero.mp <|
      le_antisymm (hP ▸ P.norm_coeff_le_l1Norm i) (norm_nonneg _)
  · rintro rfl
    exact l1Norm_zero

/-- The coefficient l¹-norm satisfies the triangle inequality. -/
theorem l1Norm_add_le (P Q : R[X]) : (P + Q).l1Norm ≤ P.l1Norm + Q.l1Norm := by
  classical
  let s := P.support ∪ Q.support
  have hadd : (P + Q).l1Norm = ∑ i ∈ s, ‖(P + Q).coeff i‖ := by
    rw [l1Norm, sum_eq_of_subset]
    · exact fun _ ↦ norm_zero
    · exact support_add
  have hP : P.l1Norm = ∑ i ∈ s, ‖P.coeff i‖ := by
    rw [l1Norm, sum_eq_of_subset]
    · exact fun _ ↦ norm_zero
    · exact Finset.subset_union_left
  have hQ : Q.l1Norm = ∑ i ∈ s, ‖Q.coeff i‖ := by
    rw [l1Norm, sum_eq_of_subset]
    · exact fun _ ↦ norm_zero
    · exact Finset.subset_union_right
  rw [hadd, hP, hQ, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ by
    simpa only [coeff_add] using norm_add_le (P.coeff i) (Q.coeff i)

/-- The coefficient l¹-norm of a finite sum is at most the sum of the coefficient l¹-norms. -/
theorem l1Norm_sum_le {S : Type*} (s : Finset S) (P : S → R[X]) :
    (∑ i ∈ s, P i).l1Norm ≤ ∑ i ∈ s, (P i).l1Norm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (l1Norm_add_le _ _).trans <| by
        simpa only [add_comm] using add_le_add_right ih (P a).l1Norm

/-- The coefficient l¹-norm is submultiplicative. -/
theorem l1Norm_mul_le (P Q : R[X]) : (P * Q).l1Norm ≤ P.l1Norm * Q.l1Norm := by
  classical
  rw [mul_eq_sum_sum]
  calc
    (∑ i ∈ P.support, Q.sum fun j a ↦ monomial (i + j) (P.coeff i * a)).l1Norm
        ≤ ∑ i ∈ P.support, (Q.sum fun j a ↦ monomial (i + j) (P.coeff i * a)).l1Norm :=
      l1Norm_sum_le P.support _
    _ ≤ ∑ i ∈ P.support, ‖P.coeff i‖ * Q.l1Norm := by
      gcongr with i hi
      rw [sum_def]
      calc
        (∑ j ∈ Q.support, monomial (i + j) (P.coeff i * Q.coeff j)).l1Norm
            ≤ ∑ j ∈ Q.support,
                (monomial (i + j) (P.coeff i * Q.coeff j)).l1Norm :=
          l1Norm_sum_le Q.support _
        _ ≤ ∑ j ∈ Q.support, ‖P.coeff i‖ * ‖Q.coeff j‖ := by
          gcongr with j hj
          simpa only [l1Norm_monomial] using norm_mul_le (P.coeff i) (Q.coeff j)
        _ = ‖P.coeff i‖ * Q.l1Norm := by
          rw [l1Norm_eq_sum_support, Finset.mul_sum]
    _ = P.l1Norm * Q.l1Norm := by
      simp only [l1Norm_eq_sum_support, Finset.sum_mul]

/-- Evaluation is controlled by coefficient length and the largest power of the evaluation
point permitted by the degree. -/
theorem norm_eval_le_l1Norm_mul [NormOneClass R] (P : R[X]) (z : R) :
    ‖P.eval z‖ ≤ P.l1Norm * max 1 ‖z‖ ^ P.natDegree := by
  rw [eval_eq_sum]
  calc
    ‖P.sum fun i a ↦ a * z ^ i‖ ≤ P.sum fun i a ↦ ‖a * z ^ i‖ := by
      rw [sum_def]
      exact norm_sum_le _ _
    _ ≤ P.sum fun _i a ↦ ‖a‖ * max 1 ‖z‖ ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ‖P.coeff i * z ^ i‖ ≤ ‖P.coeff i‖ * ‖z ^ i‖ := norm_mul_le _ _
        _ ≤ ‖P.coeff i‖ * ‖z‖ ^ i :=
          mul_le_mul_of_nonneg_left (norm_pow_le z i) (norm_nonneg _)
        _ ≤ ‖P.coeff i‖ * max 1 ‖z‖ ^ P.natDegree := by
          gcongr
          calc
            ‖z‖ ^ i ≤ max 1 ‖z‖ ^ i :=
              pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) i
            _ ≤ max 1 ‖z‖ ^ P.natDegree :=
              pow_le_pow_right₀ (le_max_left 1 ‖z‖) (le_natDegree_of_mem_supp i hi)
    _ = P.l1Norm * max 1 ‖z‖ ^ P.natDegree := by
      rw [sum_def, l1Norm_eq_sum_support, Finset.sum_mul]

/-- Taking a power raises the coefficient l¹-norm by at most the same power. -/
theorem l1Norm_pow_le [NormOneClass R] (P : R[X]) (n : ℕ) :
    (P ^ n).l1Norm ≤ P.l1Norm ^ n := by
  induction n with
  | zero => simp only [pow_zero, l1Norm_one, le_refl]
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (l1Norm_mul_le _ _).trans
        (mul_le_mul ih le_rfl P.l1Norm_nonneg (pow_nonneg P.l1Norm_nonneg n))

/-- Translating a polynomial multiplies its coefficient l¹-norm by at most the indicated
degree factor. -/
theorem l1Norm_comp_X_add_C_le [NormOneClass R] (P : R[X]) (a : R) :
    (P.comp (X + C a)).l1Norm ≤ P.l1Norm * (1 + ‖a‖) ^ P.natDegree := by
  rw [comp_eq_sum_left, sum_def]
  calc
    (∑ i ∈ P.support, C (P.coeff i) * (X + C a) ^ i).l1Norm ≤
        ∑ i ∈ P.support, (C (P.coeff i) * (X + C a) ^ i).l1Norm :=
      l1Norm_sum_le P.support _
    _ ≤ ∑ i ∈ P.support, ‖P.coeff i‖ * (1 + ‖a‖) ^ i := by
      gcongr with i hi
      calc
        (C (P.coeff i) * (X + C a) ^ i).l1Norm ≤
            (C (P.coeff i)).l1Norm * ((X + C a) ^ i).l1Norm := l1Norm_mul_le _ _
        _ ≤ ‖P.coeff i‖ * (1 + ‖a‖) ^ i := by
          rw [l1Norm_C]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          have hbase : (X + C a : R[X]).l1Norm ≤ 1 + ‖a‖ := by
            calc
              (X + C a : R[X]).l1Norm ≤ (X : R[X]).l1Norm + (C a).l1Norm :=
                l1Norm_add_le _ _
              _ = 1 + ‖a‖ := by rw [l1Norm_X, l1Norm_C]
          calc
            ((X + C a) ^ i : R[X]).l1Norm ≤ (X + C a : R[X]).l1Norm ^ i :=
              l1Norm_pow_le _ i
            _ ≤ (1 + ‖a‖) ^ i :=
              pow_le_pow_left₀ (l1Norm_nonneg (X + C a : R[X])) hbase i
    _ ≤ ∑ i ∈ P.support, ‖P.coeff i‖ * (1 + ‖a‖) ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact pow_le_pow_right₀ (a := (1 + ‖a‖ : ℝ)) (by simp)
        (le_natDegree_of_mem_supp i hi)
    _ = P.l1Norm * (1 + ‖a‖) ^ P.natDegree := by
      simp only [l1Norm_eq_sum_support, Finset.sum_mul]

/-- A Hasse derivative increases coefficient length by at most `2 ^ natDegree`. -/
theorem l1Norm_hasseDeriv_le [NormOneClass R] (P : R[X]) (k : ℕ) :
    (hasseDeriv k P).l1Norm ≤ 2 ^ P.natDegree * P.l1Norm := by
  rw [hasseDeriv_apply]
  calc
    (P.sum fun i r ↦ monomial (i - k) ((i.choose k : R) * r)).l1Norm ≤
        P.sum fun i r ↦ (monomial (i - k) ((i.choose k : R) * r)).l1Norm := by
      rw [sum_def]
      exact l1Norm_sum_le P.support _
    _ ≤ P.sum fun _i r ↦ 2 ^ P.natDegree * ‖r‖ := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [l1Norm_monomial]
      calc
        ‖(i.choose k : R) * P.coeff i‖ ≤ ‖(i.choose k : R)‖ * ‖P.coeff i‖ :=
          norm_mul_le _ _
        _ ≤ (i.choose k : ℝ) * ‖P.coeff i‖ := by
          gcongr
          simpa only [norm_one, mul_one] using (Nat.norm_cast_le (α := R) (i.choose k))
        _ ≤ (2 : ℝ) ^ P.natDegree * ‖P.coeff i‖ := by
          gcongr
          exact_mod_cast (Nat.choose_le_two_pow i k).trans
            (Nat.pow_le_pow_right (by omega) (le_natDegree_of_mem_supp i hi))
    _ = 2 ^ P.natDegree * P.l1Norm := by
      rw [sum_def, l1Norm_eq_sum_support, Finset.mul_sum]

end Polynomial
