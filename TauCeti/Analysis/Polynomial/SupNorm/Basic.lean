/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Coefficient sup norms of polynomial products

A coefficient of a finite product is bounded by its binomial weight in the sum of
the degrees times the product of the coefficient sup norms. Consequently the sup
norm of the product is bounded by the middle binomial coefficient. Over a domain
this gives a factor of at most `2 ^ d`, where `d` is the degree of the product.

These estimates control growth of coefficients under polynomial multiplication.
They include zero factors and empty products, and use Mathlib's `Polynomial.supNorm`.

## References

* Xiaorun Wu, *Diophantine geometry, week 08: arithmetic heights* (2023), Lemma 3.6.
-/

public section

open Polynomial

namespace TauCeti

/-- A coefficient is bounded by its binomial weight times the coefficient sup norm. -/
theorem _root_.Polynomial.norm_coeff_le_choose_mul_supNorm {A : Type*} [SeminormedRing A]
    (p : A[X]) (k : ℕ) :
    ‖p.coeff k‖ ≤ (p.natDegree.choose k : ℝ) * p.supNorm := by
  by_cases hk : k ≤ p.natDegree
  · exact (p.le_supNorm k).trans (le_mul_of_one_le_left p.supNorm_nonneg
      (by exact_mod_cast Nat.choose_pos hk))
  · simp [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < k),
      Nat.choose_eq_zero_of_lt (by omega : p.natDegree < k)]

/-- Each coefficient of a finite product is bounded by a binomial coefficient of the
sum of the degrees times the product of the coefficient sup norms. -/
theorem _root_.Polynomial.norm_coeff_prod_le_choose_mul_prod_supNorm
    {A ι : Type*} [SeminormedCommRing A] [NormOneClass A]
    (s : Finset ι) (f : ι → A[X]) (k : ℕ) :
    ‖(∏ i ∈ s, f i).coeff k‖ ≤
      ((∑ i ∈ s, (f i).natDegree).choose k : ℝ) * ∏ i ∈ s, (f i).supNorm := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => cases k <;> simp [Polynomial.coeff_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Polynomial.coeff_mul, Finset.sum_insert hi,
      Finset.prod_insert hi, Nat.add_choose_eq, Nat.cast_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ij _ ↦ ?_)
    calc
      ‖(f i).coeff ij.1 * (∏ j ∈ s, f j).coeff ij.2‖ ≤
          ‖(f i).coeff ij.1‖ * ‖(∏ j ∈ s, f j).coeff ij.2‖ := norm_mul_le _ _
      _ ≤ ((f i).natDegree.choose ij.1 : ℝ) * (f i).supNorm *
          (((∑ j ∈ s, (f j).natDegree).choose ij.2 : ℝ) *
            ∏ j ∈ s, (f j).supNorm) := by
        exact mul_le_mul (Polynomial.norm_coeff_le_choose_mul_supNorm _ _) (ih _)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (f i).supNorm_nonneg)
      _ = _ := by push_cast; ring

/-- The coefficient sup norm of a finite product is at most the largest binomial
coefficient of the sum of the degrees times the product of the sup norms. -/
theorem _root_.Polynomial.supNorm_prod_le_choose_mul_prod_supNorm
    {A ι : Type*} [SeminormedCommRing A] [NormOneClass A]
    (s : Finset ι) (f : ι → A[X]) :
    (∏ i ∈ s, f i).supNorm ≤
      ((∑ i ∈ s, (f i).natDegree).choose ((∑ i ∈ s, (f i).natDegree) / 2) : ℝ) *
        ∏ i ∈ s, (f i).supNorm := by
  obtain ⟨k, hk⟩ := (∏ i ∈ s, f i).exists_eq_supNorm
  rw [hk]
  refine (Polynomial.norm_coeff_prod_le_choose_mul_prod_supNorm s f k).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ ↦ (f i).supNorm_nonneg)
  exact_mod_cast Nat.choose_le_middle k (∑ i ∈ s, (f i).natDegree)

/-- The coefficient sup norm of a product of polynomials over a seminormed
commutative domain is at most `2^d` times the product of the coefficient sup norms,
where `d` is the degree of the product. -/
theorem _root_.Polynomial.supNorm_prod_le_two_pow_mul_prod_supNorm
    {A ι : Type*} [SeminormedCommRing A] [NormOneClass A] [IsDomain A]
    (s : Finset ι) (f : ι → A[X]) :
    (∏ i ∈ s, f i).supNorm ≤
      2 ^ (∏ i ∈ s, f i).natDegree * ∏ i ∈ s, (f i).supNorm := by
  classical
  by_cases hz : ∃ i ∈ s, f i = 0
  · obtain ⟨i, hi, hzero⟩ := hz
    have hp : ∏ i ∈ s, f i = 0 := Finset.prod_eq_zero hi hzero
    have hn : ∏ i ∈ s, (f i).supNorm = 0 :=
      Finset.prod_eq_zero hi (by simp [hzero])
    simp [hp, hn]
  · have hne : ∀ i ∈ s, f i ≠ 0 := by simpa using hz
    rw [Polynomial.natDegree_prod s f hne]
    refine (Polynomial.supNorm_prod_le_choose_mul_prod_supNorm s f).trans ?_
    refine mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg fun i _ ↦ (f i).supNorm_nonneg)
    exact_mod_cast Nat.choose_le_two_pow _ _

end TauCeti
