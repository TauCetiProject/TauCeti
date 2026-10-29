/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import TauCeti.Analysis.Polynomial.SupNorm.Basic
public import TauCeti.Data.Nat.Choose.Central

/-!
# The Gelfond bound for polynomial factors

For complex polynomials with product of degree `d`, the product of the coefficient
sup norms is at most `2 ^ d` times the sup norm of the product. Together with the
reverse bound in `SupNorm.Basic`, this controls coefficient heights under factorization.
Zero factors and empty products are included.

The Gelfond bound combines Mathlib's coefficient-to-Mahler and Landau estimates
with supermultiplicativity and the square-root bound for middle binomial coefficients.

## References

* Xiaorun Wu, *Diophantine geometry, week 08: arithmetic heights* (2023), Lemmas 3.5–3.6.
* Lukas Pottmeyer, *Diophantine Approximation* (2022), Lemma 3.2.10.
-/

public section

open Polynomial

namespace TauCeti

/-- The Gelfond factor bound: the product of the coefficient sup norms of complex
polynomials is at most `2^d` times the sup norm of their degree-`d` product. -/
theorem _root_.Polynomial.prod_supNorm_le_two_pow_mul_supNorm_prod
    {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    ∏ i ∈ s, (f i).supNorm ≤
      2 ^ (∏ i ∈ s, f i).natDegree * (∏ i ∈ s, f i).supNorm := by
  classical
  by_cases hz : ∃ i ∈ s, f i = 0
  · obtain ⟨i, hi, hzero⟩ := hz
    have hp : ∏ i ∈ s, f i = 0 := Finset.prod_eq_zero hi hzero
    have hn : ∏ i ∈ s, (f i).supNorm = 0 :=
      Finset.prod_eq_zero hi (by simp [hzero])
    simp [hp, hn]
  · have hne : ∀ i ∈ s, f i ≠ 0 := by simpa using hz
    have hdegree := Polynomial.natDegree_prod s f hne
    have hmahler : (∏ i ∈ s, f i).mahlerMeasure = ∏ i ∈ s, (f i).mahlerMeasure := by
      simpa only [Finset.prod, Multiset.map_map, Function.comp_def] using
        Polynomial.prod_mahlerMeasure_eq_mahlerMeasure_prod (s.val.map f)
    calc
      ∏ i ∈ s, (f i).supNorm ≤
          ∏ i ∈ s, ((f i).natDegree.choose ((f i).natDegree / 2) : ℝ) *
            (f i).mahlerMeasure := by
        exact Finset.prod_le_prod₀ (fun i _ ↦ (f i).supNorm_nonneg)
          (fun i _ ↦ (f i).supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure)
      _ = (∏ i ∈ s, ((f i).natDegree.choose ((f i).natDegree / 2) : ℝ)) *
          (∏ i ∈ s, f i).mahlerMeasure := by rw [Finset.prod_mul_distrib, hmahler]
      _ ≤ ((∏ i ∈ s, f i).natDegree.choose ((∏ i ∈ s, f i).natDegree / 2) : ℝ) *
          (∏ i ∈ s, f i).mahlerMeasure := by
        refine mul_le_mul_of_nonneg_right ?_ (Polynomial.mahlerMeasure_nonneg _)
        rw [hdegree]
        exact_mod_cast Nat.prod_choose_middle_le_choose_sum_middle s (fun i ↦ (f i).natDegree)
      _ ≤ ((∏ i ∈ s, f i).natDegree.choose ((∏ i ∈ s, f i).natDegree / 2) : ℝ) *
          (Real.sqrt ((∏ i ∈ s, f i).natDegree + 1) * (∏ i ∈ s, f i).supNorm) := by
        exact mul_le_mul_of_nonneg_left
          (Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _) (Nat.cast_nonneg _)
      _ ≤ 2 ^ (∏ i ∈ s, f i).natDegree * (∏ i ∈ s, f i).supNorm := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (Nat.choose_middle_mul_sqrt_le_two_pow _)
          (Polynomial.supNorm_nonneg _)

end TauCeti
