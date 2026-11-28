/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Nonarchimedean evaluation of integral homogeneous polynomials

`IsNonarchimedean.eval_mvPolynomial_le_pow_of_coeff_le_one` bounds the evaluation of
an integral homogeneous polynomial by the degree power of the largest coordinate
absolute value. It uses `IsNonarchimedean.apply_sum_le_sup` and homogeneity to bound
the monomials, as in Baker and Rumely, *Equidistribution of small points, rational dynamics,
and potential theory*, Remark 3.3.
-/

public section

open MvPolynomial

/-- At a nonarchimedean absolute value, a homogeneous polynomial with integral coefficients
has absolute value at most the degree power of the largest coordinate absolute value. -/
theorem IsNonarchimedean.eval_mvPolynomial_le_pow_of_coeff_le_one {K ι : Type*}
    [CommSemiring K] [Finite ι] {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {P : MvPolynomial ι K} {d : ℕ} (hP : P.IsHomogeneous d)
    (hc : ∀ s, v (P.coeff s) ≤ 1) (x : ι → K) :
    v (P.eval x) ≤ (⨆ i, v (x i)) ^ d := by
  rcases eq_or_ne P 0 with rfl | hne
  · rw [map_zero, v.map_zero]
    exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass v _) _
  have hs := support_nonempty.mpr hne
  obtain ⟨s, hs'⟩ := support_nonempty.mpr hne
  have : Nontrivial K := nontrivial_of_ne _ _ (mem_support_iff.mp hs')
  rw [eval_eq]
  refine (hv.apply_sum_le_sup hs).trans (Finset.sup'_le hs _ fun t ht ↦ ?_)
  simp only [map_mul, map_prod, map_pow]
  calc
    _ ≤ 1 * ∏ i ∈ t.support, (⨆ j, v (x j)) ^ t i := by
      refine mul_le_mul (hc t) ?_
        (Finset.prod_nonneg fun i _ ↦ pow_nonneg (v.nonneg _) _) zero_le_one
      gcongr with i
      exact le_ciSup (Set.finite_range (fun j ↦ v (x j))).bddAbove i
    _ = _ := by rw [one_mul, Finset.prod_pow_eq_pow_sum, ← hP.degree_eq_sum_deg_support ht]
