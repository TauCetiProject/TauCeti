/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Monovary
import Mathlib.Tactic

/-!
# Weighted Chebyshev inequalities

For nonnegative weights, similarly ordered real vectors have nonnegative weighted covariance;
oppositely ordered vectors have nonpositive weighted covariance. With positive weights,
equality in the similarly ordered case holds exactly when one of the vectors is constant.

The proofs use the double-sum identity for weighted covariance.

## References

Hardy, Littlewood and Pólya, *Inequalities*, Theorem 43;
Bullen, *Handbook of Means and Their Inequalities*, Chapter II, §5.3, Theorem 4.
-/

public section

open Finset

variable {ι R : Type*}

namespace Finset

/-- The double-sum identity for weighted covariance, without normalization of the weights. -/
theorem sum_weight_mul_sub_mul_sub [CommRing R] (s : Finset ι) (w a b : ι → R) :
    (∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i - a j) * (b i - b j)) =
      2 * ((∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) -
        (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i)) := by
  have heq (i j : ι) :
      w i * w j * (a i - a j) * (b i - b j) =
        (w i * a i * b i) * w j - (w i * a i) * (w j * b j) -
          (w i * b i) * (w j * a j) + w i * (w j * a j * b j) := by ring
  simp_rw [heq, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
  ring

end Finset

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

namespace MonovaryOn

/-- Weighted Chebyshev inequality on a finite set, with arbitrary nonnegative total weight. -/
theorem sum_mul_sum_le_sum_mul_sum {s : Finset ι} {w a b : ι → R}
    (hab : MonovaryOn a b s) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) := by
  have h : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i - a j) * (b i - b j) := by
    apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    have hd := (monovaryOn_iff_forall_mul_nonneg.mp hab) hj hi
    exact mul_nonneg (mul_nonneg (hw i hi) (hw j hj)) hd |>.trans_eq (by ring)
  rw [sum_weight_mul_sub_mul_sub] at h
  linarith

omit [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] in
private theorem constant_on_of_pairwise_or {s : Finset ι} {a b : ι → R}
    (h : ∀ i ∈ s, ∀ j ∈ s, a i = a j ∨ b i = b j) :
    (∀ i ∈ s, ∀ j ∈ s, a i = a j) ∨ (∀ i ∈ s, ∀ j ∈ s, b i = b j) := by
  classical
  by_cases ha : ∀ i ∈ s, ∀ j ∈ s, a i = a j
  · exact Or.inl ha
  push Not at ha
  obtain ⟨i, hi, j, hj, hij⟩ := ha
  have hbij := (h i hi j hj).resolve_left hij
  have hb (k : ι) (hk : k ∈ s) : b k = b i := by
    rcases h i hi k hk with hik | hik
    · have hjk : a j ≠ a k := fun hjk ↦ hij (hik.trans hjk.symm)
      exact ((h j hj k hk).resolve_left hjk).symm.trans hbij.symm
    · exact hik.symm
  exact Or.inr fun k hk l hl ↦ (hb k hk).trans (hb l hl).symm

/-- With positive weights, equality in weighted Chebyshev holds exactly when one vector
is constant on the finite set. Empty sets are allowed. -/
theorem sum_mul_sum_eq_sum_mul_sum_iff {s : Finset ι} {w a b : ι → R}
    (hab : MonovaryOn a b s) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i * a i) * (∑ i ∈ s, w i * b i) =
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * a i * b i) ↔
      (∀ i ∈ s, ∀ j ∈ s, a i = a j) ∨ (∀ i ∈ s, ∀ j ∈ s, b i = b j) := by
  have hnonneg (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      0 ≤ w i * w j * (a i - a j) * (b i - b j) := by
    have hd := (monovaryOn_iff_forall_mul_nonneg.mp hab) hj hi
    nlinarith only [mul_nonneg (mul_pos (hw i hi) (hw j hj)).le hd]
  constructor
  · intro heq
    have hsum : (∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i - a j) * (b i - b j)) = 0 := by
      rw [sum_weight_mul_sub_mul_sub, ← heq, sub_self, mul_zero]
    apply constant_on_of_pairwise_or
    intro i hi j hj
    have hi0 := (sum_eq_zero_iff_of_nonneg (fun i hi ↦ sum_nonneg (hnonneg i hi))).mp hsum i hi
    have hij0 := (sum_eq_zero_iff_of_nonneg (hnonneg i hi)).mp hi0 j hj
    have hwi := (hw i hi).ne'
    have hwj := (hw j hj).ne'
    simpa only [mul_eq_zero, hwi, hwj, false_or, sub_eq_zero] using hij0
  · intro hconst
    have hsum : (∑ i ∈ s, ∑ j ∈ s, w i * w j * (a i - a j) * (b i - b j)) = 0 := by
      apply sum_eq_zero
      intro i hi
      apply sum_eq_zero
      intro j hj
      rcases hconst with ha | hb
      · simp [ha i hi j hj]
      · simp [hb i hi j hj]
    rw [sum_weight_mul_sub_mul_sub] at hsum
    linarith

end MonovaryOn

namespace TauCeti

variable [Fintype ι]

/-- Chebyshev's inequality for nonnegative weights of total mass one. -/
theorem sum_mul_sum_le_sum_mul_of_monovary {w a b : ι → R}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hab : Monovary a b) :
    (∑ i, w i * a i) * (∑ i, w i * b i) ≤ ∑ i, w i * (a i * b i) := by
  simpa only [hw1, one_mul, mul_assoc] using
    (hab.monovaryOn (↑(univ : Finset ι))).sum_mul_sum_le_sum_mul_sum (fun i _ ↦ hw i)

/-- The reversed weighted Chebyshev inequality for oppositely ordered vectors. -/
theorem sum_mul_le_sum_mul_sum_of_antivary {w a b : ι → R}
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hab : Antivary a b) :
    (∑ i, w i * (a i * b i)) ≤ (∑ i, w i * a i) * (∑ i, w i * b i) := by
  have h := sum_mul_sum_le_sum_mul_of_monovary hw hw1 (monovary_neg_right.mpr hab)
  simpa only [Pi.neg_apply, mul_neg, sum_neg_distrib, neg_le_neg_iff] using h

/-- For positive weights of total mass one, equality in Chebyshev's inequality is
equivalent to one of the vectors being constant. -/
theorem sum_mul_sum_eq_sum_mul_iff_of_monovary {w a b : ι → R}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hab : Monovary a b) :
    (∑ i, w i * a i) * (∑ i, w i * b i) = (∑ i, w i * (a i * b i)) ↔
      (∀ i j, a i = a j) ∨ (∀ i j, b i = b j) := by
  simpa only [hw1, one_mul, mul_assoc, mem_univ, forall_true_left] using
    (hab.monovaryOn (↑(univ : Finset ι))).sum_mul_sum_eq_sum_mul_sum_iff (fun i _ ↦ hw i)

/-- Equality in the reversed weighted Chebyshev inequality for positive normalized weights. -/
theorem sum_mul_eq_sum_mul_sum_iff_of_antivary {w a b : ι → R}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hab : Antivary a b) :
    (∑ i, w i * (a i * b i)) = (∑ i, w i * a i) * (∑ i, w i * b i) ↔
      (∀ i j, a i = a j) ∨ (∀ i j, b i = b j) := by
  have h := sum_mul_sum_eq_sum_mul_iff_of_monovary hw hw1 (monovary_neg_right.mpr hab)
  simpa only [Pi.neg_apply, mul_neg, sum_neg_distrib, neg_inj, eq_comm] using h

end TauCeti
