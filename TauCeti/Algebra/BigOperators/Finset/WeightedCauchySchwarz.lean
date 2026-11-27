/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Weighted Cauchy--Schwarz for finite sums

This file records the form of the Cauchy--Schwarz inequality that bounds a weighted first absolute
moment by the square root of the corresponding weighted second moment. It also records the
elementary bound of a quadratic form with a nonnegative symmetric kernel by its row sums, the step
that usually comes after Cauchy--Schwarz in bilinear-sum arguments.

## Main results

* `Finset.weighted_sum_abs_le_sqrt`: the weighted first-moment bound when the weights sum to at
  most one.
* `Finset.sum_sum_abs_le_sqrt` and `Finset.sum_abs_le_sqrt`: uniform product and single-set
  Cauchy--Schwarz bounds from a mean-square bound.
* `Finset.sum_sum_mul_mul_le_of_symm`: a quadratic form with a nonnegative symmetric kernel is
  at most the sum of the squares weighted by the row sums of the kernel.
-/

public section

namespace Finset

/-- **Weighted Cauchy--Schwarz.** If nonnegative weights sum to at most one and the weighted
sum of squares of `f` is at most `ε`, then the weighted sum of `|f|` is at most `√ε`. -/
theorem weighted_sum_abs_le_sqrt {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i ≤ 1)
    (hε : ∑ i ∈ s, w i * f i ^ 2 ≤ ε) :
    ∑ i ∈ s, w i * |f i| ≤ √ε := by
  have hg : ∀ i ∈ s, 0 ≤ w i * f i ^ 2 :=
    fun i hi => mul_nonneg (hw0 i hi) (sq_nonneg _)
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  refine (sum_sq_le_sum_mul_sum_of_sq_le_mul s hw0 hg
    fun i _ => (by rw [mul_pow, sq_abs]; ring : _ = _).le).trans ?_
  exact (mul_le_mul hw1 hε (sum_nonneg hg) zero_le_one).trans_eq (one_mul ε)

/-- **Uniform product Cauchy--Schwarz.** If the average over `s` of `∑ a ∈ t, f i a ^ 2` is at most
`ε`, then `∑ i ∈ s, ∑ a ∈ t, |f i a| ≤ √(#t * ε) * #s`. -/
theorem sum_sum_abs_le_sqrt {ι α : Type*} (s : Finset ι) (t : Finset α) (f : ι → α → ℝ)
    {ε : ℝ} (hε : (∑ i ∈ s, ∑ a ∈ t, f i a ^ 2) / #s ≤ ε) :
    ∑ i ∈ s, ∑ a ∈ t, |f i a| ≤ √(#t * ε) * #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have hS : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  have hT : (0 : ℝ) < #t := Nat.cast_pos.2 ht.card_pos
  have hST : (0 : ℝ) < #s * #t := mul_pos hS hT
  have hε₀ : 0 ≤ ε :=
    (div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) hS.le).trans hε
  have hw1 : ∑ _p ∈ s ×ˢ t, ((#s : ℝ) * #t)⁻¹ ≤ 1 := by
    rw [sum_const, card_product, nsmul_eq_mul, Nat.cast_mul, mul_inv_cancel₀ hST.ne']
  have hsq : ∑ p ∈ s ×ˢ t, ((#s : ℝ) * #t)⁻¹ * f p.1 p.2 ^ 2 ≤ ε / #t := by
    rw [← mul_sum, sum_product, inv_mul_eq_div, ← div_div]
    exact div_le_div_of_nonneg_right hε hT.le
  have hcs := weighted_sum_abs_le_sqrt (s ×ˢ t) (fun _ ↦ ((#s : ℝ) * #t)⁻¹)
    (fun p ↦ f p.1 p.2) (fun _ _ ↦ inv_nonneg.2 hST.le) hw1 hsq
  rw [← mul_sum, sum_product, inv_mul_le_iff₀ hST] at hcs
  refine hcs.trans_eq ?_
  calc ((#s : ℝ) * #t) * √(ε / #t)
      = (√(ε / #t) * √((#t : ℝ) ^ 2)) * #s := by
          rw [Real.sqrt_sq hT.le]; ring
    _ = √(#t * ε) * #s := by
          rw [← Real.sqrt_mul (div_nonneg hε₀ hT.le), sq, ← mul_assoc,
            div_mul_cancel₀ _ hT.ne', mul_comm ε]

/-- **Uniform Cauchy--Schwarz.** If the average over `s` of `f i ^ 2` is at most `ε`, then
`∑ i ∈ s, |f i| ≤ √ε * #s`. -/
theorem sum_abs_le_sqrt {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {ε : ℝ} (hε : (∑ i ∈ s, f i ^ 2) / #s ≤ ε) :
    ∑ i ∈ s, |f i| ≤ √ε * #s := by
  simpa using s.sum_sum_abs_le_sqrt {()} (fun i _ ↦ f i) (by simpa using hε)

/-- **Quadratic forms with a symmetric kernel.** For a kernel `K` that is nonnegative and symmetric
on `s`, `∑_{i, j} x i x j K i j ≤ ∑_i x i ^ 2 ∑_j K i j`, from
`x i x j ≤ (x i ^ 2 + x j ^ 2) / 2`. -/
theorem sum_sum_mul_mul_le_of_symm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (K : ι → ι → ℝ)
    (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j) (hsymm : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i) :
    ∑ i ∈ s, ∑ j ∈ s, x i * x j * K i j ≤ ∑ i ∈ s, x i ^ 2 * ∑ j ∈ s, K i j := by
  have h : 2 * ∑ i ∈ s, ∑ j ∈ s, x i * x j * K i j ≤
      ∑ i ∈ s, ∑ j ∈ s, (x i ^ 2 * K i j + x j ^ 2 * K j i) := by
    rw [mul_sum]
    refine sum_le_sum fun i hi ↦ ?_
    rw [mul_sum]
    refine sum_le_sum fun j hj ↦ ?_
    rw [← hsymm i hi j hj]
    nlinarith [mul_nonneg (sq_nonneg (x i - x j)) (hK i hi j hj)]
  simp only [sum_add_distrib] at h
  rw [sum_comm (f := fun i j ↦ x j ^ 2 * K j i)] at h
  simp only [mul_sum]
  linarith

end Finset
