/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Basic.Real.Basic

/-!
# Roots of monic polynomials under nonarchimedean power-multiplicative functions

Let `f` be a nonnegative, submultiplicative, power-multiplicative and nonarchimedean function on a
nontrivial ring `R`, with values in a linearly ordered monoid with zero in which multiplication
on the right by a positive element is strictly monotone, such as a nonarchimedean
power-multiplicative ring seminorm or a valuation. If `x : R` is a root of a monic polynomial
`p = X ^ d + ∑_{i < d} aᵢ X ^ i` over `R` itself, then some `i < d` satisfies
`f x ^ (d - i) ≤ f aᵢ` (`Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero`):
otherwise every lower term `aᵢ xⁱ` would be strictly smaller than `xᵈ`, which is impossible in
the nonarchimedean relation `xᵈ = -∑_{i < d} aᵢ xⁱ`.

For real-valued `f`, taking `(d - i)`-th roots gives the root bound
`Polynomial.Monic.apply_le_iSup_apply_coeff_rpow_of_eval_eq_zero`.
-/

public section

namespace Polynomial.Monic

variable {R Γ : Type*} [Ring R] [MonoidWithZero Γ] [LinearOrder Γ] [MulPosStrictMono Γ]
  {f : R → Γ} {p : R[X]} {x : R}

/-- A nonnegative, submultiplicative, power-multiplicative function satisfies `f (-a) ≤ f a`. -/
private theorem apply_neg_le (hf_nn : ∀ a, 0 ≤ f a) (hf_mul : ∀ a b, f (a * b) ≤ f a * f b)
    (hf_pm : IsPowMul f) (a : R) : f (-a) ≤ f a := by
  -- Either `f` vanishes, or `f 1 ≤ 1` and `f (-1) ≤ 1`, as `f 1 = f 1 ^ 2 = f (-1) ^ 2`.
  have hsq (b : R) : f (b ^ 2) = f b * f b := by rw [hf_pm b one_le_two, pow_two]
  rcases (hf_nn 1).eq_or_lt with h1 | h1
  · have h0 (b : R) : f b = 0 :=
      le_antisymm (by simpa [← h1] using hf_mul 1 b) (hf_nn b)
    rw [h0, h0]
  have h11 : f 1 ≤ 1 := (mul_le_iff_le_one_left h1).mp (by rw [← hsq, one_pow])
  have hm1 : f (-1) ≤ 1 := le_of_not_gt fun h ↦ by
    have hpos : 0 < f (-1) := (hf_nn _).lt_of_ne fun h0 ↦ h1.ne' <| by
      rw [← neg_one_sq, hsq, ← h0, mul_zero]
    have := (lt_mul_iff_one_lt_left hpos).mpr h
    rw [← hsq, neg_one_sq] at this
    exact (this.trans_le h11).not_gt h
  calc f (-a) = f (-1 * a) := by rw [neg_one_mul]
    _ ≤ f (-1) * f a := hf_mul _ _
    _ ≤ 1 * f a := mul_le_mul_of_nonneg_right hm1 (hf_nn a)
    _ = f a := one_mul _

/-- A root `x` of a monic polynomial `p` of degree `d` over a nontrivial ring satisfies
`f x ^ (d - i) ≤ f (p.coeff i)` for some `i < d`, for every nonarchimedean, power-multiplicative,
nonnegative, submultiplicative function `f` into a linearly ordered monoid with zero in which
multiplication on the right by a positive element is strictly monotone, such as a nonarchimedean
power-multiplicative ring seminorm or a valuation. -/
theorem exists_apply_pow_le_apply_coeff_of_eval_eq_zero [Nontrivial R] (hp : p.Monic)
    (hf_nn : ∀ a, 0 ≤ f a) (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (hf_pm : IsPowMul f)
    (hf_na : IsNonarchimedean f) (hx : p.eval x = 0) :
    ∃ i < p.natDegree, f x ^ (p.natDegree - i) ≤ f (p.coeff i) := by
  set d := p.natDegree
  have hd : 0 < d := natDegree_pos_of_eval₂_root hp.ne_zero (RingHom.id R) hx fun _ ↦ id
  by_contra! h
  -- Every lower term `aᵢ xⁱ` is strictly smaller than `xᵈ`, which is impossible in the
  -- ultrametric relation `xᵈ = -∑_{i < d} aᵢ xⁱ`.
  have hxd0 : 0 < f x ^ d := (hf_nn _).trans_lt (by simpa using h 0 hd)
  have hterm (i : ℕ) (hi : i < d) : f (p.coeff i * x ^ i) < f x ^ d := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using h 0 hi
    have hxi : f (x ^ i) = f x ^ i := hf_pm x hi0
    -- `f x ^ i` is nonnegative, and nonzero since `f x ^ d = f x ^ (d - i) * f x ^ i` is positive.
    have hxi0 : 0 < f x ^ i := (hxi ▸ hf_nn (x ^ i)).lt_of_ne fun h0 ↦ hxd0.ne <| by
      rw [← Nat.sub_add_cancel hi.le, pow_add, ← h0, mul_zero]
    calc f (p.coeff i * x ^ i) ≤ f (p.coeff i) * f x ^ i := hxi ▸ hf_mul _ _
      _ < f x ^ (d - i) * f x ^ i := mul_lt_mul_of_pos_right (h i hi) hxi0
      _ = f x ^ d := by rw [← pow_add, Nat.sub_add_cancel hi.le]
  obtain ⟨i, hi, hsum⟩ := hf_na.finset_image_add_of_nonempty (fun i ↦ p.coeff i * x ^ i)
    (Finset.nonempty_range_iff.mpr hd.ne')
  have hxd : x ^ d = -∑ i ∈ Finset.range d, p.coeff i * x ^ i := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at hx
    exact eq_neg_of_add_eq_zero_right hx
  have := (hsum.trans_lt (hterm i (Finset.mem_range.mp hi))).trans_eq (hf_pm x hd).symm
  rw [hxd] at this
  exact (this.trans_le (apply_neg_le hf_nn hf_mul hf_pm _)).false

end Polynomial.Monic
