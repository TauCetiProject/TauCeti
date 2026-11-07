/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.List.Prime
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.LinearCombination

/-!
# Digits of `j + b * y`, factorials of digits, and cyclic shifts of digits

For a digit `j < b`, the base-`b` digits of `j + b * y` are `j` followed by the digits of `y`.
This gives the digit sum and the products over the digits of `j + b * y` in terms of those of
`y`. The product of the factorials of the base-`p` digits of `n` is prime to `p`, since every
digit is less than `p`. These facts index the digit induction in Stickelberger's congruence.

For `0 ≤ a < b ^ f - 1`, multiplication by `b` modulo `b ^ f - 1` cyclically shifts the `f`
base-`b` digits of `a`. Summing the `f` shifts `b ^ i * a % (b ^ f - 1)`, every digit of `a`
occurs once in every position, so `(b - 1) ∑_{i < f} (b ^ i * a % (b ^ f - 1)) = (b ^ f - 1) s(a)`
with `s(a)` the digit sum of `a`; equivalently `s(a) = (b - 1) ∑_{i < f} {b ^ i a / (b ^ f - 1)}`.
For `a = (b ^ f - 1) / m * t` this reads `m s(a) = (b - 1) ∑_{i < f} (b ^ i t % m)`. With `b = p`
and `b ^ f = q` the size of a finite field, this identity turns the digit-sum valuation of Gauss
sums into the exponents `t` of Stickelberger's element `∑ t σ_t⁻¹`.

## Main results

* `Nat.sum_digits_add_mul`: the digit sum of `j + b * y` is `j` plus the digit sum of `y`.
* `Nat.prod_map_digits_add_mul`: `∏ g(dᵢ)` over the digits of `j + b * y` is `g j` times the
  product over the digits of `y`, whenever `g 0 = 1`.
* `Nat.Prime.not_dvd_prod_factorial_digits`: `p` does not divide the product of the factorials of
  the base-`p` digits of `n`.
* `Nat.sub_one_mul_sum_div_pow_succ_eq_sub_sum_digits`: Legendre's identity
  `(b - 1) ∑_{i < f} ⌊a / b ^ (i + 1)⌋ = a - s(a)` for `a < b ^ f`, summed over a fixed range.
* `Nat.pow_mul_mod_pow_add_sub_one`: `b ^ i * a % (b ^ (i + k) - 1)` is the cyclic shift
  `a / b ^ k + b ^ i * (a % b ^ k)` of the digits of `a < b ^ (i + k) - 1`.
* `Nat.sub_one_mul_sum_pow_mul_mod_eq_mul_sum_digits`: the sum of the cyclic shifts,
  `(b - 1) ∑_{i < f} (b ^ i * a % (b ^ f - 1)) = (b ^ f - 1) s(a)` for `a < b ^ f - 1`.
* `Nat.sub_one_mul_sum_pow_mul_mod_eq_mul_sum_digits_div_mul`: for `m ∣ b ^ f - 1` and `t < m`,
  `(b - 1) ∑_{i < f} (b ^ i * t % m) = m s((b ^ f - 1) / m * t)`.

## References

* S. A. Katre, *Gauss–Jacobi sums and Stickelberger's theorem*, §3.
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §6.2.
-/

public section

namespace Nat

/-- Mapping canonical digits into `Fin b` and then taking their values recovers the digits. -/
theorem map_val_map_ofNat_digits {b : ℕ} [NeZero b] (hb : 2 ≤ b) (n : ℕ) :
    ((digits b n).map (Fin.ofNat b)).map Fin.val = digits b n := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (digits b n)]
  exact List.map_congr_left fun d hd ↦ Nat.mod_eq_of_lt (digits_lt_base hb hd)

/-- The digit sum of `j + b * y`, for a digit `j < b`, is `j` plus the digit sum of `y`. -/
theorem sum_digits_add_mul {b j : ℕ} (hj : j < b) (y : ℕ) :
    (digits b (j + b * y)).sum = j + (digits b y).sum := by
  obtain _ | _ | b := b
  · omega
  · obtain rfl : j = 0 := by omega
    simp
  rcases eq_or_ne j 0 with rfl | hj0
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp
    rw [digits_add _ (by omega) 0 y hj (Or.inr hy0)]
    simp
  rw [digits_add _ (by omega) j y hj (Or.inl hj0)]
  simp

/-- The product of `g` over the digits of `j + b * y`, for a digit `j < b` and `g 0 = 1`, is
`g j` times the product of `g` over the digits of `y`. -/
theorem prod_map_digits_add_mul {M : Type*} [Monoid M] {g : ℕ → M} (hg : g 0 = 1) {b j : ℕ}
    (hj : j < b) (y : ℕ) :
    ((digits b (j + b * y)).map g).prod = g j * ((digits b y).map g).prod := by
  obtain _ | _ | b := b
  · omega
  · obtain rfl : j = 0 := by omega
    simp [hg]
  rcases eq_or_ne j 0 with rfl | hj0
  · rcases eq_or_ne y 0 with rfl | hy0
    · simp [hg]
    rw [digits_add _ (by omega) 0 y hj (Or.inr hy0)]
    simp
  rw [digits_add _ (by omega) j y hj (Or.inl hj0)]
  simp

/-- A prime `p` does not divide the product of the factorials of the base-`p` digits of `n`. -/
theorem Prime.not_dvd_prod_factorial_digits {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ¬p ∣ ((digits p n).map factorial).prod := by
  rw [hp.prime.dvd_prod_iff]
  rintro ⟨_, hm, hdvd⟩
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hm
  exact absurd (hp.dvd_factorial.1 hdvd) (not_le.2 (digits_lt_base hp.one_lt hd))

open Finset in
/-- **Legendre's identity over a fixed range.** For `a < b ^ f`,
`(b - 1) ∑_{i < f} ⌊a / b ^ (i + 1)⌋ = a - s(a)`, where `s(a)` is the base-`b` digit sum of `a`.
This is `Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits` with the sum extended by zero terms
from `log b a + 1` to `f`. -/
theorem sub_one_mul_sum_div_pow_succ_eq_sub_sum_digits {b f a : ℕ} (ha : a < b ^ f) :
    (b - 1) * ∑ i ∈ range f, a / b ^ (i + 1) = a - (digits b a).sum := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  have hb : 1 < b := by
    by_contra hb
    interval_cases b <;> rcases f with _ | f <;> simp at ha <;> omega
  rw [← sub_one_mul_sum_log_div_pow_eq_sub_sum_digits]
  congr 1
  refine (sum_subset (range_subset_range.2 (log_lt_of_lt_pow ha0 ha)) fun j _ hj => ?_).symm
  rw [mem_range, not_lt] at hj
  exact Nat.div_eq_of_lt <| (lt_pow_succ_log_self hb a).trans_le <|
    Nat.pow_le_pow_right (by omega) (by omega)

/-- **Multiplication by `b ^ i` shifts digits cyclically modulo `b ^ (i + k) - 1`.** For
`a < b ^ (i + k) - 1`, `b ^ i * a % (b ^ (i + k) - 1) = a / b ^ k + b ^ i * (a % b ^ k)`: the top
`i` digits of `a` move to the bottom. -/
theorem pow_mul_mod_pow_add_sub_one {b i k a : ℕ} (ha : a < b ^ (i + k) - 1) :
    b ^ i * a % (b ^ (i + k) - 1) = a / b ^ k + b ^ i * (a % b ^ k) := by
  rw [pow_add] at ha ⊢
  generalize b ^ i = u at ha ⊢
  generalize b ^ k = w at ha ⊢
  have hw : w ≠ 0 := by rintro rfl; simp at ha
  have hA : a / w < u := Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
  have hB : a % w < w := Nat.mod_lt _ (Nat.pos_of_ne_zero hw)
  rw [← Nat.div_add_mod a w] at ha ⊢
  rw [Nat.mul_add_div (Nat.pos_of_ne_zero hw), Nat.mul_add_mod_self_left,
    Nat.div_eq_of_lt hB, Nat.mod_eq_of_lt hB, add_zero]
  generalize a / w = A at *
  generalize a % w = B at *
  -- Write `u = A + 1 + X` and `w = B + 1 + Y`; then `a < u w - 1` says `X` or `Y` is positive.
  obtain ⟨X, rfl⟩ : ∃ X, u = A + 1 + X := ⟨u - 1 - A, by omega⟩
  obtain ⟨Y, rfl⟩ : ∃ Y, w = B + 1 + Y := ⟨w - 1 - B, by omega⟩
  have h1 : 1 ≤ (A + 1 + X) * (B + 1 + Y) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have key : (A + 1 + X) * ((B + 1 + Y) * A + B) =
      (A + (A + 1 + X) * B) + ((A + 1 + X) * (B + 1 + Y) - 1) * A := by
    zify [h1]
    ring
  rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  rw [Nat.lt_sub_iff_add_lt] at ha ⊢
  rcases Y with _ | Y
  · rcases X with _ | X
    · nlinarith
    · nlinarith
  · nlinarith

open Finset in
/-- **The sum of the cyclic shifts of the digits.** For `a < b ^ f - 1`,
`(b - 1) ∑_{i < f} (b ^ i * a % (b ^ f - 1)) = (b ^ f - 1) s(a)`, where `s(a)` is the base-`b`
digit sum of `a`. Equivalently `s(a) = (b - 1) ∑_{i < f} {b ^ i a / (b ^ f - 1)}`, with `{·}` the
fractional part. -/
theorem sub_one_mul_sum_pow_mul_mod_eq_mul_sum_digits {b f a : ℕ} (ha : a < b ^ f - 1) :
    (b - 1) * ∑ i ∈ range f, b ^ i * a % (b ^ f - 1) = (b ^ f - 1) * (digits b a).sum := by
  have hb : 1 < b := by
    by_contra hb
    interval_cases b <;> rcases f with _ | f <;> simp at ha
  have hN : b ^ f = (b ^ f - 1) + 1 := by have := Nat.one_le_pow f b (by omega); omega
  generalize b ^ f - 1 = N at ha hN ⊢
  -- Each shift is `b ^ i * a` minus `N` times the quotient of `a` by `b ^ (f - i)`.
  have hterm (i : ℕ) (hi : i ∈ range f) :
      b ^ i * a % N + N * (a / b ^ (f - 1 - i + 1)) = b ^ i * a := by
    obtain ⟨k, rfl⟩ : ∃ k, f = i + k := ⟨f - i, by rw [mem_range] at hi; omega⟩
    have hmod := pow_mul_mod_pow_add_sub_one (b := b) (i := i) (k := k) (a := a) (by omega)
    rw [show b ^ (i + k) - 1 = N by omega] at hmod
    rw [show i + k - 1 - i + 1 = k by rw [mem_range] at hi; omega, hmod]
    have hNz : ((b : ℤ) ^ i * b ^ k) = N + 1 := by rw [← pow_add]; exact_mod_cast hN
    conv_rhs => rw [← Nat.div_add_mod a (b ^ k)]
    generalize a / b ^ k = A
    generalize a % b ^ k = B
    zify
    linear_combination (-A : ℤ) * hNz
  -- Summing, `∑ shifts + N ∑ ⌊a / b ^ (j + 1)⌋ = a ∑ b ^ i`; conclude by Legendre's identity.
  have hsum := sum_congr rfl hterm
  rw [sum_add_distrib, ← mul_sum, sum_range_reflect (fun j => a / b ^ (j + 1)) f,
    ← sum_mul] at hsum
  have hgeom := geom_sum_mul_of_one_le hb.le f
  rw [hN, Nat.add_sub_cancel] at hgeom
  have hleg := sub_one_mul_sum_div_pow_succ_eq_sub_sum_digits (show a < b ^ f by omega)
  have hs := digit_sum_le b a
  generalize ∑ i ∈ range f, b ^ i * a % N = S at hsum ⊢
  generalize ∑ i ∈ range f, a / b ^ (i + 1) = T at hsum hleg
  generalize ∑ i ∈ range f, b ^ i = G at hsum hgeom
  generalize (digits b a).sum = s at hs hleg ⊢
  generalize b - 1 = c at hgeom hleg ⊢
  zify [hs] at hsum hgeom hleg ⊢
  linear_combination (c : ℤ) * hsum + (a : ℤ) * hgeom - (N : ℤ) * hleg

open Finset in
/-- **The digit sum of `(b ^ f - 1) / m * t`.** If `m ∣ b ^ f - 1` and `t < m`, then
`(b - 1) ∑_{i < f} (b ^ i * t % m) = m s((b ^ f - 1) / m * t)`, where `s` is the base-`b` digit
sum. -/
theorem sub_one_mul_sum_pow_mul_mod_eq_mul_sum_digits_div_mul {b f m t : ℕ}
    (hm : m ∣ b ^ f - 1) (ht : t < m) :
    (b - 1) * ∑ i ∈ range f, b ^ i * t % m = m * (digits b ((b ^ f - 1) / m * t)).sum := by
  obtain ⟨d, hd⟩ := hm
  have hm0 : 0 < m := by omega
  rw [hd, Nat.mul_div_cancel_left _ hm0]
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · -- If `b ^ f - 1 = 0` then `b ≤ 1` or `f = 0`, and both sides vanish.
    have : b - 1 = 0 ∨ f = 0 := by
      by_contra h
      have := Nat.le_self_pow (by omega : f ≠ 0) b
      omega
    rcases this with h | rfl <;> simp [*]
  have h := sub_one_mul_sum_pow_mul_mod_eq_mul_sum_digits (a := d * t) (b := b) (f := f)
    (by rw [hd, mul_comm m d]; exact Nat.mul_lt_mul_of_pos_left ht hd0)
  simp_rw [hd, mul_comm m d, mul_left_comm _ d t, Nat.mul_mod_mul_left, ← mul_sum,
    mul_left_comm _ d, mul_assoc d m] at h
  exact Nat.eq_of_mul_eq_mul_left hd0 h

end Nat
