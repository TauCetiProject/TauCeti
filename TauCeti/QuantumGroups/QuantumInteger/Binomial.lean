/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Basic
public import Mathlib.Algebra.Algebra.Defs

import TauCeti.Algebra.BigOperators.Finset.Range
import Mathlib.Tactic

/-!
# Symmetric quantum binomial coefficients

This file defines the symmetric quantum binomial coefficient `[n choose k]_q` in a field by the
Pascal recursion
`[n+1 choose k+1]_q = q^(n-k) [n choose k]_q + q^(-(k+1)) [n choose k+1]_q`,
with `[n choose 0]_q = 1` and `[0 choose k+1]_q = 0`, and proves the noncommutative
`q`-binomial theorem: if `q ≠ 0` and two elements of an algebra satisfy `y x = q² x y`, then
`(x + y)^n = ∑_k q^(k(n-k)) [n choose k]_q x^k y^(n-k)`.

The symmetric normalization makes `[n choose k]_q` invariant under `q ↦ q⁻¹`, and under
`k ↦ n - k` for `k ≤ n`. It gives `[n choose 1]_q = [n]_q` whenever `q - q⁻¹ ≠ 0`, so that the
quantum integer `[n]_q` is defined by a nonzero denominator, and it specializes to `Nat.choose`
at `q = 1`. The `q`-binomial theorem computes the coproducts of the powers of the root
generators of `U_q(sl₂)`.

## Main definitions

* `TauCeti.quantumBinomial q n k`: the symmetric quantum binomial coefficient `[n choose k]_q`.

## Main results

* `TauCeti.quantumBinomial_succ_succ` and `TauCeti.quantumBinomial_succ_succ'`: the two Pascal
  rules, obtained from each other by `q ↦ q⁻¹`.
* `TauCeti.quantumBinomial_succ_right_eq`: the absorption identity
  `[n choose k + 1]_q [k + 1]_q = [n choose k]_q [n - k]_q`.
* `TauCeti.quantumBinomial_inv` and `TauCeti.quantumBinomial_symm`: invariance under `q ↦ q⁻¹`,
  and under `k ↦ n - k` for `k ≤ n`.
* `TauCeti.quantumBinomial_one_right`: `[n choose 1]_q = [n]_q` when `q - q⁻¹ ≠ 0`.
* `TauCeti.quantumBinomial_one`: the classical specialization `[n choose k]_1 = n.choose k`.
* `TauCeti.add_pow_of_mul_eq_smul_mul`: the `q`-binomial theorem for `y x = q² x y` with
  `q ≠ 0`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section IV.2, for Gaussian
  binomial coefficients and the `q`-binomial formula for `y x = q x y`.
* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, Chapter 0, for
  the symmetric normalization.
-/

public section

open Finset

namespace TauCeti

variable {K : Type*}

section

variable [CommSemiring K] [Inv K]

/-- The symmetric quantum binomial coefficient `[n choose k]_q`, defined by `[n choose 0]_q = 1`,
`[0 choose k+1]_q = 0` and the Pascal rule
`[n+1 choose k+1]_q = q^(n-k) [n choose k]_q + q^(-(k+1)) [n choose k+1]_q`. -/
def quantumBinomial (q : K) : ℕ → ℕ → K
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 =>
    q ^ (n - k) * quantumBinomial q n k + q⁻¹ ^ (k + 1) * quantumBinomial q n (k + 1)

/-- `[n choose 0]_q = 1`. -/
@[simp] theorem quantumBinomial_zero_right (q : K) (n : ℕ) : quantumBinomial q n 0 = 1 := by
  cases n <;> simp [quantumBinomial]

/-- `[0 choose k + 1]_q = 0`. -/
theorem quantumBinomial_zero_succ (q : K) (k : ℕ) : quantumBinomial q 0 (k + 1) = 0 := by
  simp [quantumBinomial]

/-- The defining Pascal rule
`[n+1 choose k+1]_q = q^(n-k) [n choose k]_q + q^(-(k+1)) [n choose k+1]_q`. -/
theorem quantumBinomial_succ_succ (q : K) (n k : ℕ) :
    quantumBinomial q (n + 1) (k + 1) =
      q ^ (n - k) * quantumBinomial q n k + q⁻¹ ^ (k + 1) * quantumBinomial q n (k + 1) := by
  rw [quantumBinomial]

/-- `[n choose k]_q = 0` for `n < k`. -/
@[simp] theorem quantumBinomial_eq_zero_of_lt (q : K) {n k : ℕ} (h : n < k) :
    quantumBinomial q n k = 0 := by
  induction n generalizing k with
  | zero =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero h.ne'
    exact quantumBinomial_zero_succ q k
  | succ n ih =>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : k ≠ 0)
    rw [quantumBinomial_succ_succ, ih (by omega), ih (by omega)]
    simp

/-- `[n choose n]_q = 1`. -/
@[simp] theorem quantumBinomial_self (q : K) (n : ℕ) : quantumBinomial q n n = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [quantumBinomial_succ_succ, ih, quantumBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
    simp

end

section

variable [Semifield K]

/-- Over a semifield, the quantum binomial coefficients at `q = 1` are the ordinary
binomial coefficients. -/
@[simp] theorem quantumBinomial_one (n k : ℕ) :
    quantumBinomial (1 : K) n k = n.choose k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [quantumBinomial_succ_succ, ih, Nat.choose_succ_succ]

end

variable [Field K]

/-- `[n choose 1]_q = [n]_q` whenever the quantum integers are defined by a nonzero
denominator. -/
theorem quantumBinomial_one_right {q : K} (hq : q - q⁻¹ ≠ 0) (n : ℕ) :
    quantumBinomial q n 1 = quantumInteger q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [quantumBinomial_succ_succ, ih, Nat.cast_succ, quantumInteger_natCast_succ hq]
    simp only [Nat.sub_zero, quantumBinomial_zero_right, zero_add, pow_one]
    ring

/-- The absorption identity `[n choose k + 1]_q [k + 1]_q = [n choose k]_q [n - k]_q`. At a
generic parameter it determines `[n choose k]_q` from `[n choose 0]_q = 1`. -/
theorem quantumBinomial_succ_right_eq (q : K) (n k : ℕ) :
    quantumBinomial q n (k + 1) * quantumInteger q (k + 1) =
      quantumBinomial q n k * quantumInteger q (n - k) := by
  by_cases hq : q - q⁻¹ = 0
  · simp [quantumInteger_def, hq]
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp [quantumBinomial_one_right hq, quantumInteger_one hq]
    | succ k =>
      rcases lt_or_ge k n with hk | hk
      swap
      · rw [quantumBinomial_eq_zero_of_lt q (by omega : n + 1 < k + 1 + 1)]
        rcases eq_or_lt_of_le hk with rfl | hk
        · simp
        · simp [quantumBinomial_eq_zero_of_lt q (by omega : n + 1 < k + 1)]
      -- Both sides reduce, by the induction hypothesis at `k` and `k + 1`, to multiples of
      -- `[n choose k + 1]_q`; the coefficients agree by the addition formula for `[n + 1]_q`.
      have ih₀ := ih k
      have ih₁ := ih (k + 1)
      have h₁ := quantumInteger_add q ((n : ℤ) - k) ((k : ℤ) + 1)
      have h₂ := quantumInteger_add q ((n : ℤ) - (k + 1)) ((k : ℤ) + 1 + 1)
      rw [show (n : ℤ) - k + (k + 1) = n + 1 by ring] at h₁
      rw [show (n : ℤ) - (k + 1) + (k + 1 + 1) = n + 1 by ring] at h₂
      have p₁ : q ^ (n - k) = q ^ ((n : ℤ) - k) := by rw [← Nat.cast_sub hk.le, zpow_natCast]
      have p₂ : q ^ (n - (k + 1)) = q ^ ((n : ℤ) - (k + 1)) := by
        rw [← zpow_natCast, Nat.cast_sub hk, Nat.cast_add_one]
      have p₃ : ∀ m : ℕ, q⁻¹ ^ m = q ^ (-(m : ℤ)) := fun m => by
        rw [zpow_neg, zpow_natCast, inv_pow]
      rw [quantumBinomial_succ_succ, quantumBinomial_succ_succ, p₁, p₂, p₃, p₃]
      push_cast at ih₁ ⊢
      rw [show (n : ℤ) + 1 - (k + 1) = n - k by ring]
      linear_combination q ^ ((n : ℤ) - k) * ih₀ + q ^ (-((k : ℤ) + 1 + 1)) * ih₁ -
        quantumBinomial q n (k + 1) * (h₂ - h₁)

/-- The second Pascal rule
`[n+1 choose k+1]_q = q^(-(n-k)) [n choose k]_q + q^(k+1) [n choose k+1]_q`, the image of the
defining rule under `q ↦ q⁻¹`. -/
theorem quantumBinomial_succ_succ' (q : K) (n k : ℕ) :
    quantumBinomial q (n + 1) (k + 1) =
      q⁻¹ ^ (n - k) * quantumBinomial q n k + q ^ (k + 1) * quantumBinomial q n (k + 1) := by
  rw [quantumBinomial_succ_succ]
  rcases lt_or_ge n k with h | h
  · simp [quantumBinomial_eq_zero_of_lt q h,
      quantumBinomial_eq_zero_of_lt q (h.trans k.lt_succ_self)]
  by_cases hq : q - q⁻¹ = 0
  · rw [← sub_eq_zero.mp hq]
  have habs := congrArg ((q - q⁻¹) * ·) (quantumBinomial_succ_right_eq q n k)
  simp only [mul_left_comm (q - q⁻¹), ← Nat.cast_sub h, ← Nat.cast_add_one,
    sub_inv_mul_quantumInteger_natCast hq] at habs
  linear_combination -habs

/-- The quantum binomial coefficients are invariant under `q ↦ q⁻¹`. -/
@[simp] theorem quantumBinomial_inv (q : K) (n k : ℕ) :
    quantumBinomial q⁻¹ n k = quantumBinomial q n k := by
  induction n generalizing k with
  | zero => cases k <;> simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => rw [quantumBinomial_succ_succ, ih, ih, inv_inv, quantumBinomial_succ_succ']

/-- The symmetry `[n choose n - k]_q = [n choose k]_q` for `k ≤ n`. -/
theorem quantumBinomial_symm (q : K) {n k : ℕ} (h : k ≤ n) :
    quantumBinomial q n (n - k) = quantumBinomial q n k := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      rcases eq_or_lt_of_le (Nat.le_of_succ_le_succ h) with rfl | hk
      · simp
      -- Expand the left side by the second Pascal rule and the right side by the first; the
      -- induction hypothesis at `k` and `k + 1` matches the two pairs of terms.
      have e₁ : n + 1 - (k + 1) = n - (k + 1) + 1 := by omega
      have e₂ : n - (n - (k + 1)) = k + 1 := by omega
      have e₃ : n - (k + 1) + 1 = n - k := by omega
      rw [e₁, quantumBinomial_succ_succ', quantumBinomial_succ_succ]
      simp only [e₂, e₃, ih hk, ih hk.le]
      ring

/-- The coefficient form of the defining Pascal rule used by the `q`-binomial theorem:
`q^(k(n-k)) [n choose k]_q q^(2(n-k)) + q^((k+1)(n-k-1)) [n choose k+1]_q` equals
`q^((k+1)(n-k)) [n+1 choose k+1]_q` for `k ≤ n`. -/
private theorem pow_mul_quantumBinomial_add_pow_mul_quantumBinomial {q : K} (hq : q ≠ 0)
    {n k : ℕ} (hk : k ≤ n) :
    q ^ (k * (n - k)) * quantumBinomial q n k * (q ^ 2) ^ (n - k) +
        q ^ ((k + 1) * (n - (k + 1))) * quantumBinomial q n (k + 1) =
      q ^ ((k + 1) * (n - k)) * quantumBinomial q (n + 1) (k + 1) := by
  rw [quantumBinomial_succ_succ]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rcases m with _ | j
  · simp
  have e₁ : k + (j + 1) - k = j + 1 := by omega
  have e₂ : k + (j + 1) - (k + 1) = j := by omega
  have hinv : q ^ (k + 1) * q⁻¹ ^ (k + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hq, one_pow]
  simp only [e₁, e₂]
  linear_combination (-(q ^ ((k + 1) * j) * quantumBinomial q (k + (j + 1)) (k + 1))) * hinv

/-- The **`q`-binomial theorem**: if `y x = q² x y` for a nonzero scalar `q`, then
`(x + y)^n = ∑_k q^(k(n-k)) [n choose k]_q x^k y^(n-k)`. -/
theorem add_pow_of_mul_eq_smul_mul {A : Type*} [Semiring A] [Algebra K A] {q : K} (hq : q ≠ 0)
    {x y : A} (h : y * x = q ^ 2 • (x * y)) (n : ℕ) :
    (x + y) ^ n = ∑ k ∈ range (n + 1),
      (q ^ (k * (n - k)) * quantumBinomial q n k) • (x ^ k * y ^ (n - k)) := by
  -- Moving `x` to the left across `y ^ m` produces the factor `(q ^ 2) ^ m`.
  have hpow (m : ℕ) : y ^ m * x = (q ^ 2) ^ m • (x * y ^ m) := by
    have hxy : SemiconjBy x (q ^ 2 • y) y := by rw [SemiconjBy, mul_smul_comm, h]
    rw [← (hxy.pow_right m).eq, smul_pow, mul_smul_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    -- Multiply the expansion of `(x + y)^n` on the right by `x + y`.
    have hterm : ∀ k ∈ range (n + 1),
        (q ^ (k * (n - k)) * quantumBinomial q n k) • (x ^ k * y ^ (n - k)) * (x + y) =
          (q ^ (k * (n - k)) * quantumBinomial q n k * (q ^ 2) ^ (n - k)) •
              (x ^ (k + 1) * y ^ (n - k)) +
            (q ^ (k * (n - k)) * quantumBinomial q n k) • (x ^ k * y ^ (n + 1 - k)) := by
      intro k hk
      rw [show n + 1 - k = n - k + 1 by have := mem_range.mp hk; omega]
      simp only [smul_mul_assoc, mul_add, mul_assoc, hpow, mul_smul_comm, smul_smul, pow_succ]
    -- Regroup the target sum as the shifted first sum plus the second sum, matching
    -- coefficients by the Pascal rule; the last term of the second sum vanishes.
    rw [pow_succ, ih, sum_mul, sum_congr rfl hterm, sum_range_succ_eq_sum_range_add (n := n + 1)
      (g := fun k => (q ^ (k * (n - k)) * quantumBinomial q n k) • (x ^ k * y ^ (n + 1 - k)))
      (h := fun k => (q ^ (k * (n - k)) * quantumBinomial q n k * (q ^ 2) ^ (n - k)) •
        (x ^ (k + 1) * y ^ (n - k)))]
    · simp [add_comm]
    · simp
    · -- The two contributions to index `k + 1` combine by the Pascal rule.
      intro k hk
      rw [Nat.add_sub_add_right, ← add_smul,
        ← pow_mul_quantumBinomial_add_pow_mul_quantumBinomial hq (Nat.lt_succ_iff.mp hk), add_comm]

end TauCeti
