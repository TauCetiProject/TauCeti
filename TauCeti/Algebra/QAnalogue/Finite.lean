/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Finite multiplicative q-products

The q-factorial `qFactorial q n` is the product of the geometric sums `[i]_q`
for `1 ≤ i ≤ n`. The multiplicative Pochhammer symbol `qPochhammer x q n`
is the product of `1 - x * q^i` for `0 ≤ i < n`. Unlike additive Pochhammer
symbols, its shifts multiply the first parameter by powers of the second.

These definitions can be used in polynomial rings before any specialization or
division. In particular, `qPochhammer q q n` is the factorial polynomial
`∏ i < n, (1 - q^(i+1))`. The normalization relating it to the q-factorial
is valid even when `1 - q` is not invertible.

The finite product conventions follow W. J. G. Ong, notes of Peter Scholze's
*The Habiro Ring of a Number Field*, Definition 1.1 and Table 1.
-/

public section

open Finset

namespace TauCeti

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The q-factorial, the product of `[i]_q = ∑ j < i, q^j` for `1 ≤ i ≤ n`. -/
def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, ∑ j ∈ range (i + 1), q ^ j

/-- The empty q-factorial is one. -/
@[simp] theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 := by
  simp [qFactorial]

/-- Appending the last q-integer to a q-factorial. -/
theorem qFactorial_succ (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * ∑ j ∈ range (n + 1), q ^ j := by
  simp [qFactorial, prod_range_succ]

/-- The q-factorial of one is one. -/
@[simp] theorem qFactorial_one (q : R) : qFactorial q 1 = 1 := by
  simp [qFactorial]

/-- At parameter one the q-factorial specializes to the ordinary factorial. -/
@[simp] theorem qFactorial_one_left (n : ℕ) : qFactorial (1 : R) n = n.factorial := by
  simpa only [qFactorial, one_geom_sum, Nat.cast_prod, Nat.cast_add, Nat.cast_one] using
    congrArg (fun k : ℕ => (k : R)) (prod_range_add_one_eq_factorial n)

/-- At parameter zero every factor is one. -/
@[simp] theorem qFactorial_zero_left (n : ℕ) : qFactorial (0 : R) n = 1 := by
  simp [qFactorial, zero_geom_sum]

/-- A shorter q-factorial divides a longer one, without requiring nonzero factors. -/
theorem qFactorial_dvd_qFactorial (q : R) {m n : ℕ} (h : m ≤ n) :
    qFactorial q m ∣ qFactorial q n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨∏ i ∈ range k, ∑ j ∈ range (m + i + 1), q ^ j,
    by simp [qFactorial, prod_range_add]⟩

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- The finite multiplicative Pochhammer symbol `(x;q)_n`. -/
def qPochhammer (x q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, (1 - x * q ^ i)

/-- The empty multiplicative Pochhammer product is one. -/
@[simp] theorem qPochhammer_zero (x q : R) : qPochhammer x q 0 = 1 := by
  simp [qPochhammer]

/-- The first multiplicative Pochhammer product is `1 - x`. -/
@[simp] theorem qPochhammer_one (x q : R) : qPochhammer x q 1 = 1 - x := by
  simp [qPochhammer]

/-- Appending the last factor of a multiplicative Pochhammer product. -/
theorem qPochhammer_succ (x q : R) (n : ℕ) :
    qPochhammer x q (n + 1) = qPochhammer x q n * (1 - x * q ^ n) := by
  simp [qPochhammer, prod_range_succ]

/-- Removing the first factor shifts `x` to `xq`. -/
theorem qPochhammer_succ_left (x q : R) (n : ℕ) :
    qPochhammer x q (n + 1) = (1 - x) * qPochhammer (x * q) q n := by
  simp [qPochhammer, prod_range_succ', pow_succ, mul_assoc, mul_comm]

/-- Splitting a product into two consecutive blocks shifts the first parameter
of the second block from `x` to `x * q^m`. -/
theorem qPochhammer_add (x q : R) (m n : ℕ) :
    qPochhammer x q (m + n) =
      qPochhammer x q m * qPochhammer (x * q ^ m) q n := by
  simp [qPochhammer, prod_range_add, pow_add, mul_assoc]

/-- At `q = 1` the multiplicative Pochhammer symbol is an ordinary power. -/
@[simp] theorem qPochhammer_one_right (x : R) (n : ℕ) :
    qPochhammer x 1 n = (1 - x) ^ n := by
  simp [qPochhammer]

/-- At parameter zero a positive product retains only its first factor. -/
@[simp] theorem qPochhammer_zero_right (x : R) (n : ℕ) :
    qPochhammer x 0 (n + 1) = 1 - x := by
  rw [qPochhammer_succ_left]
  simp [qPochhammer]

/-- A zero first parameter gives a product of ones. -/
@[simp] theorem qPochhammer_zero_left (q : R) (n : ℕ) : qPochhammer 0 q n = 1 := by
  simp [qPochhammer]

/-- A positive product starting at one has a zero first factor. -/
@[simp] theorem qPochhammer_one_left (q : R) (n : ℕ) :
    qPochhammer 1 q (n + 1) = 0 := by
  rw [qPochhammer_succ_left]
  simp

/-- A shorter Pochhammer product divides a longer one. -/
theorem qPochhammer_dvd_qPochhammer (x q : R) {m n : ℕ} (h : m ≤ n) :
    qPochhammer x q m ∣ qPochhammer x q n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨qPochhammer (x * q ^ m) q k, qPochhammer_add x q m k⟩

/-- The integral normalization relating q-factorials and factorial Pochhammer products.
No cancellation of `1 - q` is needed. -/
theorem one_sub_pow_mul_qFactorial (q : R) (n : ℕ) :
    (1 - q) ^ n * qFactorial q n = qPochhammer q q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, qFactorial_succ, qPochhammer_succ]
    have h := mul_neg_geom_sum q (n + 1)
    calc
      _ = ((1 - q) ^ n * qFactorial q n) *
          ((1 - q) * ∑ j ∈ range (n + 1), q ^ j) := by ring
      _ = _ := by rw [ih, h, pow_succ']

end CommRing

-- Small specializations check the finite product conventions without division.
example : qFactorial (1 : ℤ) 3 = 6 := by norm_num [Nat.factorial]

example (q : ℤ) : qFactorial q 3 = (1 + q) * (1 + q + q ^ 2) := by
  simp [qFactorial, sum_range_succ, prod_range_succ]

example (q : ℤ) : qPochhammer q q 2 = (1 - q) * (1 - q ^ 2) := by
  simp [qPochhammer_succ, pow_two]

example : qPochhammer (2 : ℤ) 3 3 = -85 := by
  norm_num [qPochhammer, prod_range_succ]

end TauCeti

namespace Units

open TauCeti

variable {R : Type*} [CommRing R]

/-- Inverting a unit parameter contributes the sign and inverse triangular power.
The exponent is `1 + ⋯ + n = n(n+1)/2`. -/
theorem qPochhammer_inv (q : Rˣ) (n : ℕ) :
    qPochhammer (↑q⁻¹ : R) ↑q⁻¹ n =
      (-1) ^ n * (↑q⁻¹ : R) ^ (n * (n + 1) / 2) * qPochhammer (↑q : R) ↑q n := by
  have htri (k : ℕ) : (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + (k + 1) := by
    have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by ring
    omega
  induction n with
  | zero => simp
  | succ n ih =>
    rw [qPochhammer_succ, qPochhammer_succ, ih, htri, pow_succ, pow_add]
    have hunit : (↑q⁻¹ : R) ^ (n + 1) * (↑q : R) ^ (n + 1) = 1 := by
      rw [← mul_pow]
      simp
    simp only [← pow_succ']
    linear_combination
      -((-1 : R) ^ n * (↑q⁻¹ : R) ^ (n * (n + 1) / 2) *
        qPochhammer (↑q : R) ↑q n) * hunit

end Units

namespace RingHom

variable {R S : Type*}

/-- Q-factorials commute with coefficient homomorphisms. -/
@[simp] theorem map_qFactorial [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (q : R) (n : ℕ) :
    f (TauCeti.qFactorial q n) = TauCeti.qFactorial (f q) n := by
  simp [TauCeti.qFactorial, map_prod, map_sum]

/-- Finite multiplicative Pochhammer products commute with coefficient homomorphisms. -/
@[simp] theorem map_qPochhammer [CommRing R] [CommRing S]
    (f : R →+* S) (x q : R) (n : ℕ) :
    f (TauCeti.qPochhammer x q n) = TauCeti.qPochhammer (f x) (f q) n := by
  simp [TauCeti.qPochhammer, map_prod]

end RingHom
