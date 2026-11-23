/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Nat.Choose.Sum
import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# The rotation formula for the probabilists' Hermite polynomials

For `c s : R` in a commutative ring with `c² + s² = 1`, the probabilists' Hermite polynomials
`Hₙ = Polynomial.hermite n` satisfy

  `Hₙ(c x + s y) = ∑_{m ≤ n} (n choose m) c^{n-m} s^m H_{n-m}(x) Hₘ(y)`.

Over `ℂ` this is the coefficient form of the factorization of the generating function
`exp(z t - t²/2)` at `z = c x + s y` into the generating functions at `x` (with `t` scaled by
`c`) and at `y` (with `t` scaled by `s`). Here it is proved over an arbitrary commutative ring:
both sides satisfy the three-term recurrence `H_{n+2}(z) = z H_{n+1}(z) - (n + 1) Hₙ(z)` with the
same initial values. With `c = cos t` and `s = sin t` it is the terminating case
`a = -n - 1/2` of the rotational addition theorem for parabolic cylinder functions
(DLMF 12.13.5), where `U(-k - 1/2, z) = exp(-z²/4) H_k(z)` (DLMF 12.7.2).

## Main statements

* `Polynomial.hermite_aeval_mul_add_mul`: the rotation formula.

## References

* *NIST Digital Library of Mathematical Functions*, [12.7.2](https://dlmf.nist.gov/12.7#E2) and
  [12.13.5](https://dlmf.nist.gov/12.13#E5).
-/

public section

namespace Polynomial

open Finset

variable {R : Type*} [CommRing R]

/-- The binomially weighted double sum `∑_{i + j = n} (n choose i) pⁱ qʲ aᵢ bⱼ` that appears on the
right-hand side of the rotation formula. -/
private noncomputable def rotationSum (p q : R) (a b : ℕ → R) (n : ℕ) : R :=
  ∑ ij ∈ antidiagonal n, (n.choose ij.1 : R) * (p ^ ij.1 * q ^ ij.2 * a ij.1 * b ij.2)

private theorem rotationSum_comm (p q : R) (a b : ℕ → R) (n : ℕ) :
    rotationSum p q a b n = rotationSum q p b a n := by
  rw [rotationSum, ← Nat.sum_antidiagonal_swap, rotationSum]
  refine sum_congr rfl fun ij hij => ?_
  rw [mem_antidiagonal] at hij
  simp only [Prod.fst_swap, Prod.snd_swap, Nat.choose_symm_of_eq_add hij.symm]
  ring

/-- Lowering the second index: the sum of `j aᵢ b_{j-1}` over `i + j = m + 1` is
`(m + 1) q` times the `m`-th rotation sum. -/
private theorem sum_antidiagonal_succ_choose_mul_mul_natCast_mul (p q : R) (a b : ℕ → R)
    (m : ℕ) :
    ∑ ij ∈ antidiagonal (m + 1),
        ((m + 1).choose ij.1 : R) * (p ^ ij.1 * q ^ ij.2 * a ij.1 * (ij.2 * b (ij.2 - 1))) =
      (m + 1) * q * rotationSum p q a b m := by
  rw [← Nat.sum_antidiagonal_swap]
  have h := sum_antidiagonal_choose_succ_nsmul_nsmul
    (fun j i => p ^ i * q ^ j * a i * b (j - 1)) m
  simp only [nsmul_eq_mul, add_tsub_cancel_right] at h
  calc _ = ∑ ij ∈ antidiagonal (m + 1),
        ((m + 1).choose ij.1 : R) * (ij.1 * (p ^ ij.2 * q ^ ij.1 * a ij.2 * b (ij.1 - 1))) :=
        sum_congr rfl fun ij hij => by
          rw [mem_antidiagonal] at hij
          simp only [Prod.fst_swap, Prod.snd_swap, Nat.choose_symm_of_eq_add hij.symm]
          ring
    _ = _ := by
      rw [h, rotationSum_comm, rotationSum, Nat.cast_succ, mul_assoc]
      exact congrArg _ (by rw [mul_sum]; exact sum_congr rfl fun ij _ => by ring)

/-- Raising the second index, using the three-term recurrence of `b`. -/
private theorem sum_antidiagonal_choose_mul_succ (p q y : R) (a b : ℕ → R)
    (hb : ∀ j, b (j + 1) = y * b j - j * b (j - 1)) (m : ℕ) :
    ∑ ij ∈ antidiagonal (m + 1),
        ((m + 1).choose ij.1 : R) * (p ^ ij.1 * q ^ (ij.2 + 1) * a ij.1 * b (ij.2 + 1)) =
      q * y * rotationSum p q a b (m + 1) - (m + 1) * q ^ 2 * rotationSum p q a b m := by
  calc _ = ∑ ij ∈ antidiagonal (m + 1),
        (q * y * ((m + 1).choose ij.1 * (p ^ ij.1 * q ^ ij.2 * a ij.1 * b ij.2)) -
          q * ((m + 1).choose ij.1 * (p ^ ij.1 * q ^ ij.2 * a ij.1 * (ij.2 * b (ij.2 - 1))))) :=
        sum_congr rfl fun ij _ => by rw [hb]; ring
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum,
        sum_antidiagonal_succ_choose_mul_mul_natCast_mul]
      simp only [rotationSum]
      ring

/-- The rotation sums satisfy the Hermite three-term recurrence at `p x + q y` whenever
`p² + q² = 1` and `a`, `b` satisfy it at `x`, `y`. -/
private theorem rotationSum_add_two {p q x y : R} (h : p ^ 2 + q ^ 2 = 1) {a b : ℕ → R}
    (ha : ∀ i, a (i + 1) = x * a i - i * a (i - 1))
    (hb : ∀ j, b (j + 1) = y * b j - j * b (j - 1)) (m : ℕ) :
    rotationSum p q a b (m + 2) =
      (p * x + q * y) * rotationSum p q a b (m + 1) - (m + 1) * rotationSum p q a b m := by
  have h₁ := sum_antidiagonal_choose_mul_succ p q y a b hb m
  have h₂ := sum_antidiagonal_choose_mul_succ q p x b a ha m
  rw [rotationSum_comm q p, rotationSum_comm q p] at h₂
  rw [rotationSum, Finset.sum_antidiagonal_choose_succ_mul
    (fun i j => p ^ i * q ^ j * a i * b j) (m + 1)]
  rw [← Nat.sum_antidiagonal_swap] at h₂
  simp only [Prod.fst_swap, Prod.snd_swap] at h₂
  have h₂' : ∑ ij ∈ antidiagonal (m + 1),
      ((m + 1).choose ij.2 : R) * (p ^ (ij.1 + 1) * q ^ ij.2 * a (ij.1 + 1) * b ij.2) =
        p * x * rotationSum p q a b (m + 1) - (m + 1) * p ^ 2 * rotationSum p q a b m := by
    rw [← h₂]
    exact sum_congr rfl fun ij _ => by ring
  rw [h₁, h₂']
  linear_combination (-(m + 1 : R) * rotationSum p q a b m) * h

/-- **Rotation formula for the Hermite polynomials.** If `c² + s² = 1`, then
`Hₙ(c x + s y) = ∑_{m ≤ n} (n choose m) c^{n-m} s^m H_{n-m}(x) Hₘ(y)`, where
`Hₙ = Polynomial.hermite n` are the probabilists' Hermite polynomials. -/
theorem hermite_aeval_mul_add_mul {c s : R} (h : c ^ 2 + s ^ 2 = 1) (x y : R) (n : ℕ) :
    aeval (c * x + s * y) (hermite n) =
      ∑ m ∈ range (n + 1), (n.choose m : R) * c ^ (n - m) * s ^ m *
        aeval x (hermite (n - m)) * aeval y (hermite m) := by
  have hrec (z : R) (j : ℕ) :
      aeval z (hermite (j + 1)) = z * aeval z (hermite j) - j * aeval z (hermite (j - 1)) := by
    cases j with
    | zero => simp
    | succ j => simpa using aeval_hermite_add_two z j
  have key : aeval (s * y + c * x) (hermite n) =
      rotationSum s c (fun j => aeval y (hermite j)) (fun i => aeval x (hermite i)) n := by
    induction n using Nat.twoStepInduction with
    | zero => simp [rotationSum]
    | one => simp [rotationSum, Nat.antidiagonal_succ]; ring
    | more n ih₀ ih₁ =>
      rw [rotationSum_add_two (by linear_combination h) (hrec y) (hrec x), ← ih₀, ← ih₁,
        aeval_hermite_add_two]
  rw [add_comm, key, rotationSum, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (n.choose i : R) * (s ^ i * c ^ j * aeval y (hermite i) * aeval x (hermite j)))]
  exact sum_congr rfl fun m _ => by ring

end Polynomial
