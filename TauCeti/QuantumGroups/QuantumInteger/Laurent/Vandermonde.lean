/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Laurent.Binomial
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Signed Laurent quantum Vandermonde convolution

The symmetric Laurent Gaussians satisfy
`[m+n choose r]_v = ∑_{a+b=r} v^(n*a-m*b) [m choose a]_v [n choose b]_v`
for all integers `m` and `n`. Working in `ℤ[v, v⁻¹]` makes the identity available
at every unit specialization, without dividing by quantum factorials. In particular,
negative toral weights and roots of unity are included.

The proof extends the Pascal-recurrence argument of
`TauCeti.quantumBinomial_add_left_eq` to signed upper arguments: downward induction
uses that every Laurent monomial is a unit. The normalization is that of G. Lusztig,
*Introduction to Quantum Groups*, §§1.3 and 34.
-/

public section

noncomputable section

namespace TauCeti

open Finset LaurentPolynomial

/-- A summand of the signed Gaussian convolution satisfies the same Pascal rule as
its sum. -/
private theorem signedVandermonde_step (m n : ℤ) (a b : ℕ) {r : ℕ}
    (hab : a + b = r) :
    T (n * (a + 1) - (m + 1) * b) *
        signedLaurentQuantumBinomial (m + 1) (a + 1) * signedLaurentQuantumBinomial n b =
      T (m + n - r) *
          (T (n * a - m * b) *
            signedLaurentQuantumBinomial m a * signedLaurentQuantumBinomial n b) +
        T (-((r : ℤ) + 1)) *
          (T (n * (a + 1) - m * b) *
            signedLaurentQuantumBinomial m (a + 1) * signedLaurentQuantumBinomial n b) := by
  subst r
  rw [signedLaurentQuantumBinomial_succ_succ]
  push_cast
  simp only [mul_add, add_mul, ← mul_assoc, ← T_add]
  congr 4 <;> ring

/-- The convolution satisfies Pascal recurrence in its first upper argument. -/
private theorem signedVandermonde_succ (m n : ℤ) (r : ℕ) :
    (∑ p ∈ antidiagonal (r + 1), T (n * p.1 - (m + 1) * p.2) *
      signedLaurentQuantumBinomial (m + 1) p.1 * signedLaurentQuantumBinomial n p.2) =
    T (m + n - r) * (∑ p ∈ antidiagonal r, T (n * p.1 - m * p.2) *
      signedLaurentQuantumBinomial m p.1 * signedLaurentQuantumBinomial n p.2) +
    T (-((r : ℤ) + 1)) * (∑ p ∈ antidiagonal (r + 1), T (n * p.1 - m * p.2) *
      signedLaurentQuantumBinomial m p.1 * signedLaurentQuantumBinomial n p.2) := by
  rw [Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [sum_congr rfl (fun p hp => signedVandermonde_step m n p.1 p.2
    (mem_antidiagonal.mp hp)), sum_add_distrib, ← mul_sum, ← mul_sum]
  simp only [Nat.cast_zero, mul_zero, zero_sub, signedLaurentQuantumBinomial_zero_right,
    mul_one]
  rw [mul_add (T (-((r : ℤ) + 1)))]
  have hb : T (-((r : ℤ) + 1)) *
      (T (-(m * (r + 1))) * signedLaurentQuantumBinomial n (r + 1)) =
        T (-((m + 1) * (r + 1))) * signedLaurentQuantumBinomial n (r + 1) := by
    rw [← mul_assoc, ← T_add]
    congr 2
    ring
  rw [hb]
  abel

/-- **Signed quantum Vandermonde convolution** in the Laurent ring. Both upper arguments
may be negative; the exponent in the summand is `n*a-m*b`. -/
theorem signedLaurentQuantumBinomial_add_left_eq (m n : ℤ) (r : ℕ) :
    signedLaurentQuantumBinomial (m + n) r =
      ∑ p ∈ antidiagonal r, T (n * p.1 - m * p.2) *
        signedLaurentQuantumBinomial m p.1 * signedLaurentQuantumBinomial n p.2 := by
  suffices h : ∀ m : ℤ, ∀ r : ℕ, signedLaurentQuantumBinomial (m + n) r =
      ∑ p ∈ antidiagonal r, T (n * p.1 - m * p.2) *
        signedLaurentQuantumBinomial m p.1 * signedLaurentQuantumBinomial n p.2 from h m r
  intro m
  induction m using Int.induction_on with
  | zero =>
    intro r
    rw [zero_add, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_eq_single 0]
    · simp
    · intro a _ hne
      have hz : signedLaurentQuantumBinomial 0 a = 0 :=
        (signedLaurentQuantumBinomial_natCast 0 a).trans
          (laurentQuantumBinomial_eq_zero_of_lt (Nat.pos_of_ne_zero hne))
      simp [hz]
    · simp
  | succ m ih =>
    intro r
    cases r with
    | zero => simp
    | succ r =>
      rw [add_right_comm (m : ℤ) 1 n,
        signedLaurentQuantumBinomial_succ_succ, ih, ih, signedVandermonde_succ]
  | pred m ih =>
    intro r
    induction r with
    | zero => simp
    | succ r ihr =>
      have h := signedVandermonde_succ (-m - 1) n r
      have hupper : -(m : ℤ) + n = (-m - 1 + n) + 1 := by ring
      rw [sub_add_cancel, ← ih, hupper, signedLaurentQuantumBinomial_succ_succ, ihr] at h
      have heq := add_left_cancel h
      -- The Pascal coefficient is a Laurent monomial, so it can be cancelled even
      -- when a quantum factorial would vanish after specialization.
      exact mul_left_cancel₀ (isUnit_T (-((r : ℤ) + 1))).ne_zero heq

end TauCeti
