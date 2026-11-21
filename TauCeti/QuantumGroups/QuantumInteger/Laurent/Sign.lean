/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Laurent.Binomial

import Mathlib.Tactic

/-!
# Changing the sign of the Laurent parameter

The symmetric Gaussian with arbitrary integer upper argument satisfies
`[m choose r]_{-v} = (-1)^{r(m-r)} [m choose r]_v`. This is an identity over the integral
Laurent ring, not a quotient-of-factorials calculation. It therefore specializes over any ring,
including at roots of unity and in positive characteristic. Negative weights require an integer
exponent; `Int.negOnePow` records its sign without division or a negative power of a nonunit.

These signs are the coefficients needed to compare the divided-power and opposite-root
relations of modified quantum enveloping algebras at opposite parameters. The quantum factorial
changes by `(-1)^{n(n-1)/2}`, the corresponding normalization for divided powers.

The conventions follow G. Lusztig, *Introduction to Quantum Groups*, Chapters 33 and 34.
-/

public section

noncomputable section

open LaurentPolynomial

namespace TauCeti

/-- Changing `v` to `-v` multiplies a natural-upper-argument Laurent Gaussian by
`(-1)^{r(n-r)}`. The formula also holds above the diagonal, where both sides vanish. -/
@[simp]
theorem rescale_neg_one_laurentQuantumBinomial (n r : ℕ) :
    rescale ℤ (-1) (laurentQuantumBinomial n r) =
      (-1) ^ (r * (n - r)) * laurentQuantumBinomial n r := by
  refine eq_of_forall_laurentEval_eq fun K _ u _ => ?_
  simp [quantumBinomial_neg_left]

/-- Changing `v` to `-v` multiplies the signed Laurent Gaussian by `(-1)^{r(m-r)}`,
including negative upper arguments. -/
@[simp]
theorem rescale_neg_one_signedLaurentQuantumBinomial (m : ℤ) (r : ℕ) :
    rescale ℤ (-1) (signedLaurentQuantumBinomial m r) =
      C ((Int.negOnePow ((r : ℤ) * (m - r)) : ℤˣ) : ℤ) *
        signedLaurentQuantumBinomial m r := by
  cases m with
  | ofNat n =>
    by_cases h : r ≤ n
    · simpa only [Int.ofNat_eq_natCast, signedLaurentQuantumBinomial_natCast,
        ← Nat.cast_sub h, ← Nat.cast_mul, Int.coe_negOnePow_natCast,
        map_pow, map_neg, map_one] using
        rescale_neg_one_laurentQuantumBinomial n r
    · simp [Int.ofNat_eq_natCast, laurentQuantumBinomial_eq_zero_of_lt (by omega : n < r)]
  | negSucc n =>
    have hsign : Int.negOnePow ((r : ℤ) * (Int.negSucc n - r)) =
        Int.negOnePow (r * ((n + r : ℕ) - r) : ℕ) := by
      rw [Int.negOnePow_eq_iff]
      convert (Int.even_mul_succ_self (r : ℤ)).neg.add
        (even_two_mul (-(r : ℤ) * n)) using 1
      simp only [Nat.add_sub_cancel, Nat.cast_mul, Int.negSucc_eq]
      ring
    rw [hsign, Int.negSucc_eq, signedLaurentQuantumBinomial_neg_succ, map_mul,
      rescale_neg_one_laurentQuantumBinomial]
    simp only [Int.coe_negOnePow_natCast, map_pow, map_neg, map_one]
    ring

/-- The Laurent quantum integer changes by `(-1)^{m-1}` when the parameter changes sign,
for every integer index. -/
@[simp]
theorem rescale_neg_one_laurentQuantumInteger (m : ℤ) :
    rescale ℤ (-1) (laurentQuantumInteger m) =
      C ((Int.negOnePow (m - 1) : ℤˣ) : ℤ) * laurentQuantumInteger m := by
  simpa using rescale_neg_one_signedLaurentQuantumBinomial m 1

/-- The integral normalization of divided powers changes by `(-1)^{n(n-1)/2}` under
`v ↦ -v`. No quantum factorial is inverted. -/
@[simp]
theorem rescale_neg_one_laurentQuantumFactorial (n : ℕ) :
    rescale ℤ (-1) (laurentQuantumFactorial n) =
      (-1) ^ (n * (n - 1) / 2) * laurentQuantumFactorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hexp : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
      simpa only [Finset.sum_range_id] using
        Finset.sum_range_succ (fun j : ℕ => j) n
    rw [laurentQuantumFactorial_succ, map_mul, ih,
      rescale_neg_one_laurentQuantumInteger]
    simp only [add_sub_cancel_right, Int.coe_negOnePow_natCast,
      map_pow, map_neg, map_one, hexp, pow_add]
    ring

/-- The sign change for signed Gaussians specializes at every unit of every ring,
including at roots of unity and at `±1`. -/
@[simp]
theorem laurentEval_neg_signedLaurentQuantumBinomial {R : Type*} [Ring R]
    (u : Rˣ) (m : ℤ) (r : ℕ) :
    laurentEval (-u) (signedLaurentQuantumBinomial m r) =
      ((Int.negOnePow ((r : ℤ) * (m - r)) : ℤˣ) : ℤ) *
        laurentEval u (signedLaurentQuantumBinomial m r) := by
  have h := congrArg (laurentEval u) (rescale_neg_one_signedLaurentQuantumBinomial m r)
  simpa [-rescale_neg_one_signedLaurentQuantumBinomial] using h

/-- The signed quantum integer changes by `(-1)^{m-1}` at opposite parameters in any ring. -/
@[simp]
theorem laurentEval_neg_laurentQuantumInteger {R : Type*} [Ring R] (u : Rˣ) (m : ℤ) :
    laurentEval (-u) (laurentQuantumInteger m) =
      ((Int.negOnePow (m - 1) : ℤˣ) : ℤ) * laurentEval u (laurentQuantumInteger m) := by
  have h := congrArg (laurentEval u) (rescale_neg_one_laurentQuantumInteger m)
  simpa [-rescale_neg_one_laurentQuantumInteger] using h

/-- The factorial sign formula remains valid after specialization in any ring. -/
@[simp]
theorem laurentEval_neg_laurentQuantumFactorial {R : Type*} [Ring R] (u : Rˣ) (n : ℕ) :
    laurentEval (-u) (laurentQuantumFactorial n) =
      (-1) ^ (n * (n - 1) / 2) * laurentEval u (laurentQuantumFactorial n) := by
  have h := congrArg (laurentEval u) (rescale_neg_one_laurentQuantumFactorial n)
  simpa [-rescale_neg_one_laurentQuantumFactorial] using h

-- These include negative weights and parameters at which field quantum factorials vanish.
example : laurentEval (-1 : ℤˣ) (signedLaurentQuantumBinomial (-2) 1) = 2 := by
  norm_num [Ring.choose_one_right]

example : laurentEval (-1 : ℤˣ) (signedLaurentQuantumBinomial 2 1) = -2 := by
  norm_num [Ring.choose_one_right]

example : laurentEval (-1 : ℤˣ) (laurentQuantumFactorial 3) = -6 := by
  norm_num [laurentEval_one_laurentQuantumFactorial]

end TauCeti
