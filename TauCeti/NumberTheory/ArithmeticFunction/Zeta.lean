/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PrimeNumberTheoremAnd contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Convolution powers of the arithmetic zeta function

The Dirichlet-convolution powers of `ArithmeticFunction.zeta` are the fixed-order divisor
functions. Their prime-power coefficients are binomial coefficients, and these coefficients
are bounded by powers of the ordinary divisor count. The analytic subpower estimate is in
`TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds`.

The prime-power argument is adapted from `d_apply_prime_pow` in
[Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*][PNT].

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/88c889477b094e54ea4775cfbfd89c14a52791fe/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L361-L370
-/

public section

namespace ArithmeticFunction

open Finset Nat
open scoped zeta

/-- The prime-power coefficient of the `(k + 1)`-fold divisor function. -/
theorem zeta_pow_succ_apply_prime_pow (k a : ℕ) {p : ℕ} (hp : p.Prime) :
    (ζ ^ (k + 1)) (p ^ a) = (a + k).choose k := by
  induction k generalizing a with
  | zero => simp [hp.ne_zero]
  | succ k ih =>
    rw [pow_succ, mul_zeta_apply, sum_divisors_prime_pow hp]
    simp_rw [ih]
    simpa [add_assoc, add_left_comm, add_comm] using sum_range_add_choose a k

/-- Fixed-order divisor coefficients are bounded by powers of the ordinary divisor count. -/
theorem zeta_pow_succ_apply_le_card_divisors_pow (k n : ℕ) :
    (ζ ^ (k + 1)) n ≤ n.divisors.card ^ k := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmult : (ζ ^ (k + 1) : ArithmeticFunction ℕ).IsMultiplicative :=
    isMultiplicative_zeta.pow
  rw [hmult.multiplicative_factorization _ hn, prod_factorization_eq_prod_primeFactors,
    Nat.card_divisors hn, ← Finset.prod_pow]
  apply Finset.prod_le_prod
  intro p hp
  rw [zeta_pow_succ_apply_prime_pow k _ (prime_of_mem_primeFactors hp)]
  exact Nat.choose_add_le_add_one_pow _ _

end ArithmeticFunction
