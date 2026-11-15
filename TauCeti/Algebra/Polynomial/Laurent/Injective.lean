/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Injective polynomial substitutions into Laurent polynomials

Substitution of `T + r T⁻¹ + s` into an ordinary polynomial is injective over any
coefficient ring, without commutativity or restrictions on zero divisors. Its `n`-th power has
coefficient one at exponent `n` and zero above it, so the leading coefficient of a polynomial
survives substitution. These coefficient formulas hold over arbitrary semirings.

The cases `(r, s) = (1, -2)` and `(-1, 0)` give uniqueness of polynomial expressions in
`T + T⁻¹ - 2` and, after the inversion `T ↦ T⁻¹`, in the Conway variable `T⁻¹ - T`.
-/

public section

open scoped Polynomial

namespace LaurentPolynomial

section Semiring

variable {R : Type*} [Semiring R]

/-- At and above exponent `n`, the `n`-th power of `T + r T⁻¹ + s` has only its
leading coefficient, which is one. -/
theorem coeff_pow_T_add_C_mul_T_neg_add_C_of_le (r s : R) (n : ℕ) (k : ℤ)
    (h : (n : ℤ) ≤ k) :
    ((T 1 + C r * T (-1) + C s : R[T;T⁻¹]) ^ n).coeff k =
      if k = n then 1 else 0 := by
  classical
  induction n generalizing k with
  | zero =>
      simp only [pow_zero, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, Nat.cast_zero]
      simp [eq_comm]
  | succ n ih =>
      rw [pow_succ', add_mul, add_mul, mul_assoc]
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_T_mul, coeff_C_mul]
      rw [ih (k - 1) (by omega), ih (k - -1) (by omega), ih k (by omega)]
      have h₁ : k - -1 ≠ (n : ℤ) := by omega
      have h₂ : k ≠ (n : ℤ) := by omega
      simp only [h₁, h₂, ↓reduceIte, mul_zero, add_zero, Nat.cast_succ]
      have h₃ : k - 1 = (n : ℤ) ↔ k = n + 1 := by omega
      simp only [h₃]

/-- Substitution of `T + r T⁻¹ + s` preserves the coefficient at the polynomial's
highest exponent. This holds over arbitrary semirings. -/
theorem coeff_eval₂_T_add_C_mul_T_neg_add_C (p : R[X]) (r s : R) :
    (Polynomial.eval₂ C (T 1 + C r * T (-1) + C s) p).coeff p.natDegree =
      p.leadingCoeff := by
  classical
  rw [Polynomial.eval₂_eq_sum_range, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single p.natDegree]
  · rw [coeff_C_mul,
      coeff_pow_T_add_C_mul_T_neg_add_C_of_le r s _ _ le_rfl]
    simp
  · intro i hi hne
    have hle : i ≤ p.natDegree := by simpa using (Finset.mem_range.mp hi)
    rw [coeff_C_mul,
      coeff_pow_T_add_C_mul_T_neg_add_C_of_le r s i _ (by exact_mod_cast hle)]
    simp [Ne.symm hne]
  · simp

end Semiring

section Ring

variable {R : Type*} [Ring R]

/-- Substitution of `T + r T⁻¹ + s` is injective on ordinary polynomials over any
coefficient ring. -/
theorem eval₂_C_T_add_C_mul_T_neg_add_C_injective (r s : R) :
    Function.Injective
      (Polynomial.eval₂ C (T 1 + C r * T (-1) + C s) : R[X] → R[T;T⁻¹]) := by
  intro p q hpq
  have hc := coeff_eval₂_T_add_C_mul_T_neg_add_C (p - q) r s
  rw [Polynomial.eval₂_sub, hpq, sub_self] at hc
  exact sub_eq_zero.mp (Polynomial.leadingCoeff_eq_zero.mp hc.symm)

/-- Substitution of the Conway variable `T⁻¹ - T` is injective on ordinary polynomials. -/
theorem eval₂_C_T_neg_sub_T_injective :
    Function.Injective (Polynomial.eval₂ C (T (-1) - T 1) : R[X] → R[T;T⁻¹]) := by
  intro p q hpq
  apply eval₂_C_T_add_C_mul_T_neg_add_C_injective (R := R) (-1) 0
  -- Mathlib's LaurentPolynomial.invert is an algebra equivalence requiring CommSemiring R.
  -- Use the exponent-negation ring equivalence to allow noncommutative coefficients.
  let f := (AddMonoidAlgebra.mapDomainRingEquiv R (AddEquiv.neg ℤ)).toRingHom
  have hfC : f.comp C = C := by ext r; simp [f, ← single_eq_C, -single_eq_C_mul_T]
  have hfT (n : ℤ) : f (T n) = T (-n) := by simp [f, T, -single_eq_C_mul_T]
  simpa only [Polynomial.hom_eval₂, hfC, map_sub, map_add, hfT, neg_neg,
    map_neg, map_one, map_zero, neg_one_mul, add_zero, sub_eq_add_neg] using congrArg f hpq

end Ring

end LaurentPolynomial
