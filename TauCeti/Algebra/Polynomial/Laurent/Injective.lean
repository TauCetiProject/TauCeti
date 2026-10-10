/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Injective polynomial substitutions into Laurent polynomials

Substitution of `T + r T⁻¹ + s` into an ordinary polynomial is injective, even over
coefficient rings with zero divisors. Its powers have highest exponent equal to the power
and coefficient one there, so the leading coefficient of a polynomial survives substitution.

The cases `(r, s) = (1, -2)` and `(-1, 0)` give uniqueness of polynomial expressions in
`T + T⁻¹ - 2` and in the Conway variable, respectively.
-/

public section

open scoped Polynomial

namespace LaurentPolynomial

variable {R : Type*} [CommSemiring R]

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
      have hT (j : ℤ) (p : R[T;T⁻¹]) : (T j * p).coeff k = p.coeff (k - j) := by
        simpa only [T, one_mul] using
          AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff (x := p) (r := (1 : R))
            (k - j) (by intro i _; omega)
      have hC (t : R) (p : R[T;T⁻¹]) : (C t * p).coeff k = t * p.coeff k := by
        exact AddMonoidAlgebra.coeff_single_zero_mul p t k
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hT, hC]
      rw [ih (k - 1) (by omega), ih (k - -1) (by omega), ih k (by omega)]
      have h₁ : k - -1 ≠ (n : ℤ) := by omega
      have h₂ : k ≠ (n : ℤ) := by omega
      simp only [h₁, h₂, ↓reduceIte, mul_zero, add_zero, Nat.cast_succ]
      have h₃ : k - 1 = (n : ℤ) ↔ k = n + 1 := by omega
      simp only [h₃]

/-- Substitution of `T + r T⁻¹ + s` preserves the coefficient at the polynomial's
highest exponent. This holds over rings with zero divisors. -/
theorem coeff_eval₂_T_add_C_mul_T_neg_add_C (p : R[X]) (r s : R) :
    (Polynomial.eval₂ C (T 1 + C r * T (-1) + C s) p).coeff p.natDegree =
      p.leadingCoeff := by
  classical
  have hC (t : R) (q : R[T;T⁻¹]) (k : ℤ) : (C t * q).coeff k = t * q.coeff k :=
    AddMonoidAlgebra.coeff_single_zero_mul q t k
  rw [Polynomial.eval₂_eq_sum_range, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single p.natDegree]
  · rw [hC,
      coeff_pow_T_add_C_mul_T_neg_add_C_of_le r s _ _ le_rfl]
    simp
  · intro i hi hne
    have hle : i ≤ p.natDegree := by simpa using (Finset.mem_range.mp hi)
    rw [hC,
      coeff_pow_T_add_C_mul_T_neg_add_C_of_le r s i _ (by exact_mod_cast hle)]
    simp [Ne.symm hne]
  · simp

end LaurentPolynomial

namespace LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- Substitution of `T + r T⁻¹ + s` is injective on ordinary polynomials over any
commutative coefficient ring. -/
theorem eval₂_C_T_add_C_mul_T_neg_add_C_injective (r s : R) :
    Function.Injective
      (Polynomial.eval₂ C (T 1 + C r * T (-1) + C s) : R[X] → R[T;T⁻¹]) := by
  have hinj : Function.Injective
      (Polynomial.eval₂RingHom C (T 1 + C r * T (-1) + C s) : R[X] →+* R[T;T⁻¹]) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro p hp
    have hc := coeff_eval₂_T_add_C_mul_T_neg_add_C p r s
    rw [Polynomial.coe_eval₂RingHom] at hp
    rw [hp] at hc
    exact Polynomial.leadingCoeff_eq_zero.mp hc.symm
  simpa only [Polynomial.coe_eval₂RingHom] using hinj

/-- Substitution of the Conway variable `T⁻¹ - T` is injective on ordinary polynomials. -/
theorem eval₂_C_T_neg_sub_T_injective :
    Function.Injective (Polynomial.eval₂ C (T (-1) - T 1) : R[X] → R[T;T⁻¹]) := by
  intro p q hpq
  have h := eval₂_C_T_add_C_mul_T_neg_add_C_injective (R := R) (-1) 0
  have he : p.comp (-Polynomial.X) = q.comp (-Polynomial.X) := by
    apply h
    simpa only [Polynomial.eval₂_comp, Polynomial.eval₂_neg, Polynomial.eval₂_X,
      map_neg, map_one, map_zero, neg_one_mul, add_zero, sub_eq_add_neg, neg_add,
      neg_neg, add_comm] using hpq
  simpa only [Polynomial.comp_neg_X_comp_neg_X] using
    congrArg (fun f : R[X] => f.comp (-Polynomial.X)) he

end LaurentPolynomial
