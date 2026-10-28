/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
-- Proof-only: evaluating a two-variable monomial, and exponents in three variables.
import TauCeti.Algebra.MvPolynomial.Fin.Two
import TauCeti.Data.Finsupp.Fin

/-!
# Two-variable polynomials substituted into three variables

For a polynomial `g(X, Y)` in two variables, this file computes the coefficient of `XⁱYʲZᵏ` in the
four three-variable polynomials `g(X + Y, Z)`, `g(X, Y + Z)`, `g(X, Y)` and `g(Y, Z)` in terms of
the coefficients of `g`. These are the four terms of the additive 2-cocycle identity
`g(X, Y) + g(X + Y, Z) = g(X, Y + Z) + g(Y, Z)`, so these formulas turn that identity into linear
equations on the coefficients of `g`.

## Main results

* `MvPolynomial.coeff_add_pow_mul_X_pow_fin_three`,
  `MvPolynomial.coeff_X_pow_mul_X_pow_fin_three`: the coefficients of `(X a + X b) ^ m * X c ^ k`
  and `X a ^ m * X c ^ k` for distinct `a, b, c : Fin 3`.
* `MvPolynomial.coeff_aeval_X_add_X_X`: the coefficient of `XⁱYʲZᵏ` in `g(X + Y, Z)` is
  `(i + j).choose i` times that of `Xⁱ⁺ʲYᵏ` in `g`.
* `MvPolynomial.coeff_aeval_X_X_add_X`: the coefficient of `XⁱYʲZᵏ` in `g(X, Y + Z)` is
  `(j + k).choose j` times that of `XⁱYʲ⁺ᵏ` in `g`.
* `MvPolynomial.coeff_aeval_X_zero_X_one`, `MvPolynomial.coeff_aeval_X_one_X_two`: the
  coefficients of `g(X, Y)` and `g(Y, Z)`.
-/

public section

namespace MvPolynomial

variable {R : Type*} [CommSemiring R]

/-- The coefficients of `(X a + X b) ^ m * X c ^ k` in three variables `a, b, c`. -/
theorem coeff_add_pow_mul_X_pow_fin_three {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (m k : ℕ) (d : Fin 3 →₀ ℕ) :
    ((X a + X b) ^ m * X c ^ k : MvPolynomial (Fin 3) R).coeff d =
      if d a + d b = m ∧ d c = k then (m.choose (d a) : R) else 0 := by
  classical
  rw [add_pow, Finset.sum_mul, coeff_sum]
  have key (l : ℕ) : (X a ^ l * X b ^ (m - l) * (m.choose l : MvPolynomial (Fin 3) R) *
      X c ^ k).coeff d = if d a = l ∧ d b = m - l ∧ d c = k then (m.choose l : R) else 0 := by
    -- Write the product as the single monomial `X a ^ l * X b ^ (m - l) * X c ^ k`.
    rw [← map_natCast (C : R →+* _)]
    simp only [C_apply, X_pow_eq_monomial, monomial_mul_monomial, add_zero, mul_one, one_mul,
      coeff_monomial, Finsupp.ext_iff_of_fin_three hab hac hbc]
    simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm, eq_comm]
  simp only [key]
  split_ifs with h
  · rw [Finset.sum_eq_single (d a)]
    · rw [ite_eq_left ⟨rfl, by omega, h.2⟩]
    · intro l _ hl
      rw [ite_eq_right (by omega)]
    · intro hd
      simp at hd
      omega
  · refine Finset.sum_eq_zero fun l hl => ?_
    rw [Finset.mem_range] at hl
    rw [ite_eq_right (by omega)]

/-- The coefficients of `X a ^ m * X c ^ k` in three variables `a, b, c`. -/
theorem coeff_X_pow_mul_X_pow_fin_three {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (m k : ℕ) (d : Fin 3 →₀ ℕ) :
    (X a ^ m * X c ^ k : MvPolynomial (Fin 3) R).coeff d =
      if d a = m ∧ d b = 0 ∧ d c = k then 1 else 0 := by
  classical
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one, coeff_monomial]
  simp only [Finsupp.ext_iff_of_fin_three hab hac hbc]
  simp [hac, hbc, hab.symm, hac.symm, eq_comm]

/-- The coefficient of `XⁱYʲZᵏ` in `g(X + Y, Z)` is `(i + j).choose i` times that of `Xⁱ⁺ʲYᵏ`
in `g`. -/
theorem coeff_aeval_X_add_X_X (g : MvPolynomial (Fin 2) R) (d : Fin 3 →₀ ℕ) :
    (aeval ![X 0 + X 1, X 2] g).coeff d =
      (d 0 + d 1).choose (d 0) *
        g.coeff (Finsupp.single 0 (d 0 + d 1) + Finsupp.single 1 (d 2)) := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    classical
    rw [aeval_monomial_fin_two, algebraMap_eq, coeff_C_mul,
      coeff_add_pow_mul_X_pow_fin_three (by decide) (by decide) (by decide), coeff_monomial]
    simp only [Finsupp.ext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all [mul_comm]
  | add p q hp hq => simp [hp, hq, mul_add]

/-- The coefficient of `XⁱYʲZᵏ` in `g(X, Y + Z)` is `(j + k).choose j` times that of `XⁱYʲ⁺ᵏ`
in `g`. -/
theorem coeff_aeval_X_X_add_X (g : MvPolynomial (Fin 2) R) (d : Fin 3 →₀ ℕ) :
    (aeval ![X 0, X 1 + X 2] g).coeff d =
      (d 1 + d 2).choose (d 1) *
        g.coeff (Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1 + d 2)) := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    classical
    rw [aeval_monomial_fin_two, algebraMap_eq, mul_comm (X 0 ^ _), coeff_C_mul,
      coeff_add_pow_mul_X_pow_fin_three (by decide) (by decide) (by decide), coeff_monomial]
    simp only [Finsupp.ext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all [mul_comm]
  | add p q hp hq => simp [hp, hq, mul_add]

/-- The coefficient of `XⁱYʲZᵏ` in `g(X, Y)` is that of `XⁱYʲ` in `g` if `k = 0`, and `0`
otherwise. -/
theorem coeff_aeval_X_zero_X_one (g : MvPolynomial (Fin 2) R) (d : Fin 3 →₀ ℕ) :
    (aeval ![X 0, X 1] g).coeff d =
      if d 2 = 0 then g.coeff (Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1)) else 0 := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    classical
    rw [aeval_monomial_fin_two, algebraMap_eq, coeff_C_mul,
      coeff_X_pow_mul_X_pow_fin_three (b := 2) (by decide) (by decide) (by decide), coeff_monomial]
    simp only [Finsupp.ext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all
  | add p q hp hq => simp [hp, hq, ite_add_ite]

/-- The coefficient of `XⁱYʲZᵏ` in `g(Y, Z)` is that of `XʲYᵏ` in `g` if `i = 0`, and `0`
otherwise. -/
theorem coeff_aeval_X_one_X_two (g : MvPolynomial (Fin 2) R) (d : Fin 3 →₀ ℕ) :
    (aeval ![X 1, X 2] g).coeff d =
      if d 0 = 0 then g.coeff (Finsupp.single 0 (d 1) + Finsupp.single 1 (d 2)) else 0 := by
  induction g using MvPolynomial.induction_on' with
  | monomial u c =>
    classical
    rw [aeval_monomial_fin_two, algebraMap_eq, coeff_C_mul,
      coeff_X_pow_mul_X_pow_fin_three (b := 0) (by decide) (by decide) (by decide), coeff_monomial]
    simp only [Finsupp.ext_iff, Fin.forall_fin_two]
    split_ifs <;> simp_all
  | add p q hp hq => simp [hp, hq, ite_add_ite]

end MvPolynomial
