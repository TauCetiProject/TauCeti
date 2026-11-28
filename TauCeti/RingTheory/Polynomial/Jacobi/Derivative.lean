/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Jacobi.Basic
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Nat.Factorial.Field

/-!
# The raising relation of the Jacobi polynomials

For the Jacobi polynomials `Pₙ^{(α,β)} = Polynomial.jacobi α β n` over a commutative `ℚ`-algebra
this file proves the raising relation

`(X - 1) (X + 1) (Pₙ^{(α+1,β+1)})' + ((β + 1) (X - 1) + (α + 1) (X + 1)) Pₙ^{(α+1,β+1)}
  = 2 (n + 1) Pₙ₊₁^{(α,β)}`,

which expresses `Pₙ₊₁^{(α,β)}` through `Pₙ^{(α+1,β+1)}` and its derivative. Over the reals it is
the polynomial content of the differentiation formula (DLMF 18.9.16)

`d/dx ((1 - x)^(α+1) (1 + x)^(β+1) Pₙ^{(α+1,β+1)}(x))
  = -2 (n + 1) (1 - x)^α (1 + x)^β Pₙ₊₁^{(α,β)}(x)`,

the inductive step of the Rodrigues formula for the Jacobi polynomials.

The proof expands both sides in the products `(X - 1)^i (X + 1)^k` of the defining sum, indexed by
the antidiagonal `i + k = n`. Multiplying by `(X - 1) (X + 1)` turns the derivative of
`(X - 1)^i (X + 1)^k` into `i (X - 1)^i (X + 1)^(k+1) + k (X - 1)^(i+1) (X + 1)^k`, and the two
resulting families match the two halves of `(n + 1) = i + k` on the antidiagonal of `n + 1`, by
the rising factorial identity `(x)ₖ₊₁ = x (x + 1)ₖ`.

## Main statements

* `Polynomial.X_sub_one_mul_X_add_one_mul_derivative_jacobi_add_one`: the raising relation.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, 18.5.8 (the
  explicit sum) and 18.9.16 (the differentiation formula).
* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, (4.10.1).
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The coefficient of `(X - 1)^i (X + 1)^k` in `2ⁿ Pₙ^{(α,β)}`, for `i + k = n`. -/
private noncomputable def jacobiCoeff (α β : R) (i k : ℕ) : R :=
  algebraMap ℚ R (1 / (i.factorial * k.factorial)) *
    ((ascPochhammer R i).eval (β + k + 1) * (ascPochhammer R k).eval (α + i + 1))

/-- `2ⁿ Pₙ^{(α,β)}` as a sum over the antidiagonal `i + k = n`. -/
private noncomputable def jacobiSum (α β : R) (n : ℕ) : R[X] :=
  ∑ p ∈ antidiagonal n, C (jacobiCoeff α β p.1 p.2) * ((X - 1) ^ p.1 * (X + 1) ^ p.2)

private theorem jacobi_eq_smul_jacobiSum (α β : R) (n : ℕ) :
    jacobi α β n = ((1 : ℚ) / 2 ^ n) • jacobiSum α β n := by
  rw [jacobi_def, jacobiSum, ← Nat.sum_antidiagonal_swap,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  simp only [jacobiCoeff, Prod.swap_prod_mk, ← eval_eq_smeval, Algebra.smul_def,
    algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

omit [Algebra ℚ R] in
/-- Multiplying by `(X - 1) (X + 1)` turns the derivative of `(X - 1)^i (X + 1)^k` into a
combination of `(X - 1)^i (X + 1)^(k+1)` and `(X - 1)^(i+1) (X + 1)^k`. -/
private theorem X_sub_one_mul_X_add_one_mul_derivative_pow_mul_pow (i k : ℕ) :
    (X - 1) * (X + 1) * derivative ((X - 1 : R[X]) ^ i * (X + 1) ^ k) =
      (i : R[X]) * ((X - 1) ^ i * (X + 1) ^ (k + 1)) +
        (k : R[X]) * ((X - 1) ^ (i + 1) * (X + 1) ^ k) := by
  rcases i with _ | i <;> rcases k with _ | k <;>
    simp only [derivative_mul, derivative_pow, derivative_sub, derivative_add, derivative_X,
      derivative_one, C_eq_natCast] <;>
    push_cast <;> ring

/-- The rising factorial identity behind the raising relation, in the variable `k`. -/
private theorem jacobiCoeff_mul_left (α β : R) (i k : ℕ) :
    jacobiCoeff (α + 1) (β + 1) i k * (α + 1 + i) = (k + 1) * jacobiCoeff α β i (k + 1) := by
  have hq : algebraMap ℚ R (1 / (i.factorial * k.factorial)) =
      algebraMap ℚ R (1 / (i.factorial * (k + 1).factorial)) * (k + 1) := by
    rw [Nat.one_div_factorial_mul_factorial_succ_right, map_mul, map_add, map_natCast, map_one]
  have hp : (ascPochhammer R (k + 1)).eval (α + i + 1) =
      (α + i + 1) * (ascPochhammer R k).eval (α + 1 + i + 1) := by
    rw [ascPochhammer_succ_eval, ← ascPochhammer_eval_succ]
    ring_nf
  simp only [jacobiCoeff, hq, hp, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- The rising factorial identity behind the raising relation, in the variable `i`. -/
private theorem jacobiCoeff_mul_right (α β : R) (i k : ℕ) :
    jacobiCoeff (α + 1) (β + 1) i k * (β + 1 + k) = (i + 1) * jacobiCoeff α β (i + 1) k := by
  have hq : algebraMap ℚ R (1 / (i.factorial * k.factorial)) =
      algebraMap ℚ R (1 / ((i + 1).factorial * k.factorial)) * (i + 1) := by
    rw [Nat.one_div_factorial_mul_factorial_succ_left, map_mul, map_add, map_natCast, map_one]
  have hp : (ascPochhammer R (i + 1)).eval (β + k + 1) =
      (β + k + 1) * (ascPochhammer R i).eval (β + 1 + k + 1) := by
    rw [ascPochhammer_succ_eval, ← ascPochhammer_eval_succ]
    ring_nf
  simp only [jacobiCoeff, hq, hp, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- The raising relation for the sums `jacobiSum`, without the powers of `2`. -/
private theorem raising_jacobiSum (α β : R) (n : ℕ) :
    (X - 1) * (X + 1) * derivative (jacobiSum (α + 1) (β + 1) n) +
        (C (β + 1) * (X - 1) + C (α + 1) * (X + 1)) * jacobiSum (α + 1) (β + 1) n =
      (n + 1 : R[X]) * jacobiSum α β (n + 1) := by
  -- split `n + 1 = k + i` on the antidiagonal of `n + 1`, and shift each half to that of `n`
  have hsplit : (n + 1 : R[X]) * jacobiSum α β (n + 1) =
      ∑ p ∈ antidiagonal (n + 1), C (p.2 * jacobiCoeff α β p.1 p.2) *
          ((X - 1) ^ p.1 * (X + 1) ^ p.2) +
        ∑ p ∈ antidiagonal (n + 1), C (p.1 * jacobiCoeff α β p.1 p.2) *
          ((X - 1) ^ p.1 * (X + 1) ^ p.2) := by
    rw [jacobiSum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun p hp => ?_
    have h : ((p.1 + p.2 : ℕ) : R[X]) = n + 1 := by rw [mem_antidiagonal.1 hp]; push_cast; ring
    rw [← h]
    simp only [map_mul, map_natCast, Nat.cast_add]
    ring
  rw [hsplit, Nat.sum_antidiagonal_succ', Nat.sum_antidiagonal_succ, jacobiSum, derivative_sum,
    mul_sum, mul_sum, ← sum_add_distrib]
  simp only [Nat.cast_zero, zero_mul, map_zero, zero_add, ← sum_add_distrib]
  refine sum_congr rfl fun p _ => ?_
  have hd := X_sub_one_mul_X_add_one_mul_derivative_pow_mul_pow (R := R) p.1 p.2
  have hl := congrArg C (jacobiCoeff_mul_left α β p.1 p.2)
  have hr := congrArg C (jacobiCoeff_mul_right α β p.1 p.2)
  simp only [derivative_C_mul, map_mul, map_add, map_one, map_natCast, Nat.cast_add,
    Nat.cast_one] at hd hl hr ⊢
  linear_combination C (jacobiCoeff (α + 1) (β + 1) p.1 p.2) * hd +
    ((X - 1) ^ p.1 * (X + 1) ^ (p.2 + 1)) * hl + ((X - 1) ^ (p.1 + 1) * (X + 1) ^ p.2) * hr

/-- The raising relation of the Jacobi polynomials:
`(X - 1) (X + 1) (Pₙ^{(α+1,β+1)})' + ((β + 1) (X - 1) + (α + 1) (X + 1)) Pₙ^{(α+1,β+1)} =
2 (n + 1) Pₙ₊₁^{(α,β)}`. Over the reals, multiplied by `-(1 - x)^α (1 + x)^β`, it is the
differentiation formula
`d/dx ((1 - x)^(α+1) (1 + x)^(β+1) Pₙ^{(α+1,β+1)}(x)) =
-2 (n + 1) (1 - x)^α (1 + x)^β Pₙ₊₁^{(α,β)}(x)` (DLMF 18.9.16), the inductive step of the Rodrigues
formula. -/
theorem X_sub_one_mul_X_add_one_mul_derivative_jacobi_add_one (α β : R) (n : ℕ) :
    (X - 1) * (X + 1) * derivative (jacobi (α + 1) (β + 1) n) =
      (2 * (n + 1)) • jacobi α β (n + 1) -
        (C (β + 1) * (X - 1) + C (α + 1) * (X + 1)) * jacobi (α + 1) (β + 1) n := by
  have h2 : (2 * (n + 1)) • ((1 : ℚ) / 2 ^ (n + 1)) • jacobiSum α β (n + 1) =
      ((1 : ℚ) / 2 ^ n) • ((n + 1 : R[X]) * jacobiSum α β (n + 1)) := by
    have e : ((n : R[X]) + 1) * jacobiSum α β (n + 1) =
        ((n + 1 : ℕ) : ℚ) • jacobiSum α β (n + 1) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      push_cast
      ring
    rw [e, smul_smul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    congr 1
    push_cast
    field_simp
    ring
  rw [jacobi_eq_smul_jacobiSum, jacobi_eq_smul_jacobiSum, derivative_smul, h2, mul_smul_comm,
    mul_smul_comm, ← smul_sub]
  congr 1
  linear_combination raising_jacobiSum α β n

end Polynomial
