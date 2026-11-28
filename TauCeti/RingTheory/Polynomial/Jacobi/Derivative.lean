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
import TauCeti.Algebra.Polynomial.Derivative

/-!
# The derivative and the raising relation of the Jacobi polynomials

For the Jacobi polynomials `Pₙ^{(α,β)} = Polynomial.jacobi α β n` over a commutative `ℚ`-algebra
this file proves the derivative formula (DLMF 18.9.15)

`(Pₙ₊₁^{(α,β)})' = ((n + α + β + 2) / 2) Pₙ^{(α+1,β+1)}`

and the raising relation

`(X - 1) (X + 1) (Pₙ^{(α+1,β+1)})' + ((β + 1) (X - 1) + (α + 1) (X + 1)) Pₙ^{(α+1,β+1)}
  = 2 (n + 1) Pₙ₊₁^{(α,β)}`,

which expresses `Pₙ₊₁^{(α,β)}` through `Pₙ^{(α+1,β+1)}` and its derivative. Over the reals it is
the polynomial content of the differentiation formula (DLMF 18.9.16)

`d/dx ((1 - x)^(α+1) (1 + x)^(β+1) Pₙ^{(α+1,β+1)}(x))
  = -2 (n + 1) (1 - x)^α (1 + x)^β Pₙ₊₁^{(α,β)}(x)`,

the inductive step of the Rodrigues formula for the Jacobi polynomials.

Both proofs are termwise computations in the products `(X - 1)^i (X + 1)^k` of the defining sum,
and both reduce to the coefficient identities `Polynomial.jacobiCoeff_mul_left` and
`Polynomial.jacobiCoeff_mul_right`. For the derivative formula, the derivative of a combination of
the products of total degree `n + 1` is re-expanded in the products of total degree `n` by
`Polynomial.derivative_sum_smul_X_add_C_pow_mul_X_add_C_pow`, and the resulting coefficient
identity is the sum of the two coefficient identities.

The proof of the raising relation expands both sides in these products, indexed by the
antidiagonal `i + k = n`. Multiplying by `(X - 1) (X + 1)` turns the derivative of
`(X - 1)^i (X + 1)^k` into `i (X - 1)^i (X + 1)^(k+1) + k (X - 1)^(i+1) (X + 1)^k`, and the two
resulting families match the two halves of `(n + 1) = i + k` on the antidiagonal of `n + 1`, one
coefficient identity for each half.

## Main statements

* `Polynomial.derivative_jacobi`: the derivative of the polynomial of index `n + 1` is a scalar
  multiple of the polynomial of index `n` with both parameters raised by one. It is a `simp`
  lemma: derivatives of Jacobi polynomials of positive index are rewritten to Jacobi polynomials.
* `Polynomial.X_sub_one_mul_X_add_one_mul_derivative_jacobi_add_one`: the raising relation.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, 18.5.8 (the
  explicit sum), 18.9.15 (the derivative) and 18.9.16 (the differentiation formula).
* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, (4.10.1).
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-! ### The derivative -/

/-- The coefficient identity behind `Polynomial.derivative_jacobi`: the sum of
`Polynomial.jacobiCoeff_mul_right` and `Polynomial.jacobiCoeff_mul_left` at the indices `(m, k)`. -/
private lemma derivative_jacobi_coeff (α β : R) (m k : ℕ) :
    ((m : R) + 1) * jacobiCoeff α β (m + 1) k + ((k : R) + 1) * jacobiCoeff α β m (k + 1) =
      ((m + k : ℕ) + α + β + 2) * jacobiCoeff (α + 1) (β + 1) m k := by
  push_cast
  linear_combination -jacobiCoeff_mul_right α β m k - jacobiCoeff_mul_left α β m k

/-- The derivative of the Jacobi polynomial of index `n + 1` is a scalar multiple of the Jacobi
polynomial of index `n` with both parameters raised by one:
`(Pₙ₊₁^{(α,β)})' = ((n + α + β + 2) / 2) Pₙ^{(α+1,β+1)}` (DLMF 18.9.15). The scalar vanishes for
`α + β = -(n + 2)`, where `Pₙ₊₁^{(α,β)}` is constant. -/
@[simp]
theorem derivative_jacobi (α β : R) (n : ℕ) :
    derivative (jacobi α β (n + 1)) =
      ((1 : ℚ) / 2) • (C (n + α + β + 2) * jacobi (α + 1) (β + 1) n) := by
  -- The shifted-power rule at the shifts `-1` and `1`, whose products are those of `jacobi_def`.
  have hd := fun f : ℕ → R => derivative_sum_smul_X_add_C_pow_mul_X_add_C_pow (-1) 1 f n
  simp only [C_1, C_neg, ← sub_eq_add_neg] at hd
  -- One factor `1 / 2` of the normalization `1 / 2 ^ (n + 1)` stays in front.
  have h2 : (1 : ℚ) / 2 ^ (n + 1) = 1 / 2 * (1 / 2 ^ n) := by ring
  -- Expand the derivative in the shifted powers of index `n`.
  rw [jacobi_eq_smul_sum_jacobiCoeff, jacobi_eq_smul_sum_jacobiCoeff, derivative_smul, hd]
  -- Collect the scalars; what remains is a termwise comparison of coefficients.
  rw [mul_smul_comm, smul_smul, ← smul_eq_C_mul, h2]
  congr 1
  rw [smul_sum]
  refine sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.lt_succ_iff.1 (mem_range.1 hk))
  -- With `n = m + k`, the exponent `n + 1 - k` of `X - 1` at index `n + 1` is `m + 1`.
  have hexp : m + k + 1 - k = m + 1 := by omega
  simp only [hexp, Nat.add_sub_add_right, Nat.add_sub_cancel, smul_smul]
  rw [← derivative_jacobi_coeff]

/-! ### The raising relation -/

/-- `2ⁿ Pₙ^{(α,β)}` as a sum over the antidiagonal `i + k = n`. -/
private noncomputable def jacobiSum (α β : R) (n : ℕ) : R[X] :=
  ∑ p ∈ antidiagonal n, C (jacobiCoeff α β p.1 p.2) * ((X - 1) ^ p.1 * (X + 1) ^ p.2)

private theorem jacobi_eq_smul_jacobiSum (α β : R) (n : ℕ) :
    jacobi α β n = ((1 : ℚ) / 2 ^ n) • jacobiSum α β n := by
  rw [jacobi_eq_smul_sum_jacobiCoeff, jacobiSum, ← Nat.sum_antidiagonal_swap,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.swap_prod_mk, smul_eq_C_mul]

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
