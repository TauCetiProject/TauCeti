/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Jacobi.Basic
public import Mathlib.Algebra.Polynomial.Derivative

import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Algebra.NatCast
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.Data.Nat.Factorial.Field
import TauCeti.RingTheory.Polynomial.Pochhammer

/-!
# Derivative and recurrences of the Jacobi polynomials

For the Jacobi polynomials `Pₙ^{(α,β)} = Polynomial.jacobi α β n` over a commutative `ℚ`-algebra,
with arbitrary parameters `α β`, this file proves the identities that relate neighbouring indices
`n` and neighbouring parameters. The index `n` bounds the degree of `Pₙ^{(α,β)}` but need not equal
it: for special parameters the leading coefficient vanishes. Each identity is stated with its
coefficients on the polynomial side, so that no division occurs. It is an identity between the
displayed weighted polynomials; it isolates an unweighted polynomial only when the coefficient in
front of that polynomial can be cancelled.

* `Polynomial.derivative_jacobi`: the derivative of the polynomial of index `n + 1` is a scalar
  multiple of the polynomial of index `n` with both parameters raised by one. It is a `simp`
  lemma: derivatives of Jacobi polynomials of positive index are rewritten to Jacobi polynomials.
* `Polynomial.jacobi_succ_contiguous_right` and `Polynomial.jacobi_succ_contiguous_left` equate
  `(2n + α + β + 3) Pₙ₊₁^{(α,β)}` with a combination of the polynomials of indices `n + 1` and `n`
  in which `β`, respectively `α`, is raised by one.
* `Polynomial.C_mul_X_add_one_mul_jacobi_add_one_right` goes the other way in `β`: it equates
  `(2n + α + β + 2) (X + 1) Pₙ^{(α,β+1)}` with a combination of the polynomials of indices `n + 1`
  and `n` at the parameters `(α, β)`.
* `Polynomial.jacobi_succ_succ` keeps both parameters fixed and relates three consecutive indices.

The relations with `α` and `β` exchanged follow by the reflection `Polynomial.jacobi_comp_neg_X`,
as `Polynomial.jacobi_succ_contiguous_left` does from `Polynomial.jacobi_succ_contiguous_right`.

The three-term recurrence holds for all parameters, whatever its leading coefficient
`c = 2 (n + 2) (n + α + β + 2) (2n + α + β + 2)` is. How much it says about `Pₙ₊₂^{(α,β)}` depends
on `c`. If `c` is a unit of the base ring, the recurrence can be solved for `Pₙ₊₂^{(α,β)}` by
multiplying by the inverse of `c`. If multiplication by `c` is only injective, that inverse is not
available, but `Pₙ₊₂^{(α,β)}` is still the unique polynomial satisfying the recurrence, by
cancellation. If `c` is a zero divisor, for instance `c = 0` for `α + β = -(n + 2)`, the
recurrence is still a valid identity but no longer determines `Pₙ₊₂^{(α,β)}`.

## Main results

* `Polynomial.derivative_jacobi`: `(Pₙ₊₁^{(α,β)})' = ((n + α + β + 2) / 2) Pₙ^{(α+1,β+1)}`
  (DLMF 18.9.15).
* `Polynomial.jacobi_succ_contiguous_right`, `Polynomial.jacobi_succ_contiguous_left`: the
  contiguous relations equating `(2n + α + β + 3) Pₙ₊₁^{(α,β)}` with a combination of the
  polynomials with `β`, respectively `α`, raised by one (DLMF 18.9.5 and its reflection).
* `Polynomial.C_mul_X_add_one_mul_jacobi_add_one_right`: the contiguous relation equating
  `(2n + α + β + 2) (X + 1) Pₙ^{(α,β+1)}` with a combination of `Pₙ₊₁^{(α,β)}` and `Pₙ^{(α,β)}`
  (DLMF 18.9.6).
* `Polynomial.jacobi_succ_succ`: the three-term recurrence (DLMF 18.9.1, 18.9.2).

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov/18>: 18.9.1,
  18.9.2, 18.9.5, 18.9.6, 18.9.15.
* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, Chapter IV.
-/

public section

open Finset

namespace Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-! ### The derivative -/

/-- The coefficient identity behind `Polynomial.derivative_jacobi`. -/
private lemma derivative_jacobi_coeff (α β : R) (m k : ℕ) :
    ((m : R) + 1) * (((1 : ℚ) / ((m + 1).factorial * k.factorial)) •
        ((ascPochhammer R (m + 1)).smeval (β + k + 1) *
          (ascPochhammer R k).smeval (α + (m + 1 : ℕ) + 1))) +
      ((k : R) + 1) * (((1 : ℚ) / (m.factorial * (k + 1).factorial)) •
        ((ascPochhammer R m).smeval (β + (k + 1 : ℕ) + 1) *
          (ascPochhammer R (k + 1)).smeval (α + m + 1))) =
      ((m + k : ℕ) + α + β + 2) * (((1 : ℚ) / (m.factorial * k.factorial)) •
        ((ascPochhammer R m).smeval (β + 1 + k + 1) *
          (ascPochhammer R k).smeval (α + 1 + m + 1))) := by
  have h₁ := congrArg (algebraMap ℚ R) (Nat.one_div_factorial_mul_factorial_succ_left (K := ℚ) m k)
  have h₂ := congrArg (algebraMap ℚ R) (Nat.one_div_factorial_mul_factorial_succ_right (K := ℚ) m k)
  simp only [map_mul, map_add, map_natCast, map_one] at h₁ h₂
  -- Peeling the first factor off a rising factorial: `(x)ₙ₊₁ = x (x + 1)ₙ`.
  have hp (n : ℕ) (x : R) :
      (ascPochhammer R (n + 1)).eval x = x * (ascPochhammer R n).eval (x + 1) := by
    rw [add_comm n 1, TauCeti.ascPochhammer_add_eval, ascPochhammer_one, eval_X, Nat.cast_one]
  -- After the first factor is peeled off the two rising factorials of length `m + 1` and `k + 1`,
  -- every rising factorial is evaluated at `β + k + 2` or at `α + m + 2`. These four equalities
  -- bring the arguments, which the two sides write differently, to one common form.
  have hα : α + ((m + 1 : ℕ) : R) + 1 = α + m + 1 + 1 := by push_cast; ring
  have hβ : β + ((k + 1 : ℕ) : R) + 1 = β + k + 1 + 1 := by push_cast; ring
  have hβ' : β + 1 + (k : R) + 1 = β + k + 1 + 1 := by ring
  have hα' : α + 1 + (m : R) + 1 = α + m + 1 + 1 := by ring
  simp only [← eval_eq_smeval, hp, hα, hβ, hβ', hα']
  simp only [Algebra.smul_def, Nat.cast_add]
  linear_combination
    -((β + k + 1) * (ascPochhammer R m).eval (β + k + 1 + 1) *
        (ascPochhammer R k).eval (α + m + 1 + 1)) * h₁ -
      (α + m + 1) * (ascPochhammer R m).eval (β + k + 1 + 1) *
        (ascPochhammer R k).eval (α + m + 1 + 1) * h₂

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
  rw [jacobi_def, jacobi_def, derivative_smul, hd]
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

/-! ### Contiguous relations -/

/-- The two sides of `Polynomial.jacobi_succ_contiguous_right` have the same value at `1`. -/
private lemma eval_one_jacobi_succ_contiguous_right (α β : R) (n : ℕ) :
    eval 1 (C (2 * n + α + β + 3) * jacobi α β (n + 1)) =
      eval 1 (C (n + α + β + 2) * jacobi α (β + 1) (n + 1) +
        C (n + 1 + α) * jacobi α (β + 1) n) := by
  simp only [eval_mul, eval_add, eval_C, eval_one_jacobi, Algebra.smul_def, ← eval_eq_smeval,
    ascPochhammer_succ_eval, Nat.algebraMap_one_div_factorial_eq_mul (K := ℚ) (A := R) n]
  ring

/-- A contiguous relation of the Jacobi polynomials, raising `β` (DLMF 18.9.5):
`(2n + α + β + 3) Pₙ₊₁^{(α,β)} = (n + α + β + 2) Pₙ₊₁^{(α,β+1)} + (n + 1 + α) Pₙ^{(α,β+1)}`. -/
theorem jacobi_succ_contiguous_right (α β : R) (n : ℕ) :
    C (2 * n + α + β + 3) * jacobi α β (n + 1) =
      C (n + α + β + 2) * jacobi α (β + 1) (n + 1) + C (n + 1 + α) * jacobi α (β + 1) n := by
  have : HasUniqueDiv R := .of_module_rat R
  induction n generalizing α β with
  | zero =>
    refine eq_of_derivative_eq_of_eval_eq 1 ?_ (eval_one_jacobi_succ_contiguous_right α β 0)
    simp only [derivative_mul, derivative_add, derivative_C, derivative_one, derivative_jacobi,
      jacobi_zero, Algebra.smul_def]
    simp only [map_add, map_mul, map_ofNat, map_one, map_zero, Nat.cast_zero]
    ring
  | succ n ih =>
    refine eq_of_derivative_eq_of_eval_eq 1 ?_
      (eval_one_jacobi_succ_contiguous_right α β (n + 1))
    have ih' := ih (α + 1) (β + 1)
    simp only [derivative_mul, derivative_add, derivative_C, derivative_jacobi,
      Algebra.smul_def]
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add,
      Nat.cast_one] at ih' ⊢
    linear_combination (algebraMap ℚ R[X] (1 / 2) * (C α + C β + n + 3)) * ih'

/-- A contiguous relation of the Jacobi polynomials, raising `α` (the reflection of
DLMF 18.9.5):
`(2n + α + β + 3) Pₙ₊₁^{(α,β)} = (n + α + β + 2) Pₙ₊₁^{(α+1,β)} - (n + 1 + β) Pₙ^{(α+1,β)}`.
It is `Polynomial.jacobi_succ_contiguous_right` for the exchanged parameters, composed with `-X`:
by `Polynomial.jacobi_comp_neg_X` the two terms of index `n + 1` acquire the sign `(-1) ^ (n + 1)`
and the term of index `n` the opposite sign. -/
theorem jacobi_succ_contiguous_left (α β : R) (n : ℕ) :
    C (2 * n + α + β + 3) * jacobi α β (n + 1) =
      C (n + α + β + 2) * jacobi (α + 1) β (n + 1) - C (n + 1 + β) * jacobi (α + 1) β n := by
  have h := congrArg (fun p : R[X] => p.comp (-X)) (jacobi_succ_contiguous_right β α n)
  simp only [mul_comp, add_comp, C_comp, jacobi_comp_neg_X, pow_succ, smul_eq_C_mul] at h
  -- The common sign `(-1) ^ n` is `1` or `-1`, and cancels in either case.
  rcases neg_one_pow_eq_or R n with hs | hs <;>
    simp only [hs, map_add, map_mul, map_neg, map_natCast, map_ofNat, map_one] at h ⊢
  · linear_combination -h
  · linear_combination h

/-- The two sides of `Polynomial.C_mul_X_add_one_mul_jacobi_add_one_right` have the same value
at `1`. -/
private lemma eval_one_C_mul_X_add_one_mul_jacobi_add_one_right (α β : R) (n : ℕ) :
    eval 1 (C (2 * n + α + β + 2) * (X + 1) * jacobi α (β + 1) n) =
      eval 1 (C (2 * ((n : R) + 1)) * jacobi α β (n + 1) + C (2 * (n + β + 1)) * jacobi α β n) := by
  simp only [eval_mul, eval_add, eval_C, eval_X, eval_one, eval_one_jacobi, Algebra.smul_def,
    ← eval_eq_smeval, ascPochhammer_succ_eval,
    Nat.algebraMap_one_div_factorial_eq_mul (K := ℚ) (A := R) n]
  ring

/-- A contiguous relation of the Jacobi polynomials, lowering `β` (DLMF 18.9.6):
`(2n + α + β + 2) (X + 1) Pₙ^{(α,β+1)} = 2 (n + 1) Pₙ₊₁^{(α,β)} + 2 (n + β + 1) Pₙ^{(α,β)}`. -/
theorem C_mul_X_add_one_mul_jacobi_add_one_right (α β : R) (n : ℕ) :
    C (2 * n + α + β + 2) * (X + 1) * jacobi α (β + 1) n =
      C (2 * ((n : R) + 1)) * jacobi α β (n + 1) + C (2 * (n + β + 1)) * jacobi α β n := by
  have : HasUniqueDiv R := .of_module_rat R
  have hH : (2 : R[X]) * algebraMap ℚ R[X] (1 / 2) = 1 := by
    rw [one_div]
    exact TauCeti.ofNat_mul_algebraMap_inv two_ne_zero
  induction n generalizing α β with
  | zero =>
    refine eq_of_derivative_eq_of_eval_eq 1 ?_
      (eval_one_C_mul_X_add_one_mul_jacobi_add_one_right α β 0)
    simp only [derivative_mul, derivative_add, derivative_C, derivative_X, derivative_one,
      derivative_jacobi, jacobi_zero, Algebra.smul_def]
    simp only [map_add, map_mul, map_ofNat, map_one, map_zero, Nat.cast_zero]
    linear_combination (-(C α + C β + 2)) * hH
  | succ n ih =>
    refine eq_of_derivative_eq_of_eval_eq 1 ?_
      (eval_one_C_mul_X_add_one_mul_jacobi_add_one_right α β (n + 1))
    have ih' := ih (α + 1) (β + 1)
    have hA := jacobi_succ_contiguous_left α (β + 1) n
    simp only [derivative_mul, derivative_add, derivative_C, derivative_X, derivative_one,
      derivative_jacobi, Algebra.smul_def]
    simp only [map_add, map_mul, map_natCast, map_ofNat, map_one, Nat.cast_add,
      Nat.cast_one] at ih' hA ⊢
    linear_combination hA + (algebraMap ℚ R[X] (1 / 2) * (C α + C β + n + 3)) * ih' +
      (-(C α + C β + n + 3) * jacobi (α + 1) (β + 1) (n + 1) +
        ((n : R[X]) + C β + 2) * jacobi (α + 1) (β + 1) n) * hH

/-! ### The three-term recurrence -/

/-- The three-term recurrence of the Jacobi polynomials (DLMF 18.9.1, 18.9.2):
`2 (n + 2) (n + α + β + 2) (2n + α + β + 2) Pₙ₊₂^{(α,β)} =
(2n + α + β + 3) ((2n + α + β + 4) (2n + α + β + 2) X + α² - β²) Pₙ₊₁^{(α,β)} -
2 (n + 1 + α) (n + 1 + β) (2n + α + β + 4) Pₙ^{(α,β)}`.
As for the Laguerre polynomials in `Polynomial.laguerre_succ_succ`, the recurrence is a linear
combination of contiguous relations in which the polynomials with a shifted parameter cancel. -/
theorem jacobi_succ_succ (α β : R) (n : ℕ) :
    C (2 * (n + 2) * (n + α + β + 2) * (2 * n + α + β + 2)) * jacobi α β (n + 2) =
      C (2 * n + α + β + 3) *
          (C ((2 * n + α + β + 4) * (2 * n + α + β + 2)) * X + C (α ^ 2 - β ^ 2)) *
          jacobi α β (n + 1) -
        C (2 * (n + 1 + α) * (n + 1 + β) * (2 * n + α + β + 4)) * jacobi α β n := by
  have hA := jacobi_succ_contiguous_right α β n
  have hB₁ := C_mul_X_add_one_mul_jacobi_add_one_right α β (n + 1)
  have hB₀ := C_mul_X_add_one_mul_jacobi_add_one_right α β n
  simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat, map_one, Nat.cast_add,
    Nat.cast_one] at hA hB₁ hB₀ ⊢
  linear_combination
    (-(X + 1) * (2 * n + C α + C β + 4) * (2 * n + C α + C β + 2)) * hA -
      (n + C α + C β + 2) * (2 * n + C α + C β + 2) * hB₁ -
      (n + 1 + C α) * (2 * n + C α + C β + 4) * hB₀

end Polynomial
