/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.Algebra.NatCast

/-!
# The elementary symmetric polynomials through the power sums

Newton's identities `(n + 1) e_(n + 1) = ∑_{i + j = n} (-1)ʲ eᵢ p_(j + 1)` can be solved for
`e_(n + 1)` once `n + 1` is invertible. Over a `ℚ`-algebra this expresses every elementary
symmetric polynomial as a polynomial in the power sums, by the polynomials `E_n` in the variables
`X r`, which stand for `p_(r + 1)`, determined by `E₀ = 1` and Newton's recursion
`E_(n + 1) = (1 / (n + 1)) ∑_{i + j = n} (-1)ʲ Eᵢ X_j`. Here `1 / (n + 1)` is the image in `R` of a
rational number, so no division is asserted in `R` itself. The polynomial `E_n` is homogeneous of
degree `n` for the weight `X r ↦ r + 1`, does not depend on the coefficient ring, and specialises
in every finite alphabet to Newton's expression of `e_n` through the power sums. Over `ℤ` no such
polynomial exists: `p₁² - p₂ = 2 e₂`.

## Main definitions

* `TauCeti.esymmPsumPoly R n`: for a `ℚ`-algebra `R`, the polynomial `E_n`
  expressing `e_n` through the power sums.

## Main results

* `TauCeti.mul_esymm_succ_eq_sum`: **Newton's identities** in the form
  `(n + 1) e_(n + 1) = ∑_{i + j = n} (-1)ʲ eᵢ p_(j + 1)`.
* `TauCeti.esymmPsumPoly_succ`,
  `TauCeti.mul_esymmPsumPoly_succ`: Newton's recursion for `E_n`.
* `TauCeti.aeval_psum_esymmPsumPoly`: in a finite alphabet, `E_n` evaluated at
  the power sums is the elementary symmetric polynomial `e_n`.
* `TauCeti.map_esymmPsumPoly`: `E_n` is natural in the coefficient ring.
* `TauCeti.isWeightedHomogeneous_esymmPsumPoly`: `E_n` has weighted degree `n`
  for the weight `X r ↦ r + 1`.
* `TauCeti.two_mul_esymmPsumPoly_two`,
  `TauCeti.six_mul_esymmPsumPoly_three`: `2 E₂ = X₀² - X₁` and
  `6 E₃ = X₀³ - 3 X₀ X₁ + 2 X₂`, representing `2 e₂ = p₁² - p₂` and
  `6 e₃ = p₁³ - 3 p₁ p₂ + 2 p₃`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2: Newton's identities (2.11′) and the expression of `e_n` through the power sums
  (2.14′).
-/

public section

namespace TauCeti

open MvPolynomial Finset

/-- **Newton's identities** in a finite alphabet, indexed by the antidiagonal of `n`:
`(n + 1) e_(n + 1) = ∑_{i + j = n} (-1)ʲ eᵢ p_(j + 1)`. This is
`MvPolynomial.mul_esymm_eq_sum` with the term `i = n + 1` removed and the signs collected. -/
theorem mul_esymm_succ_eq_sum (σ : Type*) [Fintype σ] (R : Type*) [CommRing R] (n : ℕ) :
    ((n : MvPolynomial σ R) + 1) * esymm σ R (n + 1) =
      ∑ x ∈ antidiagonal n, (-1) ^ x.2 * esymm σ R x.1 * psum σ R (x.2 + 1) := by
  have h := MvPolynomial.mul_esymm_eq_sum σ R (n + 1)
  rw [sum_filter, Nat.sum_antidiagonal_succ', mul_add, mul_sum] at h
  simp only [lt_irrefl, ↓reduceIte, mul_zero, zero_add, Nat.cast_add, Nat.cast_one] at h
  rw [h]
  refine sum_congr rfl fun x hx => ?_
  rw [mem_antidiagonal] at hx
  subst hx
  simp only [show x.1 < x.1 + x.2 + 1 by omega, ↓reduceIte]
  rw [← mul_assoc, ← mul_assoc, ← pow_add,
    show x.1 + x.2 + 1 + 1 + x.1 = x.2 + 2 * (x.1 + 1) by ring, pow_add, pow_mul]
  simp

section

variable (R : Type*) [CommRing R] [Algebra ℚ R]

/-- The polynomial `E_n` in the variables `X r`, standing for the power sums `p_(r + 1)`, which
expresses the elementary symmetric function `e_n` over a `ℚ`-algebra: `E₀ = 1` and
`E_(n + 1) = (1 / (n + 1)) ∑_{i + j = n} (-1)ʲ Eᵢ X_j`, Newton's recursion. -/
noncomputable def esymmPsumPoly : ℕ → MvPolynomial ℕ R
  | 0 => 1
  | n + 1 => algebraMap ℚ R ((n : ℚ) + 1)⁻¹ •
      ∑ x ∈ (antidiagonal n).attach, (-1) ^ x.1.2 * esymmPsumPoly x.1.1 * X x.1.2
decreasing_by
  have := Nat.antidiagonal.fst_lt x.2
  omega

@[simp]
theorem esymmPsumPoly_zero : esymmPsumPoly R 0 = 1 := by
  rw [esymmPsumPoly]

/-- **Newton's recursion** for `TauCeti.esymmPsumPoly`. -/
theorem esymmPsumPoly_succ (n : ℕ) :
    esymmPsumPoly R (n + 1) = algebraMap ℚ R ((n : ℚ) + 1)⁻¹ •
      ∑ x ∈ antidiagonal n, (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2 := by
  rw [esymmPsumPoly]
  congr 1
  exact sum_attach (antidiagonal n) fun x => (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2

/-- Newton's recursion for `TauCeti.esymmPsumPoly` with the denominator cleared:
`(n + 1) E_(n + 1) = ∑_{i + j = n} (-1)ʲ Eᵢ X_j`. -/
theorem mul_esymmPsumPoly_succ (n : ℕ) :
    (n + 1 : MvPolynomial ℕ R) * esymmPsumPoly R (n + 1) =
      ∑ x ∈ antidiagonal n, (-1) ^ x.2 * esymmPsumPoly R x.1 * X x.2 := by
  rw [esymmPsumPoly_succ, natCast_add_one_mul_algebraMap_inv_smul]

@[simp]
theorem esymmPsumPoly_one : esymmPsumPoly R 1 = X 0 := by
  simp [esymmPsumPoly_succ]

/-- `2 E₂ = X₀² - X₁`, representing `2 e₂ = p₁² - p₂` under `X r ↦ p_(r + 1)`. -/
theorem two_mul_esymmPsumPoly_two : 2 * esymmPsumPoly R 2 = X 0 ^ 2 - X 1 := by
  have h := mul_esymmPsumPoly_succ R 1
  norm_num [Nat.antidiagonal_succ] at h
  linear_combination h

/-- `6 E₃ = X₀³ - 3 X₀ X₁ + 2 X₂`, representing `6 e₃ = p₁³ - 3 p₁ p₂ + 2 p₃` under
`X r ↦ p_(r + 1)`. -/
theorem six_mul_esymmPsumPoly_three :
    6 * esymmPsumPoly R 3 = X 0 ^ 3 - 3 * X 0 * X 1 + 2 * X 2 := by
  have h := mul_esymmPsumPoly_succ R 2
  norm_num [Nat.antidiagonal_succ] at h
  linear_combination 2 * h + X 0 * two_mul_esymmPsumPoly_two R

/-- In a finite alphabet, `E_n` evaluated at the power sums `p₁, p₂, …` is the elementary
symmetric polynomial `e_n`. -/
theorem aeval_psum_esymmPsumPoly (σ : Type*) [Fintype σ] (n : ℕ) :
    aeval (fun r => psum σ R (r + 1)) (esymmPsumPoly R n) = esymm σ R n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain _ | n := n
    · simp
    refine (isUnit_natCast_add_one (K := MvPolynomial σ R) n).mul_left_cancel ?_
    rw [esymmPsumPoly_succ, map_smul, natCast_add_one_mul_algebraMap_inv_smul, map_sum,
      mul_esymm_succ_eq_sum]
    refine sum_congr rfl fun x hx => ?_
    rw [map_mul, map_mul, map_pow, map_neg, map_one, aeval_X,
      ih x.1 (Nat.antidiagonal.fst_lt hx)]

/-- **`E_n` does not depend on the coefficient ring**: it is natural in ring homomorphisms between
`ℚ`-algebras. -/
@[simp]
theorem map_esymmPsumPoly {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) (n : ℕ) :
    map f (esymmPsumPoly R n) = esymmPsumPoly S n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain _ | n := n
    · simp
    rw [esymmPsumPoly_succ, esymmPsumPoly_succ, smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C,
      RingHom.map_rat_algebraMap, map_sum]
    congr 1
    refine sum_congr rfl fun x hx => ?_
    rw [map_mul, map_mul, map_pow, map_neg, map_one, map_X,
      ih x.1 (Nat.antidiagonal.fst_lt hx)]

/-- `E_n` is homogeneous of degree `n` for the weight `X r ↦ r + 1`. -/
theorem isWeightedHomogeneous_esymmPsumPoly (n : ℕ) :
    IsWeightedHomogeneous (· + 1) (esymmPsumPoly R n) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain _ | n := n
    · simpa using isWeightedHomogeneous_one R (· + 1)
    rw [esymmPsumPoly_succ, smul_eq_C_mul]
    refine IsWeightedHomogeneous.C_mul (IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_) _
    have hx' := mem_antidiagonal.mp hx
    have h := (((isWeightedHomogeneous_one R (· + 1)).neg.pow x.2).mul
      (ih x.1 (Nat.antidiagonal.fst_lt hx))).mul (isWeightedHomogeneous_X R (· + 1) x.2)
    convert h using 1
    simp only [smul_zero, zero_add]
    omega

end

end TauCeti
