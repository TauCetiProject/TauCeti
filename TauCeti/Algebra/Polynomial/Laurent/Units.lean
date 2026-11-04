/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.LinearCombination

/-!
# Units of Laurent polynomials

A constant Laurent polynomial `C r` is a unit exactly when its coefficient `r` is a unit. The map
`C` is Mathlib's `AddMonoidAlgebra.singleZeroRingHom`, which is a local ring homomorphism. This is
the Laurent counterpart of Mathlib's `Polynomial.isUnit_C`.

Over a commutative ring without zero divisors, every unit of `R[T;T⁻¹]` is a unit monomial
`C r * T n`. This is the Laurent counterpart of Mathlib's `Polynomial.isUnit_iff`, where only
the constants survive. Over `ℤ` it says that the units of `ℤ[T;T⁻¹]` are exactly `±Tⁿ`, which is
the form taken by a unimodular determinant over the Laurent ring.

## Main results

* `LaurentPolynomial.isUnit_C`: `C r` is a unit if and only if `r` is.
* `LaurentPolynomial.isUnit_iff`: over a commutative ring without zero divisors, the units of
  `R[T;T⁻¹]` are the monomials `C r * T n` with `r` a unit.
* `LaurentPolynomial.isUnit_iff_exists_eq_T_or_neg_T`: the units of `ℤ[T;T⁻¹]` are the `±Tⁿ`.
-/

public section

namespace LaurentPolynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- A constant Laurent polynomial is a unit exactly when its coefficient is. -/
@[simp]
theorem isUnit_C {r : R} : IsUnit (C r : R[T;T⁻¹]) ↔ IsUnit r :=
  isUnit_map_iff (AddMonoidAlgebra.singleZeroRingHom (R := R) (M := ℤ)) r

end Semiring

section CommRing

variable [CommRing R] [NoZeroDivisors R]

/-- **Units of a Laurent polynomial ring.** Over a commutative ring without zero divisors, a
Laurent polynomial is a unit exactly when it is a unit monomial `C r * T n`. -/
theorem isUnit_iff {f : R[T;T⁻¹]} : IsUnit f ↔ ∃ r : R, IsUnit r ∧ ∃ n : ℤ, C r * T n = f := by
  refine ⟨fun hf => ?_, fun ⟨r, hr, n, hf⟩ => hf ▸ (isUnit_C.2 hr).mul (isUnit_T n)⟩
  nontriviality R
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  obtain ⟨g, hfg⟩ := hf.exists_right_inv
  obtain ⟨m, f', hf'⟩ := f.exists_T_pow
  obtain ⟨n, g', hg'⟩ := g.exists_T_pow
  -- Clearing denominators turns `f * g = 1` into `f' * g' = X ^ (m + n)` in `R[X]`.
  have hX : f' * g' = Polynomial.X ^ (m + n) := by
    apply Polynomial.toLaurent_injective
    simp only [map_mul, hf', hg', Polynomial.toLaurent_X_pow, Nat.cast_add, T_add]
    linear_combination (T m * T n) * hfg
  -- As `X` is prime in `R[X]`, `f'` is a power of `X` times a unit, and that unit is constant.
  obtain ⟨i, -, u, hu⟩ := (dvd_prime_pow Polynomial.prime_X _).1 (Dvd.intro _ hX)
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 (u⁻¹).isUnit
  refine ⟨r, hr, i - m, ?_⟩
  have hf'_eq : f' = Polynomial.C r * Polynomial.X ^ i := by
    rw [hru, ← hu, mul_comm, Units.mul_inv_cancel_right]
  have hfT : f * T m = C r * T i := by
    rw [← hf', hf'_eq, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow]
  calc C r * T (i - m) = f * T m * T (-m) := by rw [hfT, mul_T_assoc, sub_eq_add_neg]
    _ = f := by rw [mul_T_assoc, add_neg_cancel, T_zero, mul_one]

end CommRing

/-- **Units of `ℤ[T;T⁻¹]`.** An integral Laurent polynomial is a unit exactly when it is `Tⁿ` or
`-Tⁿ` for some `n : ℤ`. -/
theorem isUnit_iff_exists_eq_T_or_neg_T {f : ℤ[T;T⁻¹]} :
    IsUnit f ↔ ∃ n : ℤ, f = T n ∨ f = -T n := by
  rw [isUnit_iff]
  constructor
  · rintro ⟨r, hr, n, rfl⟩
    rcases Int.isUnit_iff.1 hr with rfl | rfl
    · exact ⟨n, .inl (by simp)⟩
    · exact ⟨n, .inr (by simp)⟩
  · rintro ⟨n, rfl | rfl⟩
    · exact ⟨1, isUnit_one, n, by simp⟩
    · exact ⟨-1, isUnit_one.neg, n, by simp⟩

end LaurentPolynomial
