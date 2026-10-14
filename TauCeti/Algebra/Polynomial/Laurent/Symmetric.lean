/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Symmetric Laurent polynomials

A Laurent polynomial fixed by inversion is a polynomial in `T + T⁻¹`, over any
commutative ring. The proof uses Mathlib's rescaled Chebyshev polynomials, which
express `Tⁿ + T⁻ⁿ` without dividing by two. Consequently the result applies to
integer coefficients and to rings of characteristic two.

The shifted generator `T + T⁻¹ - 2` is convenient for converting a symmetric
Alexander polynomial to the square of the Conway variable.
-/

public section

noncomputable section

open LaurentPolynomial
open scoped Polynomial

namespace Polynomial.Chebyshev

variable {R : Type*} [CommRing R]

/-- The rescaled Chebyshev polynomial expresses a pair of opposite Laurent powers. -/
@[simp] theorem eval₂_C_add_T_neg (n : ℕ) :
    Polynomial.eval₂ LaurentPolynomial.C
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : R[T;T⁻¹]) (C R n) =
      LaurentPolynomial.T (n : ℤ) + LaurentPolynomial.T (-(n : ℤ)) := by
  induction n using Nat.twoStepInduction with
  | zero => simp; ring
  | one => simp
  | more n h₀ h₁ =>
    have hrec := C_add_two R (n : ℤ)
    push_cast
    push_cast at h₁
    rw [hrec, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, h₁, h₀]
    simp only [mul_add, add_mul, ← T_add]
    have hpos : (1 : ℤ) + (n + 1) = n + 2 := by omega
    have hneg : (-1 : ℤ) + -(n + 1) = -(n + 2) := by omega
    have hleft : (1 : ℤ) + -(n + 1) = -n := by omega
    have hright : (-1 : ℤ) + (n + 1) = n := by omega
    rw [hpos, hneg, hleft, hright]
    ring

end Polynomial.Chebyshev

namespace LaurentPolynomial

/-- Truncation retains every coefficient of nonnegative exponent. -/
@[simp] theorem coeff_trunc [Semiring R] (p : R[T;T⁻¹]) (n : ℕ) :
    (trunc p).coeff n = p.coeff (n : ℤ) := (rfl)

variable {R : Type*} [CommRing R]

/-- Split a Laurent polynomial into its nonnegative and negative powers, correcting
the double-counted constant term. -/
@[simp] theorem toLaurent_trunc_add_invert (p : R[T;T⁻¹]) :
    (trunc p).toLaurent + invert ((trunc (invert p)).toLaurent) - C (p.coeff 0) = p := by
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    linear_combination hp + hq
  | C_mul_T n r =>
    have hc : (C r * T n).coeff 0 = if n = 0 then r else 0 := by
      rw [← single_eq_C_mul_T]
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    rw [hc]
    simp only [map_mul, invert_C, invert_T, trunc_C_mul_T]
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · have hn' : n ≤ 0 := hn.le
      simp [hn.not_ge, hn', hn.ne]
    · simp
    · have hn' : ¬ n ≤ 0 := by omega
      have he : ((n.toNat : ℕ) : ℤ) = n := by omega
      simp [hn.le, hn', he, ← single_eq_C_mul_T, hn.ne']

end LaurentPolynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Substitution of `s⁻¹ - s` in `q(X²)` agrees with evaluating the Laurent
polynomial `q(T + T⁻¹ - 2)` at `T = s²`, under any coefficient homomorphism. -/
theorem eval₂_comp_X_sq_eq_laurent_eval₂ {S : Type*} [CommRing S]
    (q : R[X]) (f : R →+* S) (s : Sˣ) :
    Polynomial.eval₂ f ((s⁻¹ : Sˣ).val - s.val) (q.comp (Polynomial.X ^ 2)) =
      LaurentPolynomial.eval₂ f (s ^ 2)
        (Polynomial.eval₂ LaurentPolynomial.C (T 1 + T (-1) - 2) q) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_comp]
  have hc : (LaurentPolynomial.eval₂ f (s ^ 2)).comp LaurentPolynomial.C = f := by
    ext r
    simp
  rw [hc]
  congr 1
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, map_sub, map_add, map_ofNat,
    LaurentPolynomial.eval₂_T, zpow_one, zpow_neg_one, Units.inv_pow_eq_pow_inv,
    Units.val_pow_eq_pow_val]
  have hs := s.inv_mul
  linear_combination -2 * hs

/-- The positive and reflected negative parts of an ordinary polynomial, with the
constant counted once, are a polynomial in `T + T⁻¹`. -/
theorem exists_eval₂_add_T_neg (p : R[X]) :
    ∃ q : R[X], Polynomial.eval₂ LaurentPolynomial.C
      (T 1 + T (-1)) q =
      p.toLaurent + invert p.toLaurent - LaurentPolynomial.C (p.coeff 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    refine ⟨p' + q', ?_⟩
    simp only [Polynomial.eval₂_add, map_add, Polynomial.coeff_add, hp', hq']
    ring
  | monomial n r =>
    cases n with
    | zero =>
      exact ⟨Polynomial.C r, by simp⟩
    | succ n =>
      refine ⟨Polynomial.C r * Polynomial.Chebyshev.C R (n + 1), ?_⟩
      have hc := Polynomial.Chebyshev.eval₂_C_add_T_neg (R := R) (n + 1)
      push_cast at hc
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, hc]
      simp [mul_add, add_comm]

end Polynomial

namespace LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- A Laurent polynomial is fixed by inversion exactly when it is an ordinary
polynomial in `T + T⁻¹`. This holds without inverting two. -/
theorem invert_eq_self_iff_exists_eval₂ (p : R[T;T⁻¹]) :
    invert p = p ↔ ∃ q : R[X], Polynomial.eval₂ C (T 1 + T (-1)) q = p := by
  constructor
  · intro hp
    obtain ⟨q, hq⟩ := Polynomial.exists_eval₂_add_T_neg (trunc p)
    refine ⟨q, ?_⟩
    rw [hq, coeff_trunc]
    simpa only [hp, Int.natCast_zero] using toLaurent_trunc_add_invert p
  · rintro ⟨q, rfl⟩
    induction q using Polynomial.induction_on' with
    | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
    | monomial n r => simp [Polynomial.eval₂_monomial, add_comm]

/-- A symmetric Laurent polynomial can also be expressed in the shifted generator
`T + T⁻¹ - 2`, the square of the Conway variable after doubling exponents. -/
theorem exists_eval₂_add_T_neg_sub_two {p : R[T;T⁻¹]} (hp : invert p = p) :
    ∃ q : R[X], Polynomial.eval₂ C (T 1 + T (-1) - 2) q = p := by
  obtain ⟨q, hq⟩ := (invert_eq_self_iff_exists_eval₂ p).mp hp
  refine ⟨q.comp (Polynomial.X + 2), ?_⟩
  rw [Polynomial.eval₂_comp]
  simpa using hq

end LaurentPolynomial
