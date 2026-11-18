/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Symmetric Laurent polynomials

A Laurent polynomial fixed by inversion is a polynomial in `T + T⁻¹`, over any
commutative ring. The proof uses Mathlib's rescaled Chebyshev polynomials, which
express `Tⁿ + T⁻ⁿ` without dividing by two. Consequently the result applies to
integer coefficients and to rings of characteristic two.

The shifted generator `T + T⁻¹ - 2` is convenient for converting a symmetric
Alexander polynomial to the square of the Conway variable.

The rescaled Chebyshev polynomials of the second kind give the companion identity
`(T - T⁻¹) Sₙ(T + T⁻¹) = Tⁿ⁺¹ - T⁻ⁿ⁻¹` for the antisymmetric Laurent polynomials.

Finally, a family of symmetric Laurent polynomials whose coefficients are read off a nested power
series that is symmetric in its two variables consists of constants
(`LaurentPolynomial.eq_C_coeff_zero_of_coeff_swap`).
-/

public section

noncomputable section

open LaurentPolynomial
open scoped Polynomial

namespace Polynomial.Chebyshev

variable {R : Type*} [CommRing R]

/-- The rescaled Chebyshev polynomial expresses a pair of opposite Laurent powers. -/
@[simp] theorem eval₂_C_add_T_neg (n : ℤ) :
    Polynomial.eval₂ LaurentPolynomial.C
      (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1) : R[T;T⁻¹]) (C R n) =
      LaurentPolynomial.T n + LaurentPolynomial.T (-n) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [one_add_one_eq_two]
  | one => simp
  | add_two n h₁ h₀ =>
    rw [C_add_two, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, h₁, h₀]
    simp only [mul_add, add_mul, ← T_add]
    ring_nf
  | neg_add_one n h₀ h₁ =>
    rw [C_sub_one, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, h₁, h₀]
    simp only [mul_add, add_mul, ← T_add]
    ring_nf

/-- The rescaled Chebyshev polynomial of the second kind expresses a difference of opposite
Laurent powers, once multiplied by `T - T⁻¹`. -/
@[simp] theorem T_sub_T_neg_mul_eval₂_S_add_T_neg (n : ℤ) :
    (LaurentPolynomial.T 1 - LaurentPolynomial.T (-1) : R[T;T⁻¹]) *
        Polynomial.eval₂ LaurentPolynomial.C (LaurentPolynomial.T 1 + LaurentPolynomial.T (-1))
          (S R n) =
      LaurentPolynomial.T (n + 1) - LaurentPolynomial.T (-(n + 1)) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp
  | one =>
    simp only [S_one, Polynomial.eval₂_X, mul_add, sub_mul, ← T_add]
    ring_nf
  | add_two n h₁ h₀ =>
    rw [S_add_two, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_sub,
      mul_left_comm, h₁, h₀]
    simp only [mul_sub, add_mul, ← T_add]
    ring_nf
  | neg_add_one n h₀ h₁ =>
    rw [S_sub_one, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, mul_sub,
      mul_left_comm, h₁, h₀]
    simp only [mul_sub, add_mul, ← T_add]
    ring_nf

end Polynomial.Chebyshev

namespace LaurentPolynomial

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
      simp [← single_eq_C_mul_T, Finsupp.single_apply]
    rw [hc]
    simp only [map_mul, invert_C, invert_T, trunc_C_mul_T]
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · simp [hn.not_ge, hn.le, hn.ne]
    · simp
    · have he : ((n.toNat : ℕ) : ℤ) = n := by omega
      simp [hn.le, hn.not_ge, he, ← single_eq_C_mul_T, hn.ne']

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
  congr 1
  · ext r
    simp
  · simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X, map_sub, map_add, map_ofNat,
      LaurentPolynomial.eval₂_T, zpow_one, zpow_neg_one, Units.inv_pow_eq_pow_inv,
      Units.val_pow_eq_pow_val]
    linear_combination -2 * s.inv_mul

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

/-- A Laurent polynomial is fixed by inversion exactly when it is an ordinary polynomial in the
shifted generator `T + T⁻¹ - 2`, the square of the Conway variable after doubling exponents. -/
theorem invert_eq_self_iff_exists_eval₂_sub_two (p : R[T;T⁻¹]) :
    invert p = p ↔ ∃ q : R[X], Polynomial.eval₂ C (T 1 + T (-1) - 2) q = p := by
  rw [invert_eq_self_iff_exists_eval₂]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.comp (Polynomial.X + 2), by simp [Polynomial.eval₂_comp]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.comp (Polynomial.X - 2), by simp [Polynomial.eval₂_comp]⟩

section Semiring

variable {R : Type*} [Semiring R]

/-- If the Laurent polynomials `L N` are symmetric, and the coefficient of `uᵏ` in `L N` is the
coefficient of `vᵏ⁺ᴺ` read off a series `G` that is symmetric in its two variables, then each
`L N` is constant. This is the induction in the formal Liouville theorem for the Tate curve. -/
theorem eq_C_coeff_zero_of_coeff_swap {G : PowerSeries (PowerSeries R)} {L : ℕ → R[T;T⁻¹]}
    (hcoe : ∀ (N : ℕ) (k : ℤ),
      (L N).coeff k = if k + N < 0 then 0 else
        PowerSeries.coeff (k + N).natAbs (PowerSeries.coeff N G))
    (hsymm : ∀ (N : ℕ) (k : ℤ), (L N).coeff (-k) = (L N).coeff k)
    (hswap : ∀ a b : ℕ,
      PowerSeries.coeff a (PowerSeries.coeff b G) = PowerSeries.coeff b (PowerSeries.coeff a G))
    (N : ℕ) :
    L N = C ((L N).coeff 0) := by
  have key (N : ℕ) : ∀ m : ℕ, 0 < m → (L N).coeff m = 0 := by
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro m hm
      rw [← hsymm, hcoe]
      split_ifs with h
      · rfl
      · have h' := ih (N - m) (by omega) m hm
        rw [hcoe, ite_eq_right (by omega)] at h'
        have e₁ : (-(m : ℤ) + N).natAbs = N - m := by omega
        have e₂ : ((m : ℤ) + (N - m : ℕ)).natAbs = N := by omega
        rw [e₁, hswap]
        rwa [e₂] at h'
  refine LaurentPolynomial.ext fun k ↦ ?_
  rw [LaurentPolynomial.C_apply]
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -m := ⟨k.natAbs, by omega⟩
    rw [hsymm, key N m (by omega), ite_eq_right (by omega)]
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m := ⟨k.natAbs, by omega⟩
    rw [key N m (by omega), ite_eq_right (by omega)]

end Semiring

end LaurentPolynomial
