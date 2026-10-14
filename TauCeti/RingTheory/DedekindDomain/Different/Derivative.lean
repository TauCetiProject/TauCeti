/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Derivatives of annihilating polynomials lie in the different

Let `B` be the integral closure of an integrally closed domain `A` in a finite separable extension
`L/K` of its fraction field, and let `x ∈ B` generate `L` over `K`. Mathlib shows that `f'(x)`
lies in the different ideal `𝔇_{B/A}` when `f` is the minimal polynomial of `x` over `A`
(`aeval_derivative_mem_differentIdeal`). Any polynomial `p ∈ A[X]` with `p(x) = 0` is a multiple
`f g` of the minimal polynomial, `A` being integrally closed, so `p'(x) = f'(x) g(x)` lies in the
different as well. This is the form in which an explicit equation for `x` bounds ramification: a
prime of `B` not containing `p'(x)` does not divide the different, and when `A` is a Dedekind
domain such a prime is unramified over `A` (`dvd_differentIdeal_iff`).

The case `p = Xⁿ - a` is the radical extension `L = K(a^{1/n})`: then `p'(x) = n xⁿ⁻¹`, and
multiplying by `x` gives `n a ∈ 𝔇_{B/A}`.

## Main results

* `TauCeti.aeval_derivative_mem_differentIdeal_of_aeval_eq_zero`: `p'(x) ∈ 𝔇_{B/A}` for every
  `p ∈ A[X]` with `p(x) = 0`.
* `TauCeti.natCast_mul_mem_differentIdeal_of_pow_eq`: if `xⁿ = a ∈ A`, then `n a ∈ 𝔇_{B/A}`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, Appendix, Proposition A.5.
-/

public section

open Polynomial

namespace TauCeti

variable (A K L B : Type*) [CommRing A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegralClosure B A L]
  [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

variable {A K L B}

include K L in
/-- **The derivative of an annihilating polynomial lies in the different.** If `x ∈ B` generates
`L` over `K` and `p ∈ A[X]` vanishes at `x`, then `p'(x) ∈ 𝔇_{B/A}`. For `p` the minimal polynomial
of `x` this is Mathlib's `aeval_derivative_mem_differentIdeal`. -/
theorem aeval_derivative_mem_differentIdeal_of_aeval_eq_zero {x : B}
    (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) {p : A[X]} (hp : aeval x p = 0) :
    aeval x (derivative p) ∈ differentIdeal A B := by
  -- `A` is integrally closed, so the minimal polynomial `f` of `x` divides `p = f g`, and
  -- `p'(x) = f'(x) g(x) + f(x) g'(x) = f'(x) g(x)`.
  obtain ⟨g, rfl⟩ := minpoly.isIntegrallyClosed_dvd (IsIntegralClosure.isIntegral A L x) hp
  rw [derivative_mul, map_add, map_mul, map_mul, minpoly.aeval, zero_mul, add_zero]
  exact Ideal.mul_mem_right _ _ (aeval_derivative_mem_differentIdeal A K L x hx)

include K L in
/-- **A radical generator puts `n a` in the different.** If `x ∈ B` generates `L` over `K` and
`xⁿ = a` with `a ∈ A`, then `n a ∈ 𝔇_{B/A}`. -/
theorem natCast_mul_mem_differentIdeal_of_pow_eq {x : B}
    (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) {n : ℕ} {a : A}
    (hxa : x ^ n = algebraMap A B a) :
    (n : B) * algebraMap A B a ∈ differentIdeal A B := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have hmem := aeval_derivative_mem_differentIdeal_of_aeval_eq_zero (K := K) (L := L) hx
    (p := X ^ n - C a) (by simp [hxa])
  -- `(n xⁿ⁻¹) x = n xⁿ = n a`.
  have h : (n : B) * algebraMap A B a = aeval x (derivative (X ^ n - C a : A[X])) * x := by
    simp [derivative_X_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn),
      hxa]
  rw [h]
  exact Ideal.mul_mem_right _ _ hmem

end TauCeti

end
