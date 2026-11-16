/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Derivatives of annihilating polynomials lie in the different

Let `B` be the integral closure of an integrally closed domain `A` in an extension `L/K` of its
fraction field, and let `x ∈ B` generate `L` over `K`; then `L/K` is finite, and no separability
hypothesis is needed. Mathlib shows that `f'(x)` lies in the different ideal `𝔇_{B/A}` when `f` is
the minimal polynomial of `x` over `A` and `L/K` is separable
(`aeval_derivative_mem_differentIdeal`); if `L/K` is inseparable then `f'` vanishes. Any
polynomial `p ∈ A[X]` with `p(x) = 0` is a multiple `f g` of the minimal polynomial, `A` being
integrally closed, so `p'(x) = f'(x) g(x)` lies in the different as well. This is the form in which
an explicit equation for `x` bounds ramification: a prime of `B` not containing `p'(x)` does not
divide the different, and when `A` is a Dedekind domain such a prime is unramified over `A`
(`dvd_differentIdeal_iff`).

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

variable {A K L B : Type*} [CommRing A] [Field K] [Field L] [CommRing B]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegralClosure B A L]
  [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]

/-- **The derivative of an annihilating polynomial lies in the different.** If `x ∈ B` generates
`L` over `K` and `p ∈ A[X]` vanishes at `x`, then `p'(x) ∈ 𝔇_{B/A}`. For `p` the minimal polynomial
of `x` this is Mathlib's `aeval_derivative_mem_differentIdeal`. -/
theorem aeval_derivative_mem_differentIdeal_of_aeval_eq_zero {x : B}
    (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) {p : A[X]} (hp : aeval x p = 0) :
    aeval x (derivative p) ∈ differentIdeal A B := by
  -- `A` is integrally closed, so the minimal polynomial `f` of `x` divides `p = f g`, and
  -- `p'(x) = f'(x) g(x) + f(x) g'(x) = f'(x) g(x)`.
  obtain ⟨g, rfl⟩ := minpoly.isIntegrallyClosed_dvd (IsIntegralClosure.isIntegral A L x) hp
  have hAx : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  have hint : IsIntegral K (algebraMap B L x) :=
    (IsIntegral.map (IsScalarTower.toAlgHom A B L) hAx).tower_top
  -- `L = K(x)` is finite over `K`.
  have htop : IntermediateField.adjoin K {algebraMap B L x} = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra K _ hx
  have : FiniteDimensional K L := by
    have := IntermediateField.adjoin.finiteDimensional hint
    rw [htop] at this
    exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv
  have hf : aeval x (derivative (minpoly A x)) ∈ differentIdeal A B := by
    by_cases hsep : Algebra.IsSeparable K L
    · exact aeval_derivative_mem_differentIdeal A K L x hx
    · -- If `L / K` is inseparable, so is the minimal polynomial of `x`, whose derivative vanishes.
      have hns : ¬ IsSeparable K (algebraMap B L x) := fun h ↦ hsep <| by
        rw [← IntermediateField.isSeparable_top, ← htop]
        exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).2 h
      have hder : derivative (minpoly K (algebraMap B L x)) = 0 := by
        by_contra h
        exact hns ((separable_iff_derivative_ne_zero (minpoly.irreducible hint)).2 h)
      rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx, derivative_map] at hder
      rw [Polynomial.map_eq_zero_iff (IsFractionRing.injective A K)] at hder
      simp [hder]
  simpa [derivative_mul] using Ideal.mul_mem_right (aeval x g) _ hf

/-- **A radical generator puts `n a` in the different.** If `x ∈ B` generates `L` over `K` and
`xⁿ = a` with `a ∈ A`, then `n a ∈ 𝔇_{B/A}`. -/
theorem natCast_mul_mem_differentIdeal_of_pow_eq {x : B}
    (hx : Algebra.adjoin K {algebraMap B L x} = ⊤) {n : ℕ} {a : A}
    (hxa : x ^ n = algebraMap A B a) :
    (n : B) * algebraMap A B a ∈ differentIdeal A B := by
  obtain _ | n := n
  · simp
  have hmem := Ideal.mul_mem_right x _ <| aeval_derivative_mem_differentIdeal_of_aeval_eq_zero
    (K := K) (L := L) hx (p := X ^ (n + 1) - C a) (by simp [hxa])
  -- `(n + 1) xⁿ · x = (n + 1) xⁿ⁺¹ = (n + 1) a`.
  rw [← hxa, pow_succ, ← mul_assoc]
  simpa [derivative_X_pow] using hmem

end TauCeti

end
