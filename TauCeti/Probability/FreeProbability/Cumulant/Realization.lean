/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.Probability.FreeProbability.FreeProduct.Basic

/-!
# Algebraic realization of scalar free cumulants

Every formal series with constant coefficient one is the free cumulant series of the
indeterminate for a normalized linear functional on the polynomial algebra. No positivity
is asserted: arbitrary algebraic cumulants need not come from a positive functional.
This realizes formal identities as identities of algebraic random variables.

The construction uses the moment–cumulant equation and `PowerSeries.substInvOfIsUnit`,
then extends the resulting moments using `Polynomial.basisMonomials`. Simultaneous free
realizations use `TauCeti.freeProductExpectation` on the free product of polynomial algebras.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 11
  and 16 (algebraic distributions and the moment–cumulant functional equation).
-/

public section

open PowerSeries

open TauCeti

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- Every scalar cumulant series with constant coefficient one has a normalized algebraic
realization on `R[X]`. This does not assert positivity or boundedness. -/
theorem exists_polynomial_freeCumulantSeries_eq (f : R⟦X⟧) (hf : constantCoeff f = 1) :
    ∃ φ : Polynomial R →ₗ[R] R, φ 1 = 1 ∧ freeCumulantSeries φ Polynomial.X = f := by
  classical
  -- Invert `z / f(z)` compositionally. Its inverse `L` satisfies `L = z f(L)`.
  let g := X * invOfUnit f 1
  have hg0 : constantCoeff g = 0 := by simp [g]
  have hg1 : coeff 1 g = 1 := by simp [g, constantCoeff_invOfUnit]
  let L := g.substInvOfIsUnit (hg1 ▸ isUnit_one)
  have hL0 : constantCoeff L = 0 := constantCoeff_substInvOfIsUnit _ _
  have hL : g.subst L = X := subst_substInvOfIsUnit_right g hg0 _
  have hsub : HasSubst L := .of_constantCoeff_zero hL0
  have hOne : (1 : R⟦X⟧).subst L = 1 := by simpa using (PowerSeries.subst_C (a := L) (1 : R))
  have hmul : L = X * f.subst L := by
    have h := congrArg (· * f.subst L) hL
    simpa [g, subst_mul hsub, subst_X hsub, mul_assoc,
      ← subst_mul hsub, invOfUnit_mul f 1 hf, hOne] using h
  let M : R⟦X⟧ := mk fun n => coeff (n + 1) L
  have hLM : L = X * M := by
    simpa [M, hL0] using eq_X_mul_shift_add_const L
  have hM : f.subst (X * M) = M := by
    rw [hLM] at hmul
    exact X_mul_cancel hmul.symm
  have hM0 : constantCoeff M = 1 := by
    rw [← hM, constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero (S := R) (by simp [← constantCoeff_eq]),
      hf, map_one]
  let φ : Polynomial R →ₗ[R] R :=
    (Polynomial.basisMonomials R).constr R (fun n => coeff n M)
  have hφpow (n : ℕ) : φ (Polynomial.X ^ n) = coeff n M := by
    simpa [φ, Polynomial.coe_basisMonomials, Polynomial.X_pow_eq_monomial] using
      (Polynomial.basisMonomials R).constr_basis R (fun n => coeff n M) n
  have hφ : φ 1 = 1 := by simpa [hM0] using hφpow 0
  refine ⟨φ, hφ, ?_⟩
  have hseries : momentSeries φ Polynomial.X = M := by
    ext n
    simpa only [coeff_momentSeries] using hφpow n
  exact (eq_freeCumulantSeries_of_subst_eq Polynomial.X hφ (by rwa [hseries])).symm

end PowerSeries

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Arbitrary normalized scalar cumulant series can be realized simultaneously by free
algebraic variables: take the indeterminate from each factor of the free product of polynomial
algebras. The resulting expectation is not asserted to be positive. -/
theorem exists_freeProduct_freeCumulantSeries_eq {ι : Type*} [DecidableEq ι] (f : ι → R⟦X⟧)
    (hf : ∀ i, constantCoeff (f i) = 1) :
    ∃ φ : LinearAlgebra.FreeProduct R (fun _ : ι => Polynomial R) →ₗ[R] R,
      φ 1 = 1 ∧
      IsFreelyIndependentElements φ
        (fun i => LinearAlgebra.FreeProduct.ι R (fun _ : ι => Polynomial R) i Polynomial.X) ∧
      ∀ i, freeCumulantSeries φ
        (LinearAlgebra.FreeProduct.ι R (fun _ : ι => Polynomial R) i Polynomial.X) = f i := by
  classical
  choose ψ hψ hseries using fun i => exists_polynomial_freeCumulantSeries_eq (f i) (hf i)
  refine ⟨freeProductExpectation ψ hψ, freeProductExpectation_one ψ hψ,
    isFreelyIndependentElements_ι ψ hψ (fun _ => Polynomial.X), fun i => ?_⟩
  refine (freeCumulantSeries_congr _ _ ?_).trans (hseries i)
  ext n
  simp only [coeff_momentSeries, ← map_pow, freeProductExpectation_ι]

end TauCeti
