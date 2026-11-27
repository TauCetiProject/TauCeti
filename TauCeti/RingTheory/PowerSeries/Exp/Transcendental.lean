/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Integral
import TauCeti.RingTheory.HahnSeries.PowerSeries
import Mathlib.LinearAlgebra.Eigenspace.Basic
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Transcendence of the formal exponential

Over a commutative ℚ-algebra, a polynomial relation for the formal exponential over
`R[X]` would be a sum of terms `pᵢ(X) exp(iX)`. These terms lie in distinct generalized
eigenspaces of formal differentiation, so they vanish separately. Passing to Laurent series
over a field gives transcendence over the rational function field by clearing denominators.
-/

public section

open Polynomial Module

namespace PowerSeries

variable {R : Type*} [CommRing R] [Algebra ℚ R]

private theorem polynomial_mul_rescale_exp_mem_maxGenEigenspace (p : R[X]) (i : ℕ) :
    (p : R⟦X⟧) * rescale (i : R) (exp R) ∈
      End.maxGenEigenspace (derivative.toLinearMap.restrictScalars ℚ) (i : ℚ) := by
  let T := derivative.toLinearMap.restrictScalars ℚ - (i : ℚ) • (1 : End ℚ R⟦X⟧)
  have step : Function.Semiconj (fun q : R[X] ↦ (q : R⟦X⟧) * rescale (i : R) (exp R))
      Polynomial.derivative T := by
    intro q
    simp [T, Derivation.leibniz, derivative_coe, derivative_rescale, derivative_exp,
      Algebra.smul_def, mul_comm, mul_left_comm]
  refine (End.mem_maxGenEigenspace ..).mpr ⟨p.natDegree + 1, ?_⟩
  simpa only [pow_apply_eq_iterate, iterate_derivative_eq_zero p.natDegree.lt_succ_self,
    Polynomial.coe_zero, zero_mul] using (step.iterate_right (p.natDegree + 1) p).symm

/-- The formal exponential is transcendental over the polynomial ring in its parameter. -/
theorem transcendental_exp (R : Type*) [CommRing R] [Algebra ℚ R] :
    Transcendental R[X] (exp R) := by
  rintro ⟨P, hP, hrel⟩
  let D := (derivative (R := R)).toLinearMap.restrictScalars ℚ
  have hind := (End.independent_maxGenEigenspace D).comp (Nat.cast_injective (R := ℚ))
  have h := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hind P.support
    (fun i ↦ (P.coeff i : R⟦X⟧) * exp R ^ i)
    (fun i _ ↦ by
      rw [exp_pow_eq_rescale_exp]
      exact polynomial_mul_rescale_exp_mem_maxGenEigenspace (P.coeff i) i)
  rw [aeval_def, eval₂_eq_sum, sum_def] at hrel
  obtain ⟨i, hi⟩ := support_nonempty.mpr hP
  have hz := h (by simpa [PowerSeries.algebraMap_apply'] using hrel) i hi
  exact (mem_support_iff.mp hi) <| coe_eq_zero_iff.mp <|
    ((isUnit_exp R).pow i).mul_left_eq_zero.mp hz

open scoped LaurentSeries RatFunc

/-- As a Laurent series, the formal exponential is transcendental over the rational functions. -/
theorem transcendental_coe_exp (K : Type*) [Field K] [CharZero K] :
    Transcendental (RatFunc K) (exp K : K⸨X⸩) :=
  (IsFractionRing.isAlgebraic_iff K[X] (RatFunc K) K⸨X⸩).not.mp <|
    (transcendental_algebraMap_iff (R := K[X]) (S := K⟦X⟧) (A := K⸨X⸩)
      (IsFractionRing.injective _ _)).mpr (transcendental_exp K)

end PowerSeries
