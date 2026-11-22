/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.Algebra.Quaternion.NormForm
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Integral elements of a quaternion algebra

Every quaternion `x ∈ ℍ[S,c₁,c₂,c₃]` is a root of its reduced characteristic polynomial
`X² - trd(x) X + nrd(x)`, whose coefficients are the reduced trace `trd(x) = x + star x =
2 x.re + c₂ x.imI` and the reduced norm `nrd(x) = x * star x`, the norm form
`QuaternionAlgebra.normForm`.

Over a field `F` this polynomial controls integrality: for any ring `R` with an algebra map to `F`,
a quaternion `x ∈ ℍ[F,c₁,c₂,c₃]` is integral over `R` exactly when its reduced trace and reduced
norm are. If `x` is not a scalar, the reduced characteristic polynomial is the minimal polynomial of
`x` over `F`, so it divides every monic polynomial over `R` killing `x`, and its coefficients are
then integral. When `R` is integrally closed with fraction field `F`, this says that `x` is
integral exactly when `trd(x)` and `nrd(x)` lie in `R`. This is the criterion behind orders in
quaternion algebras: their elements have integral reduced trace and norm, and they are stable under
the involution `star x = trd(x) - x`.

## Main results

* `QuaternionAlgebra.aeval_X_sq_sub_C_mul_X_add_C_eq_zero`: every quaternion is a root of
  `X² - trd(x) X + nrd(x)`.
* `QuaternionAlgebra.isIntegral_iff`: a quaternion over a field is integral over `R` exactly when
  its reduced trace and reduced norm are.
* `QuaternionAlgebra.isIntegral_iff_mem_range`: over an integrally closed domain with fraction
  field `F`, a quaternion is integral exactly when its reduced trace and reduced norm lie in `R`.

## References

* J. Voight, *Quaternion algebras*, Lemma 10.3.3 and Corollary 10.3.6.
-/

public section

open Polynomial

open scoped Quaternion

namespace QuaternionAlgebra

section CommRing

variable {S : Type*} [CommRing S] {c₁ c₂ c₃ : S}

/-- **The reduced characteristic polynomial.** Every quaternion `x` is a root of
`X² - trd(x) X + nrd(x)`, where `trd(x) = 2 x.re + c₂ x.imI` is the reduced trace and
`nrd(x) = normForm c₁ c₂ c₃ x` the reduced norm. -/
theorem aeval_X_sq_sub_C_mul_X_add_C_eq_zero (x : ℍ[S,c₁,c₂,c₃]) :
    aeval x (X ^ 2 - C (2 * x.re + c₂ * x.imI) * X + C (normForm c₁ c₂ c₃ x)) = 0 := by
  -- `x² - (x + star x) x + nrd(x) = nrd(x) - star x * x`, and `star x * x = nrd(x)`
  rw [map_add, map_sub, map_mul, aeval_X_pow, aeval_C, aeval_C, aeval_X, coe_algebraMap,
    ← self_add_star', add_mul, star_mul_self]
  noncomm_ring

end CommRing

section Field

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F] {c₁ c₂ c₃ : F}

/-- A scalar quaternion `r` has reduced trace `2 r` and reduced norm `r²`. -/
private theorem isIntegral_of_mem_range {x : ℍ[F,c₁,c₂,c₃]} (hint : IsIntegral R x)
    (hx : x ∈ (algebraMap F ℍ[F,c₁,c₂,c₃]).range) :
    IsIntegral R (2 * x.re + c₂ * x.imI) ∧ IsIntegral R (normForm c₁ c₂ c₃ x) := by
  obtain ⟨r, rfl⟩ := hx
  have hr : IsIntegral R r := (isIntegral_algHom_iff (IsScalarTower.toAlgHom R F ℍ[F,c₁,c₂,c₃])
    (algebraMap F ℍ[F,c₁,c₂,c₃]).injective).1 hint
  rw [coe_algebraMap, re_coe, imI_coe, mul_zero, add_zero, normForm_coe]
  exact ⟨two_mul r ▸ hr.add hr, hr.pow 2⟩

/-- **Integral quaternions.** A quaternion `x` over a field `F` is integral over a ring `R` exactly
when its reduced trace `2 x.re + c₂ x.imI` and its reduced norm `normForm c₁ c₂ c₃ x` are. -/
theorem isIntegral_iff {x : ℍ[F,c₁,c₂,c₃]} :
    IsIntegral R x ↔ IsIntegral R (2 * x.re + c₂ * x.imI) ∧ IsIntegral R (normForm c₁ c₂ c₃ x) := by
  set q : F[X] := X ^ 2 - C (2 * x.re + c₂ * x.imI) * X + C (normForm c₁ c₂ c₃ x)
  have hq : q.Monic := by
    unfold q
    monicity!
  have hq2 : q.natDegree = 2 := by
    unfold q
    compute_degree!
  have hqx : aeval x q = 0 := aeval_X_sq_sub_C_mul_X_add_C_eq_zero x
  refine ⟨fun hint => ?_, fun ⟨ht, hn⟩ => ?_⟩
  · by_cases hx : x ∈ (algebraMap F ℍ[F,c₁,c₂,c₃]).range
    · exact isIntegral_of_mem_range hint hx
    -- otherwise `q` is the minimal polynomial of `x` over `F`, so it divides a monic polynomial
    -- over `R` killing `x`, and its coefficients are integral over `R`
    obtain ⟨p, hp, hpx⟩ := hint
    have hmin : minpoly F x = q := by
      have hxF : IsIntegral F x := .of_finite F x
      refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxF) hq (minpoly.dvd F x hqx)
        ?_).symm
      rw [hq2, minpoly.two_le_natDegree_iff hxF]
      exact hx
    have hdvd : q ∣ p.map (algebraMap R F) := by
      rw [← hmin]
      refine minpoly.dvd F x ?_
      rwa [aeval_map_algebraMap, aeval_def]
    have hcoeff := Polynomial.isIntegral_coeff_of_dvd p q hp hq hdvd
    refine ⟨?_, by simpa [q] using hcoeff 0⟩
    simpa [q] using (hcoeff 1).neg
  · -- `x` is integral over the integral closure of `R` in `F`, which is integral over `R`
    let A := integralClosure R F
    refine isIntegral_trans (A := A) x ⟨X ^ 2 - C ⟨_, ht⟩ * X + C ⟨_, hn⟩, by monicity!, ?_⟩
    rw [← aeval_def]
    simpa [q, Subalgebra.algebraMap_eq] using hqx

/-- **Integral quaternions over an integrally closed domain.** If `R` is integrally closed with
fraction field `F`, a quaternion `x ∈ ℍ[F,c₁,c₂,c₃]` is integral over `R` exactly when its reduced
trace `2 x.re + c₂ x.imI` and its reduced norm `normForm c₁ c₂ c₃ x` lie in `R`. -/
theorem isIntegral_iff_mem_range [IsFractionRing R F] [IsIntegrallyClosed R]
    {x : ℍ[F,c₁,c₂,c₃]} :
    IsIntegral R x ↔ 2 * x.re + c₂ * x.imI ∈ (algebraMap R F).range ∧
      normForm c₁ c₂ c₃ x ∈ (algebraMap R F).range := by
  simp only [isIntegral_iff, IsIntegrallyClosed.isIntegral_iff (R := R), RingHom.mem_range]

end Field

end QuaternionAlgebra
