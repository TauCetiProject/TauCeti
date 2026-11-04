/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.AtPrime.Basic
import TauCeti.Algebra.QuadraticAlgebra.Etale

/-!
# Tests for the discriminant criterion on quadratic algebras

`QuadraticAlgebra R a b` is `R[x] ⧸ (x² - b x - a)`, free over `R` with basis `1, x`, and the
discriminant of this basis is `b² + 4a` (`Algebra.discr_quadraticAlgebra`). By the discriminant
criterion it is étale over `R` exactly when this discriminant is a unit
(`QuadraticAlgebra.etale_iff_isUnit_discr`).

* The dual numbers `k[x] ⧸ (x²)` over a field `k` have discriminant `0`, so they are not étale over
  `k`. This holds in every characteristic, including two.
* Over the localization `ℤ_(p)` of `ℤ` at an odd prime `p`, written as any `A` with
  `IsLocalization.AtPrime A (p)`, the algebra `A[x] ⧸ (x² - d)` has discriminant `4d`. It is étale
  when `d` is a unit, and it is not étale when `d = p`.
-/

open QuadraticAlgebra

namespace TauCeti

/-- *test_discr_dual_numbers*: over a field `k`, the dual numbers `k[x] ⧸ (x²)` with basis `1, x`
have discriminant `0` and are not étale over `k`. -/
example (k : Type*) [Field k] :
    Algebra.discr k (basis (0 : k) 0) = 0 ∧ ¬ Algebra.Etale k (QuadraticAlgebra k 0 0) := by
  have h : Algebra.discr k (basis (0 : k) 0) = 0 := by simp [discr_def]
  refine ⟨h, fun he ↦ not_isUnit_zero (M₀ := k) ?_⟩
  rw [← h, Algebra.discr_quadraticAlgebra]
  exact etale_iff_isUnit_discr.mp he

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
  [IsLocalization.AtPrime A (Ideal.span {(p : ℤ)})]

/-- *test_discr_quadratic*: for an odd prime `p`, a unit `d` of `ℤ_(p)` and the algebra
`ℤ_(p)[x] ⧸ (x² - d)` with basis `1, x`, the discriminant is `4d`, a unit, and the algebra is
étale over `ℤ_(p)`. -/
example (hp : p ≠ 2) {d : A} (hd : IsUnit d) :
    Algebra.discr A (basis d 0) = 4 * d ∧ IsUnit (4 * d) ∧
      Algebra.Etale A (QuadraticAlgebra A d 0) := by
  have h4 : IsUnit (4 : A) := by
    have h := (IsLocalization.AtPrime.isUnit_to_map_iff A (Ideal.span {(p : ℤ)}) 4).mpr <|
      Ideal.mem_primeCompl_iff.mpr fun hmem ↦ hp <| by
        have h2 : p ∣ 2 ^ 2 := by exact_mod_cast Ideal.mem_span_singleton.mp hmem
        exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
          ((Fact.out : p.Prime).dvd_of_dvd_pow h2)
    simpa using h
  have hdiscr : discr d (0 : A) = 4 * d := by simp [discr_def]
  exact ⟨by rw [Algebra.discr_quadraticAlgebra, hdiscr], h4.mul hd,
    etale_iff_isUnit_discr.mpr (hdiscr ▸ h4.mul hd)⟩

/-- *test_discr_quadratic*: for a prime `p` and the algebra `ℤ_(p)[x] ⧸ (x² - p)` with basis `1, x`,
the discriminant is `4p`, which is not a unit, and the algebra is not étale over `ℤ_(p)`. -/
example : Algebra.discr A (basis (p : A) 0) = 4 * p ∧ ¬ IsUnit (4 * p : A) ∧
    ¬ Algebra.Etale A (QuadraticAlgebra A (p : A) 0) := by
  have hdiscr : discr (p : A) 0 = 4 * p := by simp [discr_def]
  have hunit : ¬ IsUnit (4 * p : A) := by
    have h := IsLocalization.AtPrime.isUnit_to_map_iff A (Ideal.span {(p : ℤ)}) (4 * p)
    rw [map_mul, map_ofNat, map_natCast] at h
    rw [h, Ideal.mem_primeCompl_iff, not_not, Ideal.mem_span_singleton]
    exact dvd_mul_left _ _
  refine ⟨by rw [Algebra.discr_quadraticAlgebra, hdiscr], hunit, fun he ↦ hunit ?_⟩
  rw [← hdiscr]
  exact etale_iff_isUnit_discr.mp he

end TauCeti
