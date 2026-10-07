/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Endomorphisms whose square is a power map

If a ring endomorphism squares to a positive power map, it is integral and induces an
involution on the prime spectrum. For an endomorphism of a finitely generated algebra,
integrality implies finiteness. These criteria apply in particular to square roots of
Frobenius, without requiring the ring to be reduced.
-/

public section

namespace RingHom

variable {A : Type*}

/-- An endomorphism whose square is a positive power map is integral. -/
theorem isIntegral_of_comp_self_eq_pow [CommRing A] (f : A →+* A) {n : ℕ} (hn : 0 < n)
    (hf : ∀ x, f (f x) = x ^ n) : f.IsIntegral := by
  let := f.toAlgebra
  intro x
  apply IsIntegral.of_pow hn
  rw [← hf x]
  exact isIntegral_algebraMap

/-- An endomorphism whose square is a positive power map induces an involution on prime ideals.
This includes nonreduced rings: prime ideals detect membership of positive powers. -/
theorem comap_involutive_of_comp_self_eq_pow [CommSemiring A] (f : A →+* A) {n : ℕ}
    (hn : 0 < n)
    (hf : ∀ x, f (f x) = x ^ n) : Function.Involutive (PrimeSpectrum.comap f) := by
  intro P
  apply PrimeSpectrum.ext
  ext x
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hf]
  exact P.isPrime.pow_mem_iff_mem n hn

end RingHom

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A square root of a positive power map on a finite-type algebra is a finite morphism.
No field or characteristic hypothesis is needed. -/
theorem finite_of_comp_self_eq_pow [Algebra.FiniteType R A] (f : A →ₐ[R] A)
    {n : ℕ} (hn : 0 < n) (hf : ∀ x, f (f x) = x ^ n) : f.Finite := by
  apply (f.toRingHom.isIntegral_of_comp_self_eq_pow hn hf).to_finite
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap R A)
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
    RingHom.finiteType_algebraMap] using (inferInstance : Algebra.FiniteType R A)

end AlgHom
