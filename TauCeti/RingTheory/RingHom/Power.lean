/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Ring homomorphisms followed by a power map

Let `f : A →+* B` and `g : B → A` satisfy `f (g x) = x ^ n` for some positive `n`. Then `f` is
integral, and if `g` is a ring homomorphism then `PrimeSpectrum.comap g` is a left inverse of
`PrimeSpectrum.comap f`. For an algebra homomorphism into a finitely generated algebra,
integrality implies finiteness.

Taking `g = f` covers endomorphisms whose square is a positive power map, such as square roots
of Frobenius: they are finite on finite-type algebras and induce involutions on the prime
spectrum, without requiring the ring to be reduced.
-/

public section

namespace RingHom

variable {A B : Type*}

/-- If every element of `B` has a positive power `x ^ n = f (g x)` in the range of `f`, then `f`
is integral. -/
theorem isIntegral_of_comp_eq_pow [CommRing A] [CommRing B] (f : A →+* B) {g : B → A} {n : ℕ}
    (hn : 0 < n) (hfg : ∀ x, f (g x) = x ^ n) : f.IsIntegral := by
  let := f.toAlgebra
  intro x
  apply IsIntegral.of_pow hn
  rw [← hfg x]
  exact isIntegral_algebraMap

/-- If `f ∘ g` is a power map, then `PrimeSpectrum.comap g` is a left inverse of
`PrimeSpectrum.comap f`. This includes nonreduced rings: prime ideals detect membership of
positive powers. For the exponent `0`, the ring `B` is trivial and has no prime ideals. For
`g = f` this says that `PrimeSpectrum.comap f` is an involution. -/
theorem leftInverse_comap_of_comp_eq_pow [CommSemiring A] [CommSemiring B] (f : A →+* B)
    {g : B →+* A} {n : ℕ} (hfg : ∀ x, f (g x) = x ^ n) :
    Function.LeftInverse (PrimeSpectrum.comap g) (PrimeSpectrum.comap f) := by
  intro P
  rcases n.eq_zero_or_pos with rfl | hn
  · have h : (0 : B) = 1 := by simpa using hfg 0
    exact absurd (by rw [Ideal.eq_top_iff_one, ← h]; exact P.asIdeal.zero_mem) P.isPrime.ne_top
  ext x
  simp [hfg, P.isPrime.pow_mem_iff_mem n hn]

end RingHom

namespace AlgHom

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- If `f ∘ g` is a positive power map and `B` is a finite-type `R`-algebra, then `f` is a
finite morphism. No field or characteristic hypothesis is needed. -/
theorem finite_of_comp_eq_pow [Algebra.FiniteType R B] (f : A →ₐ[R] B) {g : B → A}
    {n : ℕ} (hn : 0 < n) (hfg : ∀ x, f (g x) = x ^ n) : f.Finite := by
  apply (f.toRingHom.isIntegral_of_comp_eq_pow hn hfg).to_finite
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap R A)
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
    RingHom.finiteType_algebraMap] using (inferInstance : Algebra.FiniteType R B)

end AlgHom
