/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dominance, injectivity and density on prime spectra

An injective homomorphism of commutative semirings induces a dense map on prime spectra.
For a reduced source ring, the converse holds. These facts supply the coordinate-ring criterion for
dominance used in dominant affine group quotients.

A subset of the prime spectrum containing every minimal prime is dense. This is how
generic properties, such as freeness of a module at the minimal primes of a reduced ring, are
turned into dense subsets of the spectrum.
-/

public section

namespace RingHom

variable {R S : Type*}

/-- An injective homomorphism of commutative semirings induces a dense map on prime spectra. -/
theorem denseRange_comap_of_injective [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (hf : Function.Injective f) :
    DenseRange (PrimeSpectrum.comap f) := by
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    RingHom.ker, Ideal.comap_bot_of_injective f hf]
  exact bot_le

/-- A ring homomorphism from a reduced ring is injective exactly when its spectral
comap has dense range. -/
theorem denseRange_comap_iff_injective [CommRing R] [CommSemiring S] [IsReduced R] (f : R →+* S) :
    DenseRange (PrimeSpectrum.comap f) ↔ Function.Injective f := by
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, RingHom.injective_iff_ker_eq_bot,
    nilradical_eq_zero, Ideal.zero_eq_bot, le_bot_iff]

end RingHom

namespace PrimeSpectrum

variable {R : Type*} [CommSemiring R]

/-- A subset of the prime spectrum containing every minimal prime is dense: every nonempty open
set contains a minimal prime, namely a generization of any of its points. -/
theorem dense_of_forall_mem_minimalPrimes {s : Set (PrimeSpectrum R)}
    (hs : ∀ (p : Ideal R) (hp : p ∈ minimalPrimes R), ⟨p, hp.1.1⟩ ∈ s) : Dense s := by
  refine dense_iff_inter_open.mpr fun U hU ⟨x, hx⟩ ↦ ?_
  obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (J := x.asIdeal) bot_le
  have hspec : (⟨q, hq.1.1⟩ : PrimeSpectrum R) ⤳ x := (le_iff_specializes _ _).mp hqx
  exact ⟨_, hspec.mem_open hU hx, hs q hq⟩

end PrimeSpectrum
