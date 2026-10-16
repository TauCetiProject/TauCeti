/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Dominance, injectivity, density and the Jacobson radical on prime spectra

An injective homomorphism of commutative semirings induces a dense map on prime spectra.
For a reduced source ring, the converse holds. These facts supply the coordinate-ring criterion for
dominance used in dominant affine group quotients.

A subset of the prime spectrum containing every minimal prime is dense. This is how
generic properties, such as freeness of a module at the minimal primes of a reduced ring, are
turned into dense subsets of the spectrum.

An open subset of the prime spectrum of a commutative ring containing the zero locus of an ideal
contained in the Jacobson radical is the whole spectrum: every prime ideal is contained in a
maximal ideal, which is a point of that zero locus, and an open set contains every point that
specializes to one of its points. For the maximal ideal of a local ring, whose zero locus is the
closed point, this is Mathlib's `IsLocalRing.closedPoint_mem_iff`.
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

/-- For an ideal `I` of a commutative ring `S` contained in the Jacobson radical of `S`, an open
subset of the prime spectrum of `S` contains the zero locus of `I` exactly when it is the whole
spectrum. -/
theorem zeroLocus_subset_iff_eq_top_of_le_jacobson_bot {S : Type*} [CommRing S] {I : Ideal S}
    (hI : I ≤ Ideal.jacobson ⊥) {U : TopologicalSpace.Opens (PrimeSpectrum S)} :
    zeroLocus (I : Set S) ⊆ U ↔ U = ⊤ := by
  refine ⟨fun hU ↦ TopologicalSpace.Opens.coe_eq_univ.mp (Set.eq_univ_of_forall fun x ↦ ?_),
    fun hU ↦ ?_⟩
  · -- `x` specializes to a closed point: a maximal ideal `m` containing the prime ideal `x`
    obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
    refine ((le_iff_specializes x ⟨m, hm.isPrime⟩).mp ((asIdeal_le_asIdeal _ _).mp hxm)).mem_open
      U.isOpen (hU ?_)
    -- a maximal ideal contains the Jacobson radical, so `m` is a point of `V(I)`
    rw [mem_zeroLocus, SetLike.coe_subset_coe]
    exact hI.trans (Ideal.jacobson_bot.trans_le (Ring.jacobson_le_of_isMaximal m))
  · rw [hU, TopologicalSpace.Opens.coe_top]
    exact Set.subset_univ _

end PrimeSpectrum
