/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Valuation.ValuationRing
import TauCeti.Topology.Compactness.Compact

/-!
# Compact subsets of the spectrum of a valuation ring

The ideals of a valuation ring `V` are totally ordered, so the points of `Spec V` form a chain for
specialization (`PrimeSpectrum.isChain_specializes`). Consequently every nonempty quasicompact
subset of `Spec V` contains a largest prime, a point specializing every other point of the subset
(`PrimeSpectrum.exists_isGreatest_of_isCompact`); it is unique by `IsGreatest.unique`.

Applied to the range of a continuous map `g : Z → Spec V` from a nonempty quasicompact space,
which is compact by `isCompact_range`, this gives a point of the image of `g` that is a
specialization of all the others. Scholze and Weinstein use this, in proving that perfect
schemes are determined by their v-sheaves, to see that a map from the v-sheaf of the spectrum
of a valuation ring to the v-sheaf of a scheme factors through that of an affine open.

Both hypotheses are needed: the empty set has no largest element, and in a valuation ring with
an infinite strictly increasing chain of primes whose union is the maximal ideal, that chain is
a non-quasicompact subset without a largest prime.

Everything holds for a `PreValuationRing`, which need not be a domain.

## References

* Peter Scholze and Jared Weinstein, *Berkeley Lectures on p-adic Geometry*, Lemma 18.3.2.
-/

public section

namespace PrimeSpectrum

variable {V : Type*} [CommRing V] [PreValuationRing V]

/-- The points of the prime spectrum of a valuation ring are pairwise comparable for
specialization, since its ideals are totally ordered. -/
theorem isChain_specializes (s : Set (PrimeSpectrum V)) : IsChain (· ⤳ ·) s := by
  intro p _ q _ _
  have := p.nontrivial
  simpa only [← le_iff_specializes, ← asIdeal_le_asIdeal] using
    total_of (· ≤ ·) p.asIdeal q.asIdeal

/-- A nonempty compact subset of the prime spectrum of a valuation ring has a largest prime: a
point of the subset that is a specialization of each of its points. -/
theorem exists_isGreatest_of_isCompact {K : Set (PrimeSpectrum V)} (hK : IsCompact K)
    (hne : K.Nonempty) : ∃ p, IsGreatest K p := by
  obtain ⟨p, hpK, hp⟩ := hK.exists_forall_specializes hne (isChain_specializes K)
  exact ⟨p, hpK, fun q hq ↦ (le_iff_specializes q p).2 (hp q hq)⟩

end PrimeSpectrum
