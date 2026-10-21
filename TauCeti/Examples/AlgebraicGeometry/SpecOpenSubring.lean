/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.SpecOpenSubring

/-!
# Examples: the spectrum of an open subring of a Huber ring

These examples test the comparison of `Spec A` and `Spec B` for an open subring `B` of a Huber
ring `A` in its three degenerate regimes. Over a Tate ring no prime is open, so the isomorphism
of `Subring.isIso_morphismRestrict_nonOpenPrimes` has all of `Spec A` as its source, even
when `B` has open primes. Over a discrete ring every prime is open, so the non-open locus is
empty. For the full subring the comparison is the restriction of an isomorphism.

## References

* R. Huber, *Continuous valuations*, Math. Z. 212 (1993), Lemma 3.7.
-/

open AlgebraicGeometry CategoryTheory TauCeti.Huber

section Tate

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]

-- No prime of a Tate ring is open, so every prime of `A` lies over a non-open prime of `B`.
example {B : Subring A} (hB : IsOpen (B : Set A)) (p : PrimeSpectrum A) :
    p ∈ Spec.map (CommRingCat.ofHom B.subtype) ⁻¹ᵁ B.nonOpenPrimes :=
  (B.mem_preimage_nonOpenPrimes hB).mpr fun hp ↦
    p.isPrime.ne_top ((IsTateRing.isOpen_iff_eq_top _).mp hp)

end Tate

section Discrete

variable {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

-- Every prime of a subring of a discrete ring is open, so the non-open locus is empty.
example (B : Subring A) : B.nonOpenPrimes = ⊥ :=
  eq_bot_iff.mpr fun _ hq ↦ ((B.mem_nonOpenPrimes).mp hq) (isOpen_discrete _)

end Discrete

section Full

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

-- The full subring is open, so the comparison applies to it.
example :
    IsIso (Spec.map (CommRingCat.ofHom (⊤ : Subring A).subtype) ∣_ (⊤ : Subring A).nonOpenPrimes) :=
  (⊤ : Subring A).isIso_morphismRestrict_nonOpenPrimes (by simp)

end Full
