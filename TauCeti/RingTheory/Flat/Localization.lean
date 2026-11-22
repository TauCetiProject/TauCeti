/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness and localization

For an `R`-algebra `S` and primes `q` of `S` and `p = q ∩ R` of `R`, the local homomorphism
`R_p → S_q` is flat iff `S_q` is flat over `R`: flatness over `R_p` and over `R` agree for an
`R_p`-module, by Mathlib's `Module.flat_iff_of_isLocalization`. Stalk maps of morphisms of affine
schemes are such local homomorphisms, so this is how flatness is read off from a stalk.

Precomposing a ring homomorphism out of a localization with the localization map preserves and
reflects flatness (`RingHom.Flat.comp_algebraMap_isLocalization_iff`), allowing flatness of an
endomorphism of a localization to be checked after restricting along the localization map.

## Main results

* `Localization.flat_localRingHom_iff`: the local homomorphism `R_p → S_q` is flat iff `S_q` is
  flat over `R`.
* `RingHom.Flat.comp_algebraMap_isLocalization_iff`: precomposing a ring homomorphism out of a
  localization with the localization map preserves and reflects flatness.
-/

public section

namespace Localization

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The local homomorphism `R_p → S_q` at primes `q` over `p` is flat iff `S_q` is flat over
`R`. -/
theorem flat_localRingHom_iff (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (h : p = q.comap (algebraMap R S)) :
    (localRingHom p q (algebraMap R S) h).Flat ↔ Module.Flat R (Localization.AtPrime q) := by
  have : q.LiesOver p := ⟨h⟩
  let := AtPrime.algebraOfLiesOver p q
  rw [← Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl]
  exact RingHom.flat_algebraMap_iff

end Localization

namespace RingHom

/-- Precomposing a ring homomorphism out of a localization with the localization map preserves and
reflects flatness. Stated for ring homomorphisms without an `Algebra Rₘ T` instance so that it
applies to endomorphisms `Rₘ →+* Rₘ`. -/
theorem Flat.comp_algebraMap_isLocalization_iff {R Rₘ T : Type*} [CommRing R] [CommRing Rₘ]
    [CommRing T] (M : Submonoid R) [Algebra R Rₘ] [IsLocalization M Rₘ] (f : Rₘ →+* T) :
    (f.comp (algebraMap R Rₘ)).Flat ↔ f.Flat := by
  algebraize_only [f, f.comp (algebraMap R Rₘ)]
  exact (Module.flat_iff_of_isLocalization Rₘ M T).symm

end RingHom
