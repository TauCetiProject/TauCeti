/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Flatness of the local homomorphism at a pair of primes

For an `R`-algebra `S` and primes `q` of `S` and `p = q ∩ R` of `R`, the local homomorphism
`R_p → S_q` is flat iff `S_q` is flat over `R`: flatness over `R_p` and over `R` agree for an
`R_p`-module, by Mathlib's `Module.flat_iff_of_isLocalization`. Stalk maps of morphisms of affine
schemes are such local homomorphisms, so this is how flatness is read off from a stalk.

When `S` is flat over `R`, the local homomorphism `R_p → S_q` is moreover faithfully flat, so
extending an ideal of `R` to `S_q` and contracting it back to `R` gives the same ideal as doing so
through `R_p`.

## Main results

* `Localization.flat_localRingHom_iff`: the local homomorphism `R_p → S_q` is flat iff `S_q` is
  flat over `R`.
* `Ideal.comap_map_localization_atPrime_of_flat`: for `S` flat over `R`, an ideal `I` of `R` and a
  prime `q` of `S` over `p`, an element of `R` lies in `I S_q` iff it lies in `I R_p`.
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

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- For a flat `R`-algebra `S` and a prime `q` of `S` over `p`, an ideal `I` of `R` has the same
saturation at `q` as at `p`: an element of `R` lies in `I S_q` iff it lies in `I R_p`, since
`R_p → S_q` is faithfully flat. -/
theorem comap_map_localization_atPrime_of_flat [Module.Flat R S] (I : Ideal R) (q : Ideal S)
    [q.IsPrime] :
    (I.map (algebraMap R (Localization.AtPrime q))).comap
        (algebraMap R (Localization.AtPrime q)) =
      (I.map (algebraMap R (Localization.AtPrime (q.comap (algebraMap R S))))).comap
        (algebraMap R (Localization.AtPrime (q.comap (algebraMap R S)))) := by
  have : q.LiesOver (q.comap (algebraMap R S)) := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap R S)) q
  rw [IsScalarTower.algebraMap_eq R (Localization.AtPrime (q.comap (algebraMap R S)))
    (Localization.AtPrime q), ← Ideal.map_map, ← Ideal.comap_comap,
    Ideal.comap_map_eq_self_of_faithfullyFlat]

end Ideal
