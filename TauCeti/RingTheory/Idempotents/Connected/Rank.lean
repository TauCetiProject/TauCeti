/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Spectrum.Prime.Rank.Decomposition

/-!
# Connected prime spectra via free projectives

Over a nontrivial commutative ring `R`, if every finitely generated projective `R`-module is free,
then every finitely generated projective `R`-module has constant stalk rank, so `Spec R` is
connected (`TauCeti.connectedSpace_primeSpectrum_of_forall_free`).

## Main results

* `TauCeti.connectedSpace_primeSpectrum_of_forall_free`: if every finitely generated projective
  module over a nontrivial commutative ring `R` is free, then `Spec R` is connected.
-/

public section

universe u

namespace TauCeti

/-- If `R` is nontrivial and every finitely generated projective `R`-module is free, then `Spec R`
is connected. -/
theorem connectedSpace_primeSpectrum_of_forall_free (R : Type u) [CommRing R] [Nontrivial R]
    (hfree : ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P]
      [Module.Projective R P], Module.Free R P) :
    ConnectedSpace (PrimeSpectrum R) :=
  (PrimeSpectrum.connectedSpace_iff_forall_exists_rankAtStalk_eq (R := R)).2
    fun P _ _ _ _ ↦
      have := hfree P
      ⟨Module.finrank R P, fun p ↦
        congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := P)) p⟩

end TauCeti
