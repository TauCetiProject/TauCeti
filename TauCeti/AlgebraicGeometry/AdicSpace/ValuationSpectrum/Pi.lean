/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic

/-!
# Valuations on finite products of rings

A point of the valuation spectrum of a finite product `∏ i, R i` of commutative rings is the
pullback of a point of some factor `Spv (R i)` along the projection `∏ i, R i → R i`
(`TauCeti.ValuationSpectrum.exists_comap_evalRingHom_eq`). Geometrically, `Spv (∏ i, R i)` is
covered by the images of the `Spv (R i)`, as `Spec (∏ i, R i)` is the disjoint union of the
`Spec (R i)`.

The support of `v` is a prime of `∏ i, R i`, so it is pulled back from a prime of some factor
`R i` (`PrimeSpectrum.exists_comap_evalRingHom_eq`). In particular it contains the kernel of the
projection onto `R i`, so `v` factors through that surjection
(`TauCeti.ValuationSpectrum.range_comap_of_surjective`).

Finiteness of the index set matters: on an infinite product, a valuation can factor through the
quotient by a nonprincipal ultrafilter and through no single factor.

This identifies the points of the fibre square of a finite étale torsor, which is a finite product
of copies of the torsor.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]

/-- **Points of the valuation spectrum of a finite product.** Every point of
`Spv (∏ i, R i)` is pulled back from a point of `Spv (R i)` along the projection to some factor
`R i`. -/
theorem exists_comap_evalRingHom_eq [Finite ι] (v : Spv (∀ i, R i)) :
    ∃ i, ∃ w : Spv (R i), comap (Pi.evalRingHom R i) w = v := by
  -- the support of `v` is pulled back from a prime of a single factor `R i`
  obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq ⟨v.supp, inferInstance⟩
  have hker : RingHom.ker (Pi.evalRingHom R i) ≤ v.supp := by
    have h := Ideal.ker_le_comap (K := q.asIdeal) (Pi.evalRingHom R i)
    rwa [← PrimeSpectrum.comap_asIdeal, hq] at h
  have hsurj : Function.Surjective (Pi.evalRingHom R i) := Function.surjective_eval i
  obtain ⟨w, hw⟩ : v ∈ Set.range (comap (Pi.evalRingHom R i)) := by
    rwa [range_comap_of_surjective hsurj]
  exact ⟨i, w, hw⟩

end TauCeti.ValuationSpectrum
