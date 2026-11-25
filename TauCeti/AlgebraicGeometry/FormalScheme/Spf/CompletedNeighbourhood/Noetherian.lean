/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FormalScheme.Spf.CompletedAtPrime.Basic

/-!
# Noetherianity of the completed localisations at an open prime

Let `A` be a noetherian adic ring with ideal of definition `I`, and let `p` be an open prime of
`A`, corresponding to a prime ideal `𝔭 ⊇ I`. This file proves that the colimit
`colim_{f ∉ 𝔭} A_{f}` of the completed localisations of `A` over the basic open neighbourhoods
`D(f)` of `p` in `Spf A` is a noetherian ring (EGA I, Ch. 0, 7.6.17). This colimit is the algebraic
model of the stalk of `Spf A` at `p` (EGA I, Ch. I, 10.1.6).

A filtered colimit of noetherian rings need not be noetherian. Here noetherianity descends from
the completed localisation `Â_𝔭`, the completion of the local ring `A_𝔭` along `I A_𝔭`, which is
noetherian and faithfully flat over the colimit
(`TauCeti.FormalScheme.Spf.faithfullyFlat_colimitToCompletedAtPrime`). A ring with a faithfully flat
noetherian algebra is noetherian.

## Main results

* `TauCeti.FormalScheme.Spf.completedNeighbourhood_noetherian`: for noetherian `A`, the colimit
  `colim_{f ∉ 𝔭} A_{f}` is a noetherian ring.

## References

* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 7.6.17, and
  Ch. I, 10.1.6.
-/

public section

universe u

open CategoryTheory Limits

namespace TauCeti.FormalScheme.Spf

open AdicRing

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsAdicRing A]
  (p : carrier A)

/-- The colimit `colim_{f ∉ p} A_{f}` of the completed localisations of a noetherian adic ring `A`
over the basic open neighbourhoods of an open prime `p` is a noetherian ring (EGA I, Ch. 0,
7.6.17). -/
instance completedNeighbourhood_noetherian [IsNoetherianRing A] :
    IsNoetherianRing (colimit (completedNeighbourhoodDiagram p) : CommRingCat) := by
  -- noetherianity descends along the faithfully flat map to the noetherian ring `Â_𝔭`
  algebraize [colimitToCompletedAtPrime p]
  have : Module.FaithfullyFlat _ (CompletedAtPrime p) := faithfullyFlat_colimitToCompletedAtPrime p
  exact isNoetherianRing_iff.mpr
    (Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
      (A := CompletedAtPrime p)
      (isNoetherian_of_linearEquiv (TensorProduct.AlgebraTensorModule.rid _ _ _).symm))

end TauCeti.FormalScheme.Spf
