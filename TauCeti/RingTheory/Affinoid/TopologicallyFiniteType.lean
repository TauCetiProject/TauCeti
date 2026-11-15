/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.ResidueField

import TauCeti.RingTheory.Affinoid.Continuity
import TauCeti.RingTheory.Huber.Restricted.Noetherian

/-!
# Affinoid algebras are the algebras topologically of finite type

Let `K` be a complete nonarchimedean field with a nontrivial absolute value. There are two
notions of an affinoid `K`-algebra in the library.

* The classical one, `TauCeti.IsAffinoidAlgebra K B`, is purely algebraic: `B` is a quotient of a
  Tate algebra `K⟨X₁, …, Xₙ⟩` as a `K`-algebra, with no norm or topology on `B`.
* Huber's one is topological: `B` is a topological `K`-algebra admitting an open quotient map of
  `K`-algebras from the completed Tate algebra, that is
  `TauCeti.Huber.IsTopologicallyFiniteType (algebraMap K B)` (Wedhorn, Definition 5.57). Together
  with its power-bounded subring `B°`, such an algebra is what Wedhorn's Definition 7.56 calls an
  affinoid `K`-algebra.

This file proves that the two notions agree on every complete ultrametric normed `K`-algebra `B`
(`TauCeti.Huber.isTopologicallyFiniteType_algebraMap_iff_isAffinoidAlgebra`). One direction holds
for any topology on `B` (`TauCeti.Huber.IsTopologicallyFiniteType.exists_surjective_algHom`). For
the other, every surjection `π : K⟨X₁, …, Xₙ⟩ → B` of `K`-algebras is automatically continuous
(`TauCeti.IsAffinoidAlgebra.continuous_algHom`). Read through the identification of the completed
Huber Tate algebra with the Gauss-normed one
(`TauCeti.Huber.restrictedMvPowerSeriesCompletionGaussAlgEquiv`), it is then a presentation in
Huber's sense by the open mapping theorem
(`TauCeti.Huber.isStrictlyTopologicallyFiniteType_of_surjective`). Thus every algebraic Tate
presentation of `B` induces its norm topology.

So the theory of algebras topologically of finite type applies to the classical affinoid algebras
with their Banach topology. In particular they are strongly noetherian Tate rings
(`TauCeti.IsAffinoidAlgebra.isStronglyNoetherian`), and their adic spectra are affinoid adic
spaces (`TauCeti.ValuationSpectrum.isAdic_presentationLimitPreAdicSpace_of_isAffinoidAlgebra`).

## Main results

* `TauCeti.IsAffinoidAlgebra.isTopologicallyFiniteType`: a complete ultrametric normed affinoid
  `K`-algebra is topologically of finite type over `K`.
* `TauCeti.Huber.isTopologicallyFiniteType_algebraMap_iff_isAffinoidAlgebra`: for a complete
  ultrametric normed `K`-algebra, being topologically of finite type over `K` is equivalent to
  being affinoid.
* `TauCeti.IsAffinoidAlgebra.isStronglyNoetherian`: a complete ultrametric normed affinoid
  `K`-algebra is strongly noetherian.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 5.57 and
  Definition 7.56.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1 and
  §6.1.3.
-/

public section

namespace TauCeti

open Huber

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]

namespace IsAffinoidAlgebra

/-- **A complete ultrametric normed affinoid algebra is topologically of finite type** (Wedhorn,
Definition 5.57): its norm topology is the quotient topology of a Tate presentation. Every
surjection `K⟨X₁, …, Xₙ⟩ → B` of `K`-algebras is a presentation in Huber's sense, by automatic
continuity and the open mapping theorem. -/
theorem isTopologicallyFiniteType (hB : IsAffinoidAlgebra K B) :
    IsTopologicallyFiniteType (algebraMap K B) := by
  obtain ⟨n, π, hπ⟩ := (isAffinoidAlgebra_iff K B).mp hB
  have := MvPowerSeries.isNoetherianRing_isRestricted_subring (K := K) (c := fun _ : Fin n ↦ 1)
  -- precompose with the identification of the completed Tate algebra with the Gauss-normed one
  let e := restrictedMvPowerSeriesCompletionGaussAlgEquiv (n := n) (R := K)
  have hc : Continuous (π.comp e.toAlgHom) := by
    simpa [e] using
      (hB.continuous_algHom π).comp continuous_restrictedMvPowerSeriesCompletionGaussEquiv
  exact (isStrictlyTopologicallyFiniteType_of_surjective (π.comp e.toAlgHom) hc.continuousAt
    (hπ.comp e.surjective)).isTopologicallyFiniteType

/-- **A complete ultrametric normed affinoid algebra is strongly noetherian**: being topologically
of finite type over the strongly noetherian Tate ring `K`, every completed Tate algebra over it is
noetherian. -/
theorem isStronglyNoetherian (hB : IsAffinoidAlgebra K B) : IsStronglyNoetherian B :=
  have : IsTateRing B := IsTateRing.of_normedAlgebra K B
  hB.isTopologicallyFiniteType.isStronglyNoetherian

end IsAffinoidAlgebra

/-- **Affinoid algebras are the algebras topologically of finite type.** A complete ultrametric
normed `K`-algebra `B` is topologically of finite type over `K` in Huber's sense (Wedhorn,
Definition 5.57) exactly when it is a quotient of a Tate algebra `K⟨X₁, …, Xₙ⟩` as a
`K`-algebra. -/
theorem Huber.isTopologicallyFiniteType_algebraMap_iff_isAffinoidAlgebra :
    IsTopologicallyFiniteType (algebraMap K B) ↔ IsAffinoidAlgebra K B :=
  ⟨fun h ↦ (isAffinoidAlgebra_iff K B).mpr h.exists_surjective_algHom,
    IsAffinoidAlgebra.isTopologicallyFiniteType⟩

end TauCeti
