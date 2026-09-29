/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Scheme
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Base change of the bundled coordinate Hopf algebra of `𝔾ₐ`

`TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv` identifies `K ⊗[k] O(𝔾ₐ)` with the coordinate
bialgebra of `𝔾ₐ` over `K`. This file bundles that equivalence as an isomorphism in
`CommHopfAlgCat K`, so that the base change of `𝔾ₐ` over `k` *is* `𝔾ₐ` over `K` as a commutative
Hopf algebra, and not merely as a bialgebra.

Over a domain, its prime spectrum is connected, and the bundled base-change isomorphism transports
that connectedness to every scalar extension whose target is a domain.

The antipode needs no separate argument: a bialgebra map between Hopf algebras automatically
commutes with the antipodes, which is what `CommHopfAlgCat.isoMk` uses.

The bundled form is what a consumer of a *presentation* needs. It is an abbreviation so that the
existing simp lemmas for `gaScalarTensorBialgEquiv` apply directly to its forward and inverse
maps. A closed subgroup scheme of a group scheme over `k` is a Hopf-ideal quotient of its coordinate
Hopf algebra; base-changing that presentation produces a quotient of `K ⊗[k] O(G)`, and reading the
result as a closed subgroup scheme over `K` means transporting along an isomorphism in
`CommHopfAlgCat K`. This is the
`𝔾ₐ` companion of `TauCeti.GeneralLinear.coordinateHopfAlgebraBaseChangeIso`, and, as there, the
extension ring's carrier universe must contain the base ring's; the unbundled bialgebra
equivalence has no such restriction.

## Main declarations

* `TauCeti.AdditiveGroup.coordinateHopfAlgebraBaseChangeIso`: the bundled isomorphism.
* `TauCeti.AdditiveGroup.connectedSpace_primeSpectrum_coordinateHopfAlgebra`: the coordinate
  algebra has connected prime spectrum over a domain.
* `TauCeti.AdditiveGroup.connectedSpace_primeSpectrum_baseChange_coordinateHopfAlgebra`:
  the base-changed coordinate algebra has connected prime spectrum over a domain.

## References

The underlying equivalence is `TauCeti.AdditiveGroup.gaScalarTensorBialgEquiv`, itself the
rank-one case of `TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`. This advances the base-change
half of Layer 9 of `TauCetiRoadmap/ReductiveGroups/README.md`. See W. C. Waterhouse,
*Introduction to Affine Group Schemes*, §1, and J. S. Milne, *Algebraic Groups* (2017), §2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.AdditiveGroup

universe u v

variable (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [Algebra k K]

/-- Base change of the bundled coordinate Hopf algebra of `𝔾ₐ` is the coordinate Hopf algebra of
`𝔾ₐ` over the new base. -/
noncomputable abbrev coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra k) ≅ coordinateHopfAlgebra K :=
  _root_.CommHopfAlgCat.isoMk (gaScalarTensorBialgEquiv (k := k) (K := K))

/-- The coordinate Hopf algebra of `𝔾ₐ` has connected prime spectrum over a domain. -/
theorem connectedSpace_primeSpectrum_coordinateHopfAlgebra
    (K : Type u) [CommRing K] [IsDomain K] :
    ConnectedSpace (PrimeSpectrum (coordinateHopfAlgebra K)) := by
  change ConnectedSpace (PrimeSpectrum (SymmetricAlgebra K K))
  infer_instance

/-- The base change of the coordinate Hopf algebra of `𝔾ₐ` has connected prime spectrum
when the extension ring is a domain. -/
theorem connectedSpace_primeSpectrum_baseChange_coordinateHopfAlgebra
    (k : Type u) (K : Type max u v) [CommRing k] [CommRing K] [IsDomain K] [Algebra k K] :
    ConnectedSpace (PrimeSpectrum
      (CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra k))) := by
  let e := coordinateHopfAlgebraBaseChangeIso k K
  have := connectedSpace_primeSpectrum_coordinateHopfAlgebra K
  exact connectedSpace_primeSpectrum_of_injective e.hom.hom.toAlgHom.toRingHom
    (ConcreteCategory.bijective_of_isIso e.hom).1

end TauCeti.AdditiveGroup
