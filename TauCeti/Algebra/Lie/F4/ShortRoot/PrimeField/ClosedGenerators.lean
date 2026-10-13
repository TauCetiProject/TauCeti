/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Carrier
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic

/-!
# Closed generators of the short-root F₄ carrier over 𝔽₂

The eight numbered simple-root maps and the weight-torus map into the prime-field short-root
carrier are closed immersions. Their parametrizations therefore identify closed copies of the
additive group and of the rank-four split torus inside the carrier, over nonreduced value algebras
as well as fields. These are the closed-subgroup inputs needed to recognize the carrier's torus
and root datum in a pinned-group comparison.

The coordinate maps of the integral root subgroups are surjective by their explicit matrix
coordinates, while the twenty-six short-root weights span the full character lattice. Base change
to `𝔽₂` preserves both surjections without a flatness hypothesis, and factoring the resulting
maps through the subgroup generated over `𝔽₂` preserves them again.

The integral root-coordinate calculation is in `TauCeti.Algebra.Lie.F4.ShortRoot.Carrier`; the
weight-span theorem is in
`TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.F4.ShortRootWeight.Basic`. The
organization follows the prime-field short-root type-`G₂` carrier.

## Main declarations

* `TauCeti.F4ShortRoot.PrimeField.generator_surjective`: every generating coordinate map is
  surjective.
* `TauCeti.F4ShortRoot.PrimeField.isClosedImmersion_rootSubgroup`: the numbered root-subgroup
  maps are closed immersions.
* `TauCeti.F4ShortRoot.PrimeField.isClosedImmersion_weightTorus`: the weight-torus map is a closed
  immersion.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

/-- Each reduced generating coordinate map is surjective: the eight simple-root generators
parametrize closed copies of `𝔾ₐ`, and the torus generator parametrizes a closed split torus. -/
theorem generator_surjective (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    Function.Surjective (generator j).hom := by
  rcases j with k | ⟨⟩
  · rw [generator_inl, kostantRootSubgroupBaseChangePresentationCoordinateMap_def]
    exact _root_.CommHopfAlgCat.baseChangeMap_surjective_of_iso _
      (_root_.TauCeti.F4ShortRoot.representedRootSubgroupCoordinateMap_surjective k)
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ (ZMod 2) 26).symm
      (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ (ZMod 2))
  · rw [generator_inr, GeneralLinear.weightTorusBaseChangeCoordinateMap_eq]
    exact GeneralLinear.weightTorusCoordinateMap_surjective f4ShortRootWeight
      span_range_f4ShortRootWeight_eq_top

private theorem isClosedImmersion_eqToHom_comp_generator
    (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) {G : Grp (Over (Spec (CommRingCat.of (ZMod 2))))}
    (hG : G = (hopfSpec (CommRingCat.of (ZMod 2))).obj (Opposite.op (generatorCodomain j))) :
    IsClosedImmersion (eqToHom hG ≫
      GeneralLinear.generatorToGeneratedGroupScheme 26 generator j).hom.hom.left := by
  rw [← closedSubgroupMorphismProperty_iff (Spec (CommRingCat.of (ZMod 2))),
    (closedSubgroupMorphismProperty _).cancel_left_of_respectsIso]
  apply (closedSubgroupMorphismProperty_iff _ _).2
  exact GeneralLinear.isClosedImmersion_generatorToGeneratedGroupScheme_of_surjective
    26 generator j (generator_surjective j)

/-- Every numbered positive or negative simple-root map is a closed immersion into the
short-root carrier over `𝔽₂`. -/
instance isClosedImmersion_rootSubgroup (k : Fin 4 ⊕ Fin 4) :
    IsClosedImmersion (rootSubgroup k).hom.hom.left := by
  rw [rootSubgroup_def]
  exact isClosedImmersion_eqToHom_comp_generator (.inl k) _

/-- The rank-four weight-torus map is a closed immersion into the short-root carrier over `𝔽₂`.
This asserts that it is a split torus subgroup, without asserting maximality. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion weightTorus.hom.hom.left := by
  rw [weightTorus_def]
  exact isClosedImmersion_eqToHom_comp_generator (.inr ()) _

end TauCeti.F4ShortRoot.PrimeField
