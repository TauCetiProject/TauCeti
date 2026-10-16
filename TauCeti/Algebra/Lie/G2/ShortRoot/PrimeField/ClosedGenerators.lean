/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Carrier
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic

/-!
# Closed generators of the short-root G₂ carrier over 𝔽₃

The four numbered simple-root maps and the weight-torus map into the prime-field short-root
carrier are closed immersions. Thus their parametrizations identify closed copies of the
additive group and of the rank-two split torus inside the carrier, including on nonreduced
value algebras. This supplies the closed-subgroup condition needed to use these maps as root
subgroups and as a candidate maximal torus in a pinned-group comparison.

Surjectivity of the generating coordinate maps follows from the integral root-matrix
calculations and the fact that the seven weights span the full character lattice. Scalar
extension preserves that surjectivity, without requiring flatness of ℤ → 𝔽₃. Factoring through
the separately generated prime-field carrier preserves it as well.

The integral root-coordinate calculation is from
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`, and the weight-span theorem
is from `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.ShortRootWeight`.
The organization follows `TauCeti.Algebra.Lie.E7.Minuscule.ClosedGenerators`, using the general
generated-subgroup closed-immersion criterion rather than a new presentation of the carrier.

## Main declarations

* `TauCeti.G2ShortRoot.PrimeField.generator_surjective`: each generating coordinate map is
  surjective.
* `TauCeti.G2ShortRoot.PrimeField.isClosedImmersion_rootSubgroup`: the numbered root-subgroup
  maps are closed immersions.
* `TauCeti.G2ShortRoot.PrimeField.isClosedImmersion_weightTorus`: the weight-torus map is a
  closed immersion.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.G2ShortRoot.PrimeField

/-- Each reduced generating coordinate map is surjective: the four simple-root generators
parametrize closed copies of `𝔾ₐ`, and the torus generator parametrizes a closed split torus. -/
theorem generator_surjective (j : (Fin 2 ⊕ Fin 2) ⊕ Unit) :
    Function.Surjective (generator j).hom := by
  rcases j with k | ⟨⟩
  · rw [generator_inl, kostantRootSubgroupBaseChangePresentationCoordinateMap_def]
    exact _root_.CommHopfAlgCat.baseChangeMap_surjective_of_iso _
      (IntegralToralClosure.representedRootSubgroupCoordinateMap_surjective k)
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ (ZMod 3) 7).symm
      (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso ℤ (ZMod 3))
  · rw [generator_inr, GeneralLinear.weightTorusBaseChangeCoordinateMap_eq]
    exact GeneralLinear.weightTorusCoordinateMap_surjective weight span_range_weight_eq_top

private theorem isClosedImmersion_eqToHom_comp_generator
    (j : (Fin 2 ⊕ Fin 2) ⊕ Unit) {G : Grp (Over (Spec (CommRingCat.of (ZMod 3))))}
    (hG : G = (hopfSpec (CommRingCat.of (ZMod 3))).obj (Opposite.op (generatorCodomain j))) :
    IsClosedImmersion (eqToHom hG ≫
      GeneralLinear.generatorToGeneratedGroupScheme 7 generator j ≫
      eqToHom groupScheme_eq_generatedGroupScheme.symm).hom.hom.left := by
  rw [← closedSubgroupMorphismProperty_iff (Spec (CommRingCat.of (ZMod 3))),
    (closedSubgroupMorphismProperty _).cancel_left_of_respectsIso,
    (closedSubgroupMorphismProperty _).cancel_right_of_respectsIso]
  apply (closedSubgroupMorphismProperty_iff _ _).2
  exact GeneralLinear.isClosedImmersion_generatorToGeneratedGroupScheme_of_surjective
    7 generator j (generator_surjective j)

/-- Every numbered positive or negative simple-root map is a closed immersion into the
short-root carrier over `𝔽₃`. -/
instance isClosedImmersion_rootSubgroup (k : Fin 2 ⊕ Fin 2) :
    IsClosedImmersion (rootSubgroup k).hom.hom.left := by
  rw [rootSubgroup_def]
  exact isClosedImmersion_eqToHom_comp_generator (.inl k) _

/-- The rank-two weight-torus map is a closed immersion into the short-root carrier over
`𝔽₃`. This asserts that it is a split torus subgroup, without asserting maximality. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion weightTorus.hom.hom.left := by
  rw [weightTorus_def]
  exact isClosedImmersion_eqToHom_comp_generator (.inr ()) _

end TauCeti.G2ShortRoot.PrimeField
