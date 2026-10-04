/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Carrier
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup

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

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.

The integral root-coordinate calculation and weight-span theorem are from
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`. The organization follows
`TauCeti.Algebra.Lie.E7.Minuscule.ClosedGenerators`, using the general generated-subgroup
closed-immersion criterion rather than a new presentation of the carrier.
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
  · have hroot : Function.Surjective
        (kostantRootSubgroupCoordinateMap
          (TauCeti.serreRootGenerator CartanMatrix.G₂) (TauCeti.serreH ℚ CartanMatrix.G₂)
          rep lattice.toAddSubgroup rep_kostantForm_mem_lattice k
          (isNilpotent_rep_serreRootGenerator k) latticeBasis).hom := by
      rw [← mkQuotient_comp_kostantRootSubgroupToralCoordinateMap
        (TauCeti.serreRootGenerator CartanMatrix.G₂) (TauCeti.serreH ℚ CartanMatrix.G₂)
        rep lattice.toAddSubgroup rep_kostantForm_mem_lattice
        isNilpotent_rep_serreRootGenerator latticeBasis weight k,
        _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
      exact (IntegralToralClosure.rootSubgroupCoordinateMap_surjective k).comp
        (CommHopfAlgCat.mkQuotient_surjective _ _)
    rw [generator_inl, kostantRootSubgroupBaseChangePresentationCoordinateMap_def,
      _root_.CommHopfAlgCat.hom_comp, _root_.CommHopfAlgCat.hom_comp,
      BialgHom.coe_comp, BialgHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).2.comp
      ((CommHopfAlgCat.baseChangeMap_surjective _ hroot).comp
        (ConcreteCategory.bijective_of_isIso _).2)
  · rw [generator_inr, GeneralLinear.weightTorusBaseChangeCoordinateMap_eq]
    exact GeneralLinear.weightTorusCoordinateMap_surjective weight span_range_weight_eq_top

/-- Every numbered positive or negative simple-root map is a closed immersion into the
short-root carrier over `𝔽₃`. -/
instance isClosedImmersion_rootSubgroup (k : Fin 2 ⊕ Fin 2) :
    IsClosedImmersion (rootSubgroup k).hom.hom.left := by
  rw [← closedSubgroupMorphismProperty_iff (Spec (CommRingCat.of (ZMod 3))),
    rootSubgroup_def,
    (closedSubgroupMorphismProperty _).cancel_left_of_respectsIso,
    (closedSubgroupMorphismProperty _).cancel_right_of_respectsIso]
  apply (closedSubgroupMorphismProperty_iff _ _).2
  exact GeneralLinear.isClosedImmersion_generatorToGeneratedGroupScheme_of_surjective
    7 generator (.inl k) (generator_surjective (.inl k))

/-- The rank-two weight-torus map is a closed immersion into the short-root carrier over
`𝔽₃`. This asserts that it is a split torus subgroup, without asserting maximality. -/
instance isClosedImmersion_weightTorus : IsClosedImmersion weightTorus.hom.hom.left := by
  rw [← closedSubgroupMorphismProperty_iff (Spec (CommRingCat.of (ZMod 3))),
    weightTorus_def,
    (closedSubgroupMorphismProperty _).cancel_left_of_respectsIso,
    (closedSubgroupMorphismProperty _).cancel_right_of_respectsIso]
  apply (closedSubgroupMorphismProperty_iff _ _).2
  exact GeneralLinear.isClosedImmersion_generatorToGeneratedGroupScheme_of_surjective
    7 generator (.inr ()) (generator_surjective (.inr ()))

end TauCeti.G2ShortRoot.PrimeField
