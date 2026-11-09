/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.RootSubgroup
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Primitive

/-!
# Closed simple-root subgroups of the full-weight Chevalley scheme

The numbered positive and negative simple-root morphisms into the full-weight Chevalley
scheme over `ℤ` are closed immersions. This is an integral statement, not just injectivity
on points over fields; it remains valid after arbitrary base change, including to nonreduced
rings and rings of small characteristic.

The morphisms are the existing `kostantRootSubgroupToToral` on
`TauCeti.DynkinType.scChevalleyDatum`, with target `TauCeti.DynkinType.chevalleyGroupScheme`.
No new root maps or ambient group are introduced. For each signed simple root, the fundamental
summand at its node supplies a primitive two-step string
(`TauCeti.DynkinType.exists_isPrimitive_scLattice_rootOperator`). The basis-independent criterion
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive`
then proves that the root coordinate map is surjective. Factoring through the coordinate algebra
of the toral closure preserves surjectivity. No change of weight basis or generation theorem
for field-valued points is needed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.DynkinType

open _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

local notation "D" => t.scChevalleyDatum ht

/-- Every numbered positive or negative simple-root morphism into the full-weight Chevalley
scheme is a closed immersion over `ℤ`. In particular its parameter is faithful over all
commutative value rings, not merely over fields. -/
instance isClosedImmersion_scChevalleyDatum_rootSubgroup (i : Fin t.rank ⊕ Fin t.rank) :
    IsClosedImmersion
      (kostantRootSubgroupToToral (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        (D).representation (D).lattice (D).representation_mem_lattice
        (D).isNilpotent_representation_rootGenerator (D).basis
        (D).coordinateWeight i).hom.hom.left := by
  apply isClosedImmersion_kostantRootSubgroupToToral_of_surjective
  apply kostantRootSubgroupToralCoordinateMap_surjective_of_surjective
  -- Expose the datum fields once, before using the primitive string on its actual lattice.
  dsimp only [scChevalleyDatum]
  -- Term elimination keeps the large represented-module signature out of tactic reversion.
  exact (t.exists_isPrimitive_scLattice_rootOperator ht i).elim fun v hv =>
    kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.scModule ht)) (t.scLattice ht).toAddSubgroup
      (t.kostantForm_apply_mem_scLattice ht) i
      (t.isNilpotent_representation_scModule_rootGenerator ht i) (t.scWeightBasis ht) v hv.1 hv.2

/-- The numbered simple-root morphisms of the full-weight datum are monomorphisms of group
schemes, so they can be used as subgroup objects. -/
instance mono_scChevalleyDatum_rootSubgroup (i : Fin t.rank ⊕ Fin t.rank) :
    Mono (kostantRootSubgroupToToral (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      (D).representation (D).lattice (D).representation_mem_lattice
      (D).isNilpotent_representation_rootGenerator (D).basis (D).coordinateWeight i) :=
  Grp.mono_of_mono_left _

end

end TauCeti.DynkinType
