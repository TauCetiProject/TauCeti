/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Primitive
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Primitive

/-!
# Closed simple-root subgroups of a Chevalley group scheme

For **any** Chevalley datum `D`, the numbered positive and negative simple-root morphisms into
`D.groupScheme` over `ℤ` are closed immersions. This is an integral scheme-theoretic statement,
not merely injectivity on points over fields; it remains valid after arbitrary base change,
including to nonreduced rings and rings of small characteristic, and across all isogeny types.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.isClosedImmersion_kostantRootSubgroupToToral`: every numbered
  positive or negative simple-root morphism into `D.groupScheme` is a closed immersion over `ℤ`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory
open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-- Every numbered positive or negative simple-root morphism into the group scheme of a Chevalley
datum is a closed immersion over `ℤ`. -/
instance isClosedImmersion_kostantRootSubgroupToToral (i : Fin t.rank ⊕ Fin t.rank) :
    IsClosedImmersion
      (kostantRootSubgroupToToral (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
        D.representation D.lattice D.representation_mem_lattice
        D.isNilpotent_representation_rootGenerator D.basis
        D.coordinateWeight i).hom.hom.left := by
  apply isClosedImmersion_kostantRootSubgroupToToral_of_surjective
  apply kostantRootSubgroupToralCoordinateMap_surjective_of_surjective
  exact (D.exists_isPrimitive_kostantRootOperator i).elim fun m hm =>
    kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive_of_isCartanWeightVector
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice i
      (D.isNilpotent_representation_rootGenerator i) D.basis
      D.isCartanWeightVector_basis (t.lie_lieBasis_h_rootGenerator ht i)
      (t.rootGeneratorWeight_ne_zero ht i) m hm

end

end TauCeti.DynkinType.ChevalleyDatum
