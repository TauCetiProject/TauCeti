/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Cone
public import TauCeti.AlgebraicTopology.SimplicialComplex.Product

/-!
# Collapsing ordered simplicial cylinders

If a complex is a cone whose apex is the greatest vertex, then its ordered cylinder is again a
cone: its apex is the pair of the original apex with the terminal interval vertex. Consequently a
finite such cylinder collapses to that apex. In particular this applies to the full simplex,
supplying a first nontrivial family for which the conclusion of Zeeman's conjecture holds and
checking that the ordered-product convention and the collapse API fit together.

The ordered cylinder is the staircase triangulation from
`TauCeti.AlgebraicTopology.SimplicialComplex.Product`; collapse and the theorem that finite cones
collapse are from `TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Cone`. The argument is the
standard observation that every vertex of a full ordered simplex lies below its greatest vertex.

## Main results

* `AbstractSimplicialComplex.isCone_orderedCylinder_of_isCone`: taking the ordered cylinder
  preserves a cone whose apex is greatest.
* `AbstractSimplicialComplex.isCone_orderedCylinder_top`: the full-simplex specialization.
* `AbstractSimplicialComplex.collapsesTo_point_orderedCylinder_top`: a finite such cylinder
  collapses to its greatest terminal vertex.
* `AbstractSimplicialComplex.collapsible_orderedCylinder_top`: a finite such cylinder is
  collapsible.
-/

public section

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι] [OrderTop ι]

/-- The ordered cylinder of a cone whose apex is the greatest vertex is a cone with apex the pair
of that vertex and the terminal endpoint of the interval. -/
theorem isCone_orderedCylinder_of_isCone {K : AbstractSimplicialComplex ι}
    (hK : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex ⊤) :
    PreAbstractSimplicialComplex.IsCone
      K.orderedCylinder.toPreAbstractSimplicialComplex (⊤, (1 : Fin 2)) := by
  refine ⟨K.orderedCylinder.singleton_mem _, ?_⟩
  intro σ hσ
  rw [orderedCylinder_toPreAbstractSimplicialComplex] at hσ ⊢
  rw [PreAbstractSimplicialComplex.mem_orderedProd_iff] at hσ ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.image_insert, Prod.fst] using hK.insert_mem hσ.1
  · exact Finset.image_nonempty.mpr (Finset.insert_nonempty _ _)
  · rw [Finset.coe_insert]
    exact hσ.2.2.insert fun p _ _ ↦ Or.inr ⟨le_top, Fin.le_last p.2⟩

/-- The ordered cylinder of the full abstract simplex is a cone with apex the greatest vertex at
the terminal endpoint of the interval. -/
theorem isCone_orderedCylinder_top :
    PreAbstractSimplicialComplex.IsCone
      (orderedCylinder (⊤ : AbstractSimplicialComplex ι)).toPreAbstractSimplicialComplex
      (⊤, (1 : Fin 2)) := by
  apply isCone_orderedCylinder_of_isCone
  exact ⟨Finset.singleton_nonempty _, fun _ _ ↦ Finset.insert_nonempty _ _⟩

/-- The ordered cylinder of a cone with greatest apex on a finite vertex type collapses to the
corresponding terminal apex. -/
theorem collapsesTo_point_orderedCylinder_of_isCone [Finite ι]
    {K : AbstractSimplicialComplex ι}
    (hK : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex ⊤) :
    PreAbstractSimplicialComplex.CollapsesTo K.orderedCylinder.toPreAbstractSimplicialComplex
      (PreAbstractSimplicialComplex.point (⊤, (1 : Fin 2))) := by
  classical
  let _ := Fintype.ofFinite ι
  exact (isCone_orderedCylinder_of_isCone hK).collapsesTo_point (Set.toFinite _)

/-- The ordered cylinder of a cone with greatest apex on a finite vertex type is collapsible. -/
theorem collapsible_orderedCylinder_of_isCone [Finite ι] {K : AbstractSimplicialComplex ι}
    (hK : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex ⊤) :
    PreAbstractSimplicialComplex.Collapsible K.orderedCylinder.toPreAbstractSimplicialComplex :=
  PreAbstractSimplicialComplex.collapsible_iff.mpr
    ⟨(⊤, (1 : Fin 2)), collapsesTo_point_orderedCylinder_of_isCone hK⟩

/-- The ordered cylinder of a full simplex on a finite vertex type collapses to its greatest
vertex at the terminal endpoint. -/
theorem collapsesTo_point_orderedCylinder_top [Finite ι] :
    PreAbstractSimplicialComplex.CollapsesTo
      (orderedCylinder (⊤ : AbstractSimplicialComplex ι)).toPreAbstractSimplicialComplex
      (PreAbstractSimplicialComplex.point (⊤, (1 : Fin 2))) :=
  collapsesTo_point_orderedCylinder_of_isCone
    ⟨Finset.singleton_nonempty _, fun _ _ ↦ Finset.insert_nonempty _ _⟩

/-- The ordered cylinder of a full simplex on a finite vertex type is collapsible. -/
theorem collapsible_orderedCylinder_top [Finite ι] :
    PreAbstractSimplicialComplex.Collapsible
      (orderedCylinder (⊤ : AbstractSimplicialComplex ι)).toPreAbstractSimplicialComplex :=
  collapsible_orderedCylinder_of_isCone
    ⟨Finset.singleton_nonempty _, fun _ _ ↦ Finset.insert_nonempty _ _⟩

end AbstractSimplicialComplex
