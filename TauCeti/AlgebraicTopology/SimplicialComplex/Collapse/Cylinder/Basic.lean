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

* `AbstractSimplicialComplex.collapsesTo_point_orderedCylinder_of_isCone`: a finite cone's
  ordered cylinder collapses to its terminal apex.
* `AbstractSimplicialComplex.collapsible_orderedCylinder_of_isCone`: a finite cone's ordered
  cylinder is collapsible.
* `AbstractSimplicialComplex.collapsesTo_point_orderedCylinder_top`: a finite such cylinder
  collapses to its greatest terminal vertex.
* `AbstractSimplicialComplex.collapsible_orderedCylinder_top`: a finite such cylinder is
  collapsible.
-/

public section

namespace AbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι]

/-- The ordered cylinder of a finite cone whose apex bounds every vertex collapses to the
corresponding terminal apex. -/
theorem collapsesTo_point_orderedCylinder_of_isCone {v : ι}
    {K : AbstractSimplicialComplex ι}
    (hfin : K.faces.Finite)
    (hK : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex v)
    (hv : ∀ w, ({w} : Finset ι) ∈ K → w ≤ v) :
    PreAbstractSimplicialComplex.CollapsesTo K.orderedCylinder.toPreAbstractSimplicialComplex
      (PreAbstractSimplicialComplex.point (v, (1 : Fin 2))) :=
  (isCone_orderedCylinder_of_isCone hK hv).collapsesTo_point
    (finite_faces_orderedCylinder hfin)

/-- The ordered cylinder of a finite cone whose apex bounds every vertex is collapsible. -/
theorem collapsible_orderedCylinder_of_isCone {v : ι} {K : AbstractSimplicialComplex ι}
    (hfin : K.faces.Finite)
    (hK : PreAbstractSimplicialComplex.IsCone K.toPreAbstractSimplicialComplex v)
    (hv : ∀ w, ({w} : Finset ι) ∈ K → w ≤ v) :
    PreAbstractSimplicialComplex.Collapsible K.orderedCylinder.toPreAbstractSimplicialComplex :=
  (isCone_orderedCylinder_of_isCone hK hv).collapsible (finite_faces_orderedCylinder hfin)

variable [OrderTop ι]

/-- The ordered cylinder of a full simplex on a finite vertex type collapses to its greatest
vertex at the terminal endpoint. -/
theorem collapsesTo_point_orderedCylinder_top [Finite ι] :
    PreAbstractSimplicialComplex.CollapsesTo
      (orderedCylinder (⊤ : AbstractSimplicialComplex ι)).toPreAbstractSimplicialComplex
      (PreAbstractSimplicialComplex.point (⊤, (1 : Fin 2))) := by
  classical
  let _ := Fintype.ofFinite ι
  exact isCone_orderedCylinder_top.collapsesTo_point (Set.toFinite _)

/-- The ordered cylinder of a full simplex on a finite vertex type is collapsible. -/
theorem collapsible_orderedCylinder_top [Finite ι] :
    PreAbstractSimplicialComplex.Collapsible
      (orderedCylinder (⊤ : AbstractSimplicialComplex ι)).toPreAbstractSimplicialComplex :=
  PreAbstractSimplicialComplex.collapsible_iff.mpr
    ⟨(⊤, (1 : Fin 2)), collapsesTo_point_orderedCylinder_top⟩

end AbstractSimplicialComplex
