/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.PL
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Sequence

/-!
# Collapsible triangulations of polyhedra

Simplicial collapsibility refers to a particular complex. Collapsibility of a PL polyhedron
instead allows a choice of triangulation: the polyhedron must be PL homeomorphic to the
polyhedron of a simplicially collapsible complex. This distinction matters when stating
collapse problems for products, since a chosen product triangulation need not itself admit
the desired collapse.

`HasCollapsibleTriangulation` expresses this existence condition using `PLHomeomorphic`,
not merely a topological homeomorphism. Its witnesses may use a different vertex type.
It is invariant under PL homeomorphism and implies contractibility of the weak polyhedron.
No converse from contractibility, or collapse of the original triangulation, is asserted.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology* (1972),
  Chapter 3, p. 39 (collapse of polyhedra).
* E. C. Zeeman, *On the dunce hat*, Topology 2 (1964), 341–358.
-/

public section

namespace PreAbstractSimplicialComplex

/-- The PL polyhedron of `K` admits a simplicially collapsible triangulation with vertices
in universe `v`. The witnessing complex need not be the given triangulation `K`. -/
def HasCollapsibleTriangulation.{v, u} {ι : Type u}
    (K : PreAbstractSimplicialComplex ι) : Prop :=
  ∃ (κ : Type v) (L : PreAbstractSimplicialComplex κ), PLHomeomorphic K L ∧ Collapsible L

universe u v w

variable {ι : Type u} {κ : Type w} {K : PreAbstractSimplicialComplex ι}
  {L : PreAbstractSimplicialComplex κ}

/-- A collapsible triangulation consists of a PL identification with a collapsible complex. -/
theorem hasCollapsibleTriangulation_iff :
    HasCollapsibleTriangulation.{v} K ↔
      ∃ (κ : Type v) (L : PreAbstractSimplicialComplex κ),
        PLHomeomorphic K L ∧ Collapsible L := Iff.rfl

/-- A simplicially collapsible complex supplies its own collapsible triangulation. -/
theorem Collapsible.hasCollapsibleTriangulation (h : Collapsible K) :
    HasCollapsibleTriangulation.{u} K :=
  ⟨ι, K, PLHomeomorphic.refl K, h⟩

/-- Transport a collapsible triangulation across a PL homeomorphism. -/
theorem HasCollapsibleTriangulation.of_plHomeomorphic
    (hL : HasCollapsibleTriangulation.{v} L) (h : PLHomeomorphic K L) :
    HasCollapsibleTriangulation.{v} K := by
  obtain ⟨ν, A, hLA, hA⟩ := hasCollapsibleTriangulation_iff.mp hL
  exact ⟨ν, A, h.trans hLA, hA⟩

/-- Existence of a collapsible triangulation depends only on the PL polyhedron. -/
theorem PLHomeomorphic.hasCollapsibleTriangulation_iff (h : PLHomeomorphic K L) :
    HasCollapsibleTriangulation.{v} K ↔ HasCollapsibleTriangulation.{v} L :=
  ⟨fun hK => hK.of_plHomeomorphic h.symm, fun hL => hL.of_plHomeomorphic h⟩

/-- A polyhedron admitting a collapsible triangulation is contractible. This does not
assert that its given triangulation is simplicially collapsible. -/
theorem HasCollapsibleTriangulation.contractibleSpace
    (h : HasCollapsibleTriangulation.{v} K) :
    ContractibleSpace
      {x : AbstractSimplicialComplex.Realization (⊤ : AbstractSimplicialComplex ι) //
        x.1.support ∈ K} := by
  obtain ⟨κ, L, hPL, hL⟩ := hasCollapsibleTriangulation_iff.mp h
  obtain ⟨e, _⟩ := plHomeomorphic_iff.mp hPL
  let := hL.contractibleSpace (A := ⊤) le_top
  exact e.contractibleSpace

end PreAbstractSimplicialComplex
