/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Relabel.PL
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Sequence
public import TauCeti.AlgebraicTopology.SimplicialComplex.Collapse.Map

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
in universe `v`. The witnessing complex need not be the given triangulation `K`.
The universe is immaterial by `HasCollapsibleTriangulation.universe_iff`. -/
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

/-- A collapsible triangulation can be represented in any vertex universe, since its
finitely many faces use only finitely many vertices. -/
theorem HasCollapsibleTriangulation.changeUniverse (h : HasCollapsibleTriangulation.{v} K) :
    HasCollapsibleTriangulation.{w} K := by
  classical
  obtain ⟨ν, A, hKA, hA⟩ := hasCollapsibleTriangulation_iff.mp h
  let V := hA.finite_faces.toFinset.biUnion id
  have hV : ∀ σ ∈ A, σ ⊆ V := by
    intro σ hσ v hv
    exact Finset.mem_biUnion.mpr ⟨σ, hA.finite_faces.mem_toFinset.mpr hσ, hv⟩
  let B : PreAbstractSimplicialComplex V :=
    { faces := {σ | σ.image Subtype.val ∈ A}
      isRelLowerSet_faces := fun {_} hσ =>
        ⟨Finset.image_nonempty.mp (A.isRelLowerSet_faces hσ).1,
          fun _ hτσ hτ => (A.isRelLowerSet_faces hσ).2
            (Finset.image_mono _ hτσ) (hτ.image _)⟩ }
  let i : V ↪ ν := Function.Embedding.subtype (· ∈ V)
  have hBA : B.map i = A := by
    apply SetLike.ext
    intro σ
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact hτ
    · intro hσ
      have heq : (σ.subtype (· ∈ V)).image Subtype.val = σ := by
        simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
          Finset.subtype_map_of_mem (hV σ hσ)
      have hτ : (σ.subtype (· ∈ V)).image Subtype.val ∈ A := heq.symm ▸ hσ
      exact mem_map_iff.mpr ⟨σ.subtype (· ∈ V), hτ, heq⟩
  have hB : Collapsible B :=
    (Collapsible.map_iff_of_injective i i.injective).mp (hBA.symm ▸ hA)
  let e : V ↪ ULift.{w} (Fin V.card) :=
    (Finset.equivFin V).toEmbedding.trans (Equiv.ulift.symm.toEmbedding)
  have hAB : PLHomeomorphic A B :=
    hBA ▸ (PLHomeomorphic.relabeling B i).symm
  exact ⟨ULift (Fin V.card), B.map e,
    hKA.trans (hAB.trans (PLHomeomorphic.relabeling B e)), hB.map e e.injective⟩

/-- The witness vertex universe does not affect existence of a collapsible triangulation. -/
theorem HasCollapsibleTriangulation.universe_iff :
    HasCollapsibleTriangulation.{v} K ↔ HasCollapsibleTriangulation.{w} K :=
  ⟨fun h => h.changeUniverse, fun h => h.changeUniverse⟩

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
  let := hL.contractibleSpace (A := ⊤) _root_.le_top
  exact e.contractibleSpace

end PreAbstractSimplicialComplex
