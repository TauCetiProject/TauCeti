/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.RefinementCategory
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

/-!
# The structure presheaf of an adic spectrum

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and extends the assignment to an
arbitrary open `V ⊆ Spa(A,A⁺)` by the limit over the rational subsets contained in `V`. This file
constructs that limit.

The index is `RationalIndex`: a presentation together with a proof that the rational subset it
presents lies in `V`, ordered by refinement. `RefinementCategory` already makes the assignment
`p ↦ A⟨p.num / p.den⟩` functorial on presentations, so the diagram is obtained by restricting that
functor along the forgetful map, and the value is its limit — which exists because
`CompleteSeparatedTopCommRingCat` has all small limits.

## Main definitions

* `TauCeti.ValuationSpectrum.spaOpens` : the rational subset of a presentation, as an open.
* `TauCeti.ValuationSpectrum.RationalIndex` : the index category for an open.
* `TauCeti.ValuationSpectrum.rationalIndexDiagram` : the diagram it indexes.
* `TauCeti.ValuationSpectrum.structurePresheafObj` : the value `𝒪_X(V)`.
* `TauCeti.ValuationSpectrum.structurePresheafMap` : the restriction morphism of a containment.
* `TauCeti.ValuationSpectrum.structurePresheaf` : the presheaf itself.

## Why the index is presentations and not subsets

`A⟨T/s⟩` is built from the data `(T, s)`, and two presentations of the *same* rational subset give
canonically isomorphic but not equal rings. Indexing the limit by presentations rather than by
subsets avoids having to choose one, and costs nothing: refinement is cofinal among presentations of
a given subset, so the limit is unchanged.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The rational subset a presentation presents, as an open of `Spa(A,A⁺)`. -/
def spaOpens {P : PairOfDefinition A} (Aplus : Subring A) (p : P.Presentation) :
    Opens ↥(spa Aplus) :=
  ⟨Subtype.val ⁻¹' rationalSubset Aplus p.num p.den,
    isOpen_val_preimage_rationalSubset Aplus p.num p.den⟩

/-- **The index of the limit defining `𝒪_X(V)`**: presentations whose rational subset lies in
`V`. -/
structure RationalIndex {P : PairOfDefinition A} (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) where
  /-- The presentation. -/
  pres : P.Presentation
  /-- Its rational subset is contained in `V`. -/
  le_open : spaOpens Aplus pres ≤ V

variable {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- Refinement of the underlying presentations orders the index. -/
instance : Preorder (RationalIndex (P := P) Aplus V) :=
  Preorder.lift RationalIndex.pres

/-- Forgetting the containment is a functor to the category of all presentations. -/
def rationalIndexInclusion (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    RationalIndex (P := P) Aplus V ⥤ P.Presentation where
  obj i := i.pres
  map h := homOfLE h.le

/-- **The diagram `𝒪_X(V)` is the limit of**: each presentation refining `V` contributes
`A⟨T/s⟩`, and a refinement contributes its restriction morphism. -/
noncomputable def rationalIndexDiagram (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    RationalIndex (P := P) Aplus V ⥤ CompleteSeparatedTopCommRingCat.{v} :=
  rationalIndexInclusion Aplus V ⋙ P.presentationFunctor

/-- **The value of the structure presheaf on an open**, `𝒪_X(V) = lim_{R(T/s) ⊆ V} A⟨T/s⟩`
(Wedhorn §8.1). The limit exists because `CompleteSeparatedTopCommRingCat` has all small
limits. -/
noncomputable def structurePresheafObj (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    CompleteSeparatedTopCommRingCat.{v} :=
  limit (rationalIndexDiagram (P := P) Aplus V)

/-- Restricting the containment reindexes the diagram: a presentation refining `W` refines `V`
whenever `W ≤ V`. -/
def rationalIndexRestrict {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    RationalIndex (P := P) Aplus W ⥤ RationalIndex (P := P) Aplus V where
  obj i := ⟨i.pres, i.le_open.trans h⟩
  map f := homOfLE f.le

/-- **The restriction morphism `𝒪_X(V) ⟶ 𝒪_X(W)` of a containment `W ≤ V`**: the limit over the
presentations refining `V` maps to the limit over the smaller index, by reindexing. -/
noncomputable def structurePresheafMap {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    structurePresheafObj (P := P) Aplus V ⟶ structurePresheafObj (P := P) Aplus W :=
  limit.pre (rationalIndexDiagram (P := P) Aplus V) (rationalIndexRestrict (P := P) h)

/-- **The structure presheaf** `V ↦ 𝒪_X(V)` on `Spa(A,A⁺)`, valued in
`CompleteSeparatedTopCommRingCat` (Wedhorn §8.1). Both functor laws are reindexing identities for
the limit: restricting along `le_refl` is the identity on the index, and restricting twice is
restricting once. -/
noncomputable def structurePresheaf (P : PairOfDefinition A) (Aplus : Subring A) :
    (Opens ↥(spa Aplus))ᵒᵖ ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj V := structurePresheafObj (P := P) Aplus V.unop
  map h := structurePresheafMap (P := P) (leOfHom h.unop)
  map_id V := by
    apply limit.hom_ext
    intro j
    erw [limit.pre_π, Category.id_comp]
    rfl
  map_comp {X Y Z} f g := by
    simp only [structurePresheafMap]
    exact (limit.pre_pre (rationalIndexDiagram (P := P) Aplus X.unop)
      (rationalIndexRestrict (P := P) (leOfHom f.unop))
      (rationalIndexRestrict (P := P) (leOfHom g.unop))).symm

end

end TauCeti.ValuationSpectrum
