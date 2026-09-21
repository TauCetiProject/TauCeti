/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.RefinementCategory
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

import TauCeti.RingTheory.Huber.OpenIdeal

/-!
# The presentation-indexed limit behind the structure presheaf

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and extends the assignment to an
arbitrary open `V ⊆ Spa(A,A⁺)` by the limit over the rational subsets contained in `V`. This file
constructs that limit **indexed by presentations rather than by rational subsets**, and makes it a
presheaf. It is deliberately not named for `𝒪_X`: see *What this is not, yet* below.

The index is `PresentationIndex`: a presentation together with a proof that the rational subset it
presents lies in `V`, ordered by refinement. `RefinementCategory` already makes the assignment
`p ↦ A⟨p.num / p.den⟩` functorial on presentations, so the diagram is obtained by restricting that
functor along the forgetful map, and the value is its limit — which exists because
`CompleteSeparatedTopCommRingCat` has all small limits.

## Main definitions

* `TauCeti.ValuationSpectrum.PresentationIndex` : the index category for an open — presentations
  whose numerator ideal is open, so that the basic open they present really is a rational subset.
* `TauCeti.ValuationSpectrum.PresentationIndex.commonRefinement` : the common refinement of two
  indices.
* `TauCeti.ValuationSpectrum.presentationIndexDiagram` : the diagram it indexes.
* `TauCeti.ValuationSpectrum.presentationLimit` : the limit itself.
* `TauCeti.ValuationSpectrum.presentationLimitMap` : the restriction morphism of a containment.
* `TauCeti.ValuationSpectrum.presentationLimitPresheaf` : the presheaf they assemble into.

## Main results

* `IsDirected (TauCeti.ValuationSpectrum.PresentationIndex Aplus V) (· ≤ ·)` : the index is
  directed — two admissible presentations refining `V` have an admissible common refinement.
  `Presentation.commonRefinement` leaves both index fields to its consumers, because
  `Presentation` carries no openness field.
* `TauCeti.ValuationSpectrum.presentationLimit_hom_ext` : two morphisms into the limit agree as
  soon as their projections do.
* `TauCeti.ValuationSpectrum.presentationLimitMap_comp_π` : restriction is reindexing —
  restricting and then projecting is projecting at the same presentation.
* `TauCeti.ValuationSpectrum.presentationLimitMap_refl` and
  `TauCeti.ValuationSpectrum.presentationLimitMap_comp` : the two functor laws, as normal forms
  for a restriction map along `le_refl` and for a composite of two restriction maps.

## Why the index is presentations and not subsets

`A⟨T/s⟩` is built from the data `(T, s)`, and two presentations of the *same* rational subset give
canonically isomorphic but not equal rings. Indexing the limit by presentations rather than by
subsets avoids having to choose one.

## What this is not, yet

The presheaf built here is **not identified with Wedhorn's `𝒪_X`**, and is named for what it is
rather than for what it is expected to become. Wedhorn indexes by rational *subsets* `U ⊆ V`, which
presupposes that `𝒪_X(U)` is well defined; here the index is presentations, so the value depends a
priori on presentation data. Two results close the gap:

* refinement maps between two presentations of the *same* rational subset are isomorphisms, so that
  `p ↦ A⟨p.num / p.den⟩` descends to a function of the subset. The isomorphism is supplied by
  `TauCeti.ValuationSpectrum.presentationRingEquivOfEq` when `A⁺` consists of power-bounded
  elements; and
* the presentation index is then cofinal in the subset index, so the two limits agree. This one is
  not yet available.

Nothing in this file computes `𝒪_X(V)`. What it establishes is self-contained: the limit exists,
restriction along a containment is reindexing, and the two functor laws hold. On a rational open
`U` the value is identified with `A_U` in
`TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational`, when `A⁺` consists of
power-bounded elements.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.

## Provenance

The idea of indexing the limit by presentations, and the refinement relation ordering them, were
adapted from AINTLIB (Apache-2.0), commit `37bbdaeb9ad9e3bc9f0d660feadc2779e455a91c`,
`projects/AdicSpaces/Adic spaces/StructurePresheafLimit.lean`. The Lean here is written against this
repository's own `RefinementCategory` and `PairOfDefinition.Presentation` API; no code was copied.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **The index of the limit**: presentations whose numerator ideal is open and whose rational
subset lies in `V`.

The openness of `Ideal.span pres.num` is what makes `R(pres.num / pres.den)` a *rational* subset
in Wedhorn's sense rather than a general basic open — it is the defining condition of
`TauCeti.ValuationSpectrum.spaRationalFamily`. Carrying it as a field of the index restricts the
diagram to admissible presentations; because it is a field, every object supplies its own proof
and the refinement morphisms carry no preservation obligation. -/
structure PresentationIndex {P : PairOfDefinition A} (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) where
  /-- The presentation. -/
  pres : P.Presentation
  /-- Its numerator ideal is open, so the subset it presents is rational. -/
  isOpen_span : IsOpen (Ideal.span (pres.num : Set A) : Set A)
  /-- Its rational subset is contained in `V`. -/
  le_open : spaBasicOpen Aplus pres.num pres.den ≤ V

variable {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-- Refinement of the underlying presentations orders the index. -/
instance : Preorder (PresentationIndex (P := P) Aplus V) :=
  Preorder.lift PresentationIndex.pres

omit [IsTopologicalRing A] in
/-- **An index is its presentation.** The other two fields are propositions, so they are
proof-irrelevant and carry no information: equality of indices reduces to equality of the
underlying presentations. -/
@[ext]
theorem PresentationIndex.ext {i j : PresentationIndex (P := P) Aplus V} (h : i.pres = j.pres) :
    i = j := by
  cases i
  cases j
  subst h
  rfl

omit [IsTopologicalRing A] in
/-- **The common refinement presents the intersection**: `R(p · q) = R(p) ∩ R(q)` for the common
refinement of two presentations. This is `TauCeti.ValuationSpectrum.rationalSubset_inter`, whose
presentation of an intersection the common refinement follows. -/
theorem rationalSubset_commonRefinement (Aplus : Subring A) (p q : P.Presentation) :
    rationalSubset Aplus (p.commonRefinement q).num (p.commonRefinement q).den =
      rationalSubset Aplus p.num p.den ∩ rationalSubset Aplus q.num q.den := by
  classical
  rw [PairOfDefinition.Presentation.commonRefinement_num,
    PairOfDefinition.Presentation.commonRefinement_den, rationalSubset_inter]

omit [IsTopologicalRing A] in
/-- The rational subset of an index of `V` lies in every rational subset containing `V`. -/
theorem PresentationIndex.rationalSubset_subset (i : PresentationIndex (P := P) Aplus V)
    {T : Finset A} {s : A} (hV : V ≤ spaBasicOpen Aplus T s) :
    rationalSubset Aplus i.pres.num i.pres.den ⊆ rationalSubset Aplus T s :=
  spaBasicOpen_le_spaBasicOpen_iff.mp (i.le_open.trans hV)

/-- **The common refinement of two indices**: `Presentation.commonRefinement` of the underlying
presentations, which is again admissible and presents the intersection of the two rational
subsets, so it again lies in `V`.

Both of the index's own fields have to be re-established, which is what
`TauCeti.Huber.PairOfDefinition.Presentation.commonRefinement` deliberately does not do — it
carries no openness field. The containment in `V` is `rationalSubset_commonRefinement`, and
openness of the numerator span is `TauCeti.Huber.PairOfDefinition.isOpen_span_insert_mul_insert`,
the admissibility half of Wedhorn Remark 7.30(5), which
`TauCeti.ValuationSpectrum.inter_mem_spaRationalFamily_of_pairOfDefinition` also uses. -/
noncomputable def PresentationIndex.commonRefinement (i j : PresentationIndex (P := P) Aplus V) :
    PresentationIndex (P := P) Aplus V where
  pres := i.pres.commonRefinement j.pres
  isOpen_span := by
    classical
    rw [PairOfDefinition.Presentation.commonRefinement_num]
    exact P.isOpen_span_insert_mul_insert i.isOpen_span j.isOpen_span
  le_open := le_trans (spaBasicOpen_le_spaBasicOpen_iff.mpr <| by
    rw [rationalSubset_commonRefinement]
    exact Set.inter_subset_left) i.le_open

/-- The presentation of the common refinement of two indices is the common refinement of their
presentations. -/
@[simp]
theorem PresentationIndex.commonRefinement_pres (i j : PresentationIndex (P := P) Aplus V) :
    (i.commonRefinement j).pres = i.pres.commonRefinement j.pres := (rfl)

/-- The common refinement of two indices refines the left one. -/
theorem PresentationIndex.le_commonRefinement_left (i j : PresentationIndex (P := P) Aplus V) :
    i ≤ i.commonRefinement j :=
  i.pres.le_commonRefinement_left j.pres

/-- The common refinement of two indices refines the right one. -/
theorem PresentationIndex.le_commonRefinement_right (i j : PresentationIndex (P := P) Aplus V) :
    j ≤ i.commonRefinement j :=
  i.pres.le_commonRefinement_right j.pres

/-- **The index is directed**: two admissible presentations refining `V` are both refined by
their common refinement `PresentationIndex.commonRefinement`. -/
instance : IsDirected (PresentationIndex (P := P) Aplus V) (· ≤ ·) :=
  ⟨fun i j ↦ ⟨i.commonRefinement j, i.le_commonRefinement_left j,
    i.le_commonRefinement_right j⟩⟩

/-- Forgetting the containment is a functor to the category of all presentations. -/
private def presentationIndexInclusion (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    PresentationIndex (P := P) Aplus V ⥤ P.Presentation where
  obj i := i.pres
  map h := homOfLE h.le

/-- **The diagram the limit is taken over**: each admissible presentation refining `V` contributes
`A⟨T/s⟩`, and a refinement contributes its restriction morphism. -/
noncomputable def presentationIndexDiagram (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    PresentationIndex (P := P) Aplus V ⥤ CompleteSeparatedTopCommRingCat.{v} :=
  presentationIndexInclusion Aplus V ⋙ P.presentationFunctor

private theorem presentationIndexDiagram_obj_eq (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    (presentationIndexDiagram Aplus V).obj i = i.pres.completionLocObj := by
  rw [presentationIndexDiagram]
  exact PairOfDefinition.presentationFunctor_obj P i.pres

/-- The diagram sends an index to the completed localization of its presentation. -/
theorem presentationIndexDiagram_obj (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    (presentationIndexDiagram Aplus V).obj i = i.pres.completionLocObj :=
  presentationIndexDiagram_obj_eq Aplus V i

private theorem presentationIndexDiagram_map_heq (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j) :
    HEq ((presentationIndexDiagram Aplus V).map f)
      (PairOfDefinition.Presentation.restrictionHom f.le) := by
  rw [presentationIndexDiagram]
  exact heq_of_eq (PairOfDefinition.presentationFunctor_map P (homOfLE f.le))

/-- The diagram takes a refinement of indices to the restriction morphism of the underlying
refinement of presentations. -/
@[simp]
theorem presentationIndexDiagram_map (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j) :
    HEq ((presentationIndexDiagram Aplus V).map f)
      (PairOfDefinition.Presentation.restrictionHom f.le) :=
  presentationIndexDiagram_map_heq Aplus V f

/-- Build a cone over the presentation diagram from maps to the completed localization at each
index that commute with restriction morphisms. -/
noncomputable def presentationIndexCone (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (W : CompleteSeparatedTopCommRingCat.{v})
    (app : ∀ i : PresentationIndex (P := P) Aplus V, W ⟶ i.pres.completionLocObj)
    (naturality : ∀ {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j),
      app i ≫ PairOfDefinition.Presentation.restrictionHom f.le = app j) :
    Cone (presentationIndexDiagram (P := P) Aplus V) := by
  rw [presentationIndexDiagram]
  exact
    { pt := W
      π :=
        { app := app
          naturality := fun i j f ↦ by
            -- Unfolding the composite diagram leaves its object and map types definitionally,
            -- but not propositionally, identified with those of `presentationFunctor`.  Its map
            -- lemma is consequently an `HEq`, so it cannot rewrite this dependent naturality
            -- goal; `change` exposes the common restriction-morphism normal form instead.
            change app j = app i ≫ PairOfDefinition.Presentation.restrictionHom f.le
            exact (naturality f).symm } }

private theorem presentationIndexCone_pt_aux (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (W : CompleteSeparatedTopCommRingCat.{v})
    (app : ∀ i : PresentationIndex (P := P) Aplus V, W ⟶ i.pres.completionLocObj)
    (naturality : ∀ {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j),
      app i ≫ PairOfDefinition.Presentation.restrictionHom f.le = app j) :
    (presentationIndexCone Aplus V W app naturality).pt = W := by
  unfold presentationIndexCone presentationIndexDiagram
  rfl

/-- The vertex of a cone built with `presentationIndexCone` is the specified object. -/
theorem presentationIndexCone_pt (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (W : CompleteSeparatedTopCommRingCat.{v})
    (app : ∀ i : PresentationIndex (P := P) Aplus V, W ⟶ i.pres.completionLocObj)
    (naturality : ∀ {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j),
      app i ≫ PairOfDefinition.Presentation.restrictionHom f.le = app j) :
    (presentationIndexCone Aplus V W app naturality).pt = W :=
  presentationIndexCone_pt_aux Aplus V W app naturality

private theorem presentationIndexCone_π_app_aux (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (W : CompleteSeparatedTopCommRingCat.{v})
    (app : ∀ i : PresentationIndex (P := P) Aplus V, W ⟶ i.pres.completionLocObj)
    (naturality : ∀ {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j),
      app i ≫ PairOfDefinition.Presentation.restrictionHom f.le = app j)
    (i : PresentationIndex (P := P) Aplus V) :
    eqToHom (presentationIndexCone_pt Aplus V W app naturality).symm ≫
        (presentationIndexCone Aplus V W app naturality).π.app i ≫
          eqToHom (presentationIndexDiagram_obj Aplus V i) = app i := by
  unfold presentationIndexCone presentationIndexDiagram
  -- The cone-point and diagram-object equations insert `eqToHom` transports around the stored
  -- leg.  After unfolding the wrappers these transports reduce to identities by proof
  -- irrelevance; `change` makes that definitional reduction explicit before reflexivity.
  change app i = app i
  rfl

/-- A cone built with `presentationIndexCone` has the specified leg after transporting the diagram
object to the completed localization of its presentation. -/
@[simp]
theorem presentationIndexCone_π_app (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (W : CompleteSeparatedTopCommRingCat.{v})
    (app : ∀ i : PresentationIndex (P := P) Aplus V, W ⟶ i.pres.completionLocObj)
    (naturality : ∀ {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j),
      app i ≫ PairOfDefinition.Presentation.restrictionHom f.le = app j)
    (i : PresentationIndex (P := P) Aplus V) :
    eqToHom (presentationIndexCone_pt Aplus V W app naturality).symm ≫
        (presentationIndexCone Aplus V W app naturality).π.app i ≫
          eqToHom (presentationIndexDiagram_obj Aplus V i) = app i :=
  presentationIndexCone_π_app_aux Aplus V W app naturality i

/-- **The limit over the presentations refining `V`**, `lim_{R(T/s) ⊆ V} A⟨T/s⟩` — Wedhorn §8.1's
formula for `𝒪_X(V)`, but indexed by presentations rather than by rational subsets. The limit
exists because `CompleteSeparatedTopCommRingCat` has all small limits. This is *not* shown to be
`𝒪_X(V)`; see the module docstring. -/
noncomputable def presentationLimit (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    CompleteSeparatedTopCommRingCat.{v} :=
  limit (presentationIndexDiagram (P := P) Aplus V)

/-- Restricting the containment reindexes the diagram: a presentation refining `W` refines `V`
whenever `W ≤ V`. -/
def presentationIndexRestrict {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    PresentationIndex (P := P) Aplus W ⥤ PresentationIndex (P := P) Aplus V where
  obj i := ⟨i.pres, i.isOpen_span, i.le_open.trans h⟩
  map f := homOfLE f.le

omit [IsTopologicalRing A] in
/-- Restricting an index keeps its presentation. -/
@[simp]
theorem presentationIndexRestrict_obj_pres {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (i : PresentationIndex (P := P) Aplus W) :
    ((presentationIndexRestrict (P := P) h).obj i).pres = i.pres := (rfl)

/-- **The restriction morphism of a containment `W ≤ V`**: the limit over the presentations
refining `V` maps to the limit over the smaller index, by reindexing. -/
noncomputable def presentationLimitMap {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    presentationLimit (P := P) Aplus V ⟶ presentationLimit (P := P) Aplus W :=
  limit.pre (presentationIndexDiagram (P := P) Aplus V) (presentationIndexRestrict (P := P) h)

/-! ### The projection, and the restriction normal forms

`presentationLimit` is a `limit`, so Mathlib's `limit.w`, `limit.lift` and `limit.lift_π` are its
interface and are not restated here. Two names do have to exist. `presentationLimitπ` is
load-bearing rather than cosmetic: `presentationLimitMap`'s codomain is `presentationLimit W`, and
because that definition is sealed the elaborator will not identify it with `limit (diagram W)`, so
`limit.π` cannot be written at the use site — it reports *"definitions were not unfolded because
their definition is not exposed"*. `presentationLimit_hom_ext` follows it: `limit.hom_ext` leaves
goals spelled with `limit.π`, which the restriction lemmas below then fail to rewrite.
-/

/-- **The projection of `presentationLimit` at an index.** -/
noncomputable def presentationLimitπ (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    presentationLimit (P := P) Aplus V ⟶ (presentationIndexDiagram (P := P) Aplus V).obj i :=
  limit.π _ i

/-- The projection at an index, with its codomain transported to the completed localization of
the underlying presentation. -/
noncomputable def presentationLimitπToPresentation (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) (i : PresentationIndex (P := P) Aplus V) :
    presentationLimit (P := P) Aplus V ⟶ i.pres.completionLocObj :=
  presentationLimitπ Aplus V i ≫ eqToHom (presentationIndexDiagram_obj Aplus V i)

/-- **Projections are compatible with refinement**: projecting then restricting along a refinement
is projecting at the finer index. -/
-- These three are not restatements of Mathlib's limit API for their own sake: `presentationLimit`
-- is sealed, so a consumer in another module cannot apply `limit.w`, `limit.lift` or `limit.lift_π`
-- to it at all. They are the only access to the universal property from outside this file.
@[simp]
theorem presentationLimitπ_comp_map {i j : PresentationIndex (P := P) Aplus V} (h : i ⟶ j) :
    presentationLimitπ (P := P) Aplus V i ≫ (presentationIndexDiagram (P := P) Aplus V).map h =
      presentationLimitπ (P := P) Aplus V j :=
  limit.w _ h

private theorem presentationIndexDiagram_obj_comp_restriction
    {i j : PresentationIndex (P := P) Aplus V} (h : i ⟶ j) :
    eqToHom (presentationIndexDiagram_obj (P := P) Aplus V i) ≫
        PairOfDefinition.Presentation.restrictionHom h.le =
      (presentationIndexDiagram (P := P) Aplus V).map h ≫
        eqToHom (presentationIndexDiagram_obj (P := P) Aplus V j) := by
  unfold presentationIndexDiagram
  -- Changing the diagram objects also changes both endpoints of its map, which is why
  -- `presentationIndexDiagram_map` is an `HEq` rather than a rewrite lemma.  Once the composite
  -- functor is unfolded, both transported sides reduce definitionally to the restriction map.
  change PairOfDefinition.Presentation.restrictionHom h.le =
    PairOfDefinition.Presentation.restrictionHom h.le
  rfl

/-- Projecting at a presentation and then restricting is projection at the refined presentation,
after transporting the diagram objects to their completed-localization descriptions. -/
@[simp]
theorem presentationLimitπ_comp_restriction
    {i j : PresentationIndex (P := P) Aplus V} (h : i ≤ j) :
    presentationLimitπToPresentation (P := P) Aplus V i ≫
        PairOfDefinition.Presentation.restrictionHom h =
      presentationLimitπToPresentation (P := P) Aplus V j := by
  unfold presentationLimitπToPresentation
  rw [Category.assoc, presentationIndexDiagram_obj_comp_restriction (homOfLE h), ← Category.assoc,
    presentationLimitπ_comp_map (P := P) (homOfLE h)]

/-- **The universal property**: a cone over the diagram factors through the limit. -/
noncomputable def presentationLimitLift (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (s : Cone (presentationIndexDiagram (P := P) Aplus V)) :
    s.pt ⟶ presentationLimit (P := P) Aplus V :=
  limit.lift _ s

/-- **The lift is a factorisation**: composing it with a projection recovers the cone leg. -/
@[simp]
theorem presentationLimitLift_comp_π (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (s : Cone (presentationIndexDiagram (P := P) Aplus V))
    (i : PresentationIndex (P := P) Aplus V) :
    presentationLimitLift (P := P) Aplus V s ≫ presentationLimitπ (P := P) Aplus V i = s.π.app i :=
  limit.lift_π _ _

/-- The lift followed by the projection transported to the presentation object is the transported
cone leg. -/
@[simp]
theorem presentationLimitLift_comp_πToPresentation (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) (s : Cone (presentationIndexDiagram (P := P) Aplus V))
    (i : PresentationIndex (P := P) Aplus V) :
    presentationLimitLift (P := P) Aplus V s ≫
        presentationLimitπToPresentation (P := P) Aplus V i =
      s.π.app i ≫ eqToHom (presentationIndexDiagram_obj Aplus V i) := by
  unfold presentationLimitπToPresentation
  rw [← Category.assoc, presentationLimitLift_comp_π]

/-- The lift of a cone built from presentationwise maps has those maps as its transported
projections. -/
theorem presentationIndexCone_lift_comp_πToPresentation (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) (W : CompleteSeparatedTopCommRingCat.{v})
    (app : ∀ i : PresentationIndex (P := P) Aplus V, W ⟶ i.pres.completionLocObj)
    (naturality : ∀ {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j),
      app i ≫ PairOfDefinition.Presentation.restrictionHom f.le = app j)
    (i : PresentationIndex (P := P) Aplus V) :
    eqToHom (presentationIndexCone_pt Aplus V W app naturality).symm ≫
        presentationLimitLift Aplus V (presentationIndexCone Aplus V W app naturality) ≫
          presentationLimitπToPresentation Aplus V i = app i := by
  rw [presentationLimitLift_comp_πToPresentation, presentationIndexCone_π_app]

/-- **Extensionality**: maps into the limit agree when their projections do. -/
-- Tagged `@[ext]` because `presentationLimit` is sealed, so `ext` cannot reach `limit.hom_ext`
-- through it from another module.
@[ext]
theorem presentationLimit_hom_ext {W : CompleteSeparatedTopCommRingCat.{v}}
    {f g : W ⟶ presentationLimit (P := P) Aplus V}
    (h : ∀ i, f ≫ presentationLimitπ (P := P) Aplus V i =
      g ≫ presentationLimitπ (P := P) Aplus V i) : f = g :=
  limit.hom_ext h

/-- Extensionality using the projections transported to their presentation objects. -/
theorem presentationLimit_hom_ext_toPresentation {W : CompleteSeparatedTopCommRingCat.{v}}
    {f g : W ⟶ presentationLimit (P := P) Aplus V}
    (h : ∀ i, f ≫ presentationLimitπToPresentation (P := P) Aplus V i =
      g ≫ presentationLimitπToPresentation (P := P) Aplus V i) : f = g := by
  apply presentationLimit_hom_ext
  intro i
  apply (cancel_mono (eqToHom (presentationIndexDiagram_obj Aplus V i))).mp
  simpa only [presentationLimitπToPresentation, Category.assoc] using h i

/-- **Restricting an index does not change what the diagram sends it to.** -/
-- This is the object half of the reindexing characterisation, and what lets the index functors
-- stay sealed: the two objects are definitionally equal, and naming that equality here means no
-- consumer has to see a body to use it.
theorem presentationIndexDiagram_obj_restrict {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (i : PresentationIndex (P := P) Aplus W) :
    (presentationIndexDiagram (P := P) Aplus V).obj ((presentationIndexRestrict (P := P) h).obj i) =
      (presentationIndexDiagram (P := P) Aplus W).obj i := (rfl)

/-- **Restriction is reindexing**: restricting to `W` and then projecting at an index of `W` is
projecting at the same presentation viewed as an index of `V`, transported along
`presentationIndexDiagram_obj_restrict`. -/
-- The transport is the price of keeping the index functors sealed; it is `eqToHom` of a
-- `rfl`-equality, so `simp` discharges it at every use site.
@[simp]
theorem presentationLimitMap_comp_π {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (i : PresentationIndex (P := P) Aplus W) :
    presentationLimitMap (P := P) h ≫ presentationLimitπ (P := P) Aplus W i =
      presentationLimitπ (P := P) Aplus V ((presentationIndexRestrict (P := P) h).obj i) ≫
        eqToHom (presentationIndexDiagram_obj_restrict (P := P) h i) :=
  limit.pre_π _ _ _

/-- Restriction followed by a projection transported to its presentation object is the
corresponding transported projection before restriction. -/
@[simp]
theorem presentationLimitMap_comp_πToPresentation {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (i : PresentationIndex (P := P) Aplus W) :
    presentationLimitMap (P := P) h ≫
        presentationLimitπToPresentation (P := P) Aplus W i =
      presentationLimitπToPresentation (P := P) Aplus V
          ((presentationIndexRestrict (P := P) h).obj i) ≫
        eqToHom (congrArg PairOfDefinition.Presentation.completionLocObj
          (presentationIndexRestrict_obj_pres h i)) := by
  unfold presentationLimitπToPresentation
  rw [← Category.assoc, presentationLimitMap_comp_π]
  simp only [Category.assoc, eqToHom_trans]

/-- **Restricting along `le_refl` is the identity.** -/
@[simp]
theorem presentationLimitMap_refl (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    presentationLimitMap (P := P) (le_refl V) = 𝟙 (presentationLimit (P := P) Aplus V) := by
  apply limit.hom_ext
  intro j
  -- `presentationIndexRestrict (le_refl V)` is only definitionally the identity functor, so
  -- `limit.pre_π`'s index does not match syntactically and `rw` reports no occurrence.
  erw [limit.pre_π, Category.id_comp]
  rfl

/-- **Successive restrictions compose** to the restriction along the transitive containment. -/
@[simp]
theorem presentationLimitMap_comp {U V W : Opens ↥(spa Aplus)} (h₁ : W ≤ V) (h₂ : U ≤ W) :
    presentationLimitMap (P := P) h₁ ≫ presentationLimitMap (P := P) h₂ =
      presentationLimitMap (P := P) (h₂.trans h₁) := by
  refine presentationLimit_hom_ext (P := P) fun j => ?_
  -- The last step needs `erw`: the two sides land in `(diagram W).obj i` and
  -- `(diagram V).obj ((restrict h₁).obj i)`, which are definitionally but not syntactically equal.
  simp only [Category.assoc, presentationLimitMap_comp_π]
  erw [presentationLimitMap_comp_π]
  rfl

/-- **The presheaf `V ↦ presentationLimit V`** on `Spa(A,A⁺)`, valued in
`CompleteSeparatedTopCommRingCat`. Both functor laws are reindexing identities for the limit:
restricting along `le_refl` is the identity on the index, and restricting twice is restricting
once. Wedhorn §8.1's `𝒪_X` is this presheaf only once presentation-independence is available. -/
-- This definition is sealed, as are the three index functors above. Two consequences worth
-- naming, because they are what the evaluation lemmas below look like: `_obj` closes with
-- `(rfl)` rather than `rfl`, the parentheses letting the elaborator postpone a defeq check the
-- sealed body would otherwise refuse; and `_map` cannot be stated bare at all, since its sides
-- live in `(presheaf).obj V ⟶ (presheaf).obj W` and `presentationLimit V.unop ⟶
-- presentationLimit W.unop`, equal only definitionally. It carries `eqToHom` transports built
-- from `_obj`. Both transports are `eqToHom` of `rfl`-equalities, so `simp` removes them at the
-- use site and no consumer sees a body.
noncomputable def presentationLimitPresheaf (P : PairOfDefinition A) (Aplus : Subring A) :
    (Opens ↥(spa Aplus))ᵒᵖ ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj V := presentationLimit (P := P) Aplus V.unop
  map h := presentationLimitMap (P := P) (leOfHom h.unop)
  map_id V := presentationLimitMap_refl (P := P) Aplus V.unop
  map_comp f g := (presentationLimitMap_comp (P := P) (leOfHom f.unop) (leOfHom g.unop)).symm


/-- Evaluating the presheaf on an open is the limit over that open. -/
@[simp]
theorem presentationLimitPresheaf_obj (P : PairOfDefinition A) (Aplus : Subring A)
    (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheaf P Aplus).obj V = presentationLimit (P := P) Aplus V.unop :=
  (rfl)

/-- The presheaf's action on a containment is the reindexing map. -/
@[simp]
theorem presentationLimitPresheaf_map (P : PairOfDefinition A) (Aplus : Subring A)
    {V W : (Opens ↥(spa Aplus))ᵒᵖ} (h : V ⟶ W) :
    (presentationLimitPresheaf P Aplus).map h =
      eqToHom (presentationLimitPresheaf_obj P Aplus V) ≫
        presentationLimitMap (P := P) (leOfHom h.unop) ≫
          eqToHom (presentationLimitPresheaf_obj P Aplus W).symm :=
  (rfl)

end

end TauCeti.ValuationSpectrum
