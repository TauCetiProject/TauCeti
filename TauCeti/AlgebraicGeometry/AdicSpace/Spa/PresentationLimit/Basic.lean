/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basis
public import TauCeti.RingTheory.Huber.LocalizationTopology.CompleteSeparated.RefinementCategory
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Limits

/-!
# The presentation-indexed limit of completed rational localizations

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and extends the assignment to an
arbitrary open `V ⊆ Spa(A,A⁺)` by a limit of completed rational localizations. This file builds
the limit **indexed by presentations** rather than by rational subsets. Identifying it with
Wedhorn's `𝒪_X` is an initiality statement about the indexing functor which is *not* proved
here, so the declarations are named for the construction rather than for the target — see
"Why the index is presentations and not subsets" below.

The presheaf is Mathlib's **pointwise right Kan extension** of `rationalDiagram` along
`rationalInclusion`. `CompleteSeparated/RefinementCategory.lean` already makes the assignment
`p ↦ A⟨p.num / p.den⟩` functorial on presentations; `rationalDiagram` restricts that functor to
the presentations with open numerator ideal — the rational-basis condition — and
`rationalInclusion` records which open each of them presents, contravariantly, since refinement
shrinks the rational subset.

Unfolded, the extension's value on `V` is the limit of `A⟨T/s⟩` over the rational presentations
whose open is contained in `V` — a limit that exists because `CompleteSeparatedTopCommRingCat` has
all small limits — and its action on a containment is the reindexing of that limit. The index of
that limit is `StructuredArrow (op V) rationalInclusion`, abbreviated `RationalIndex`: nothing
about it is built here, so Mathlib's limit, `StructuredArrow` and Kan extension APIs all apply
directly.

Everything here is stated for an arbitrary `Subring` of a topological ring carrying a pair of
definition. Wedhorn's standing hypotheses — a Huber ring, a ring of integral elements — are
likewise not imposed; the sibling `spa` and `rationalSubset` carry the same convention. Adding
them would not turn this into `𝒪_X`: what is missing is the initiality of the indexing functor,
not the hypotheses.

## Main definitions

* `TauCeti.ValuationSpectrum.isRational` : presenting a member of the rational basis.
* `TauCeti.ValuationSpectrum.rationalInclusion` : the open each of them presents.
* `TauCeti.ValuationSpectrum.rationalDiagram` : the diagram they index.
* `TauCeti.ValuationSpectrum.RationalIndex` : the index at an open, a `StructuredArrow`.
* `TauCeti.ValuationSpectrum.presentationLimitPresheaf` : the presheaf, the Kan extension.
* `TauCeti.ValuationSpectrum.presentationLimitObj` : its value, the candidate for `𝒪_X(V)`.
* `TauCeti.ValuationSpectrum.presentationLimitCone` : the cone that value is a limit of, with
  `presentationLimitIsLimit` its universal property — the two together are the whole interface,
  used through Mathlib's `IsLimit` API rather than through local wrappers.
* `TauCeti.ValuationSpectrum.presentationLimitMap` : the restriction morphism of a containment.
* `TauCeti.Huber.PairOfDefinition.HasSheafyPresentationLimit` : the presentation-indexed
  presheaf is a sheaf. It is named for the presheaf it actually tests: until the initiality
  statement is proved, that presheaf is not known to be Wedhorn's `𝒪_X`, so this is not yet the
  roadmap's `Huber.IsSheafyPair` (`AdicSpaces/README.md:522`) — which the rename leaves free.

## Main results

* `TauCeti.Huber.PairOfDefinition.hasSheafyPresentationLimit_iff` : sheafiness unfolds to
  Mathlib's sheaf
  condition (`HasSheafyPresentationLimit` is not exposed; this is the route across).
* `presentationLimitPresheaf_obj`, `presentationLimitPresheaf_map` : its simp interface.
* `presentationLimitMap_π` : the characteristic equation of the restriction morphism, and
  `presentationLimitMap_refl` / `presentationLimitMap_comp` : its identity and composition laws,
  which are the presheaf's functor laws.
* `presentationLimitπ_map` and `presentationLimitπ_restrictionHom` : the cone equation, stated
  both as `Cone.w` and at the shape `simp` leaves a goal in.
* The `IsFilteredOrEmpty` instance on `RationalIndex` : two indices have a common refinement, so
  presentations of the same subset are constrained through one.

The interface is the universal property, and it is Mathlib's: `presentationLimitCone` is the
cone and `presentationLimitIsLimit` its limit proof. Everything the universal property gives —
`.lift` and its `.fac`, `.hom_ext`, `IsLimit.conePointUniqueUpToIso`, cofinality — is reached
through that `IsLimit` directly rather than through wrappers named here; only
`presentationLimitπ`, which the restriction equations below are stated with, has a local name.
This is why the definitions are exposed rather than sealed.

Reindexing needs no lemmas of its own. `presentationLimitMap` is the presheaf's own action, so
`_refl` and `_comp` are its functor laws and `_π` is `limit.lift_π`; the inclusion of one index
into another is `StructuredArrow.map`, whose functoriality is Mathlib's.

## Why the index is presentations and not subsets

`A⟨T/s⟩` is built from the data `(T, s)`, and two presentations of the *same* rational subset
give canonically isomorphic but not equal rings. Indexing the limit by presentations avoids
having to choose one. Any two indices map onwards to a common refinement — this is the
`IsFilteredOrEmpty` instance, via the product presentation — so presentations of the same subset
are constrained through one. That is weaker than identifying their components,
which would need the unproved initiality.

**The comparison with Wedhorn's limit over rational *subsets* is not proved here.** It is an
initiality (cofinality) statement about the forgetful functor from presentations to rational
opens: expected, but not formalized, and nothing in this file depends on it. Because it is
unproved, nothing here is named `structurePresheaf` or claimed to *be* `𝒪_X` — the declarations
say `presentationLimit`, and so does the directory holding them. The identification, once proved,
should be a theorem relating the two limits rather than a renaming of this one, and
`Spa/StructurePresheaf/` is left free for the file that proves it.

## Provenance

Adapted from AINTLIB's `StructurePresheafLimit.lean` (see References), including the name
`RationalIndex`. The model deliberately diverges: the source hand-builds the limit as a subring
`limitSections V` of a product carrying the subspace topology and proves closedness,
completeness, separatedness and functoriality one by one, while here the value is the
categorical `limit` in `CompleteSeparatedTopCommRingCat`, so all of that is supplied by the
category (#3735, #3736). The source's object is not an object of a category and so cannot be
handed to `CategoryTheory.Presheaf.IsSheaf`, which is what the sheafiness definition below
needs. Its `IsSheafy` is a typeclass on the ring; the `P`-relative Prop here is distinct.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/StructurePresheafLimit.lean`.
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits Opposite _root_.TopologicalSpace TauCeti.Huber

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in
/-- **A presentation is rational when it presents a member of the rational basis**: when its
numerator ideal is open.

The openness condition is necessary but not evidently sufficient: `Presentation` also carries
`hasDenominatorPower`, which this repository nowhere derives from `IsOpen (Ideal.span num)`. So
these may present a proper subfamily of the rational opens contained in a given open, and showing
they cover all of them is part of the outstanding comparison, not something recorded here. -/
def isRational (P : PairOfDefinition A) : ObjectProperty P.Presentation :=
  fun p ↦ IsOpen (Ideal.span (p.num : Set A) : Set A)

variable {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

variable (P) in
/-- **Each rational presentation names the rational open it presents.** Refinement of
presentations shrinks the rational subset — this is `spaRationalOpen_le_of_cofactor` — so the
assignment is contravariant, and the codomain is taken in `(Opens _)ᵒᵖ` to record that.

`@[expose]`, like `presentationFunctor`: `rationalDiagram` below composes with this functor, and
the equations identifying the composite's values are unstatable unless it unfolds
definitionally — their two sides otherwise live in different hom-types. -/
@[expose]
def rationalInclusion (Aplus : Subring A) :
    (isRational P).FullSubcategory ⥤ (Opens ↥(spa Aplus))ᵒᵖ where
  obj p := op (spaRationalOpen Aplus p.obj.num p.obj.den)
  map {p q} h := (homOfLE (show spaRationalOpen Aplus q.obj.num q.obj.den ≤
      spaRationalOpen Aplus p.obj.num p.obj.den by
    obtain ⟨r, hr, hT⟩ :=
      PairOfDefinition.Presentation.le_def.mp (leOfHom ((isRational P).ι.map h))
    exact spaRationalOpen_le_of_cofactor Aplus hr hT)).op
  map_id _ := rfl
  map_comp _ _ := rfl

variable (P) in
/-- **The diagram the limit is taken over**: each rational presentation contributes its completed
rational localization `A⟨T/s⟩`, and a refinement contributes its restriction morphism. -/
@[expose]
noncomputable def rationalDiagram :
    (isRational P).FullSubcategory ⥤ CompleteSeparatedTopCommRingCat.{v} :=
  (isRational P).ι ⋙ P.presentationFunctor

/-- The diagram's value at a rational presentation is its completed rational localization. -/
@[simp]
theorem rationalDiagram_obj (p : (isRational P).FullSubcategory) :
    (rationalDiagram P).obj p = p.obj.completionLocObj := (rfl)

/-- The diagram's value at a refinement is its restriction morphism. -/
@[simp]
theorem rationalDiagram_map {p q : (isRational P).FullSubcategory} (h : p ⟶ q) :
    (rationalDiagram P).map h =
      PairOfDefinition.Presentation.restrictionHom (leOfHom ((isRational P).ι.map h)) := (rfl)

variable (P) in
/-- **The index of the limit at an open `V`**: a rational presentation together with a proof that
the rational subset it presents is contained in `V`, a refinement of presentations being a
morphism.

This is literally Mathlib's `StructuredArrow`, so its whole API applies unchanged — the
abbreviation names the role the category plays here rather than introducing a new one. An object
is `StructuredArrow.mk` of the containment, and `i.right.obj` is the underlying presentation. -/
abbrev RationalIndex (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :=
  StructuredArrow (op V) (rationalInclusion P Aplus)

/-- **The index is filtered**: the common refinement of two indices is again an index — its
numerator span is open by `isOpen_span_insert_mul_insert` (this is what the insert-augmented
numerators of `Presentation.commonRefinement` are for), and its rational open is the intersection
of the factors' (`spaRationalOpen_inf`), hence contained in `V` through either factor.
Presentations of the same rational subset are therefore constrained through a common
refinement — weaker than identifying their components, which needs the unproved initiality.

Filtered *or empty*: nothing here provides an index for an arbitrary `V`, and a `V` containing no
rational open has none. This is the form the eventual cofinality argument needs; it is not what
makes the limit exist, since `CompleteSeparatedTopCommRingCat` has all small limits
(`Topology/Category/TopCommRingCat/CompleteSeparated/Limits.lean`). -/
instance : IsFilteredOrEmpty (RationalIndex P Aplus V) where
  cocone_objs i j := by
    classical
    have hopen : isRational P (i.right.obj.commonRefinement j.right.obj) := by
      change IsOpen (Ideal.span
        ((i.right.obj.commonRefinement j.right.obj).num : Set A) : Set A)
      rw [PairOfDefinition.Presentation.commonRefinement_num]
      exact isOpen_span_insert_mul_insert P i.right.property j.right.property
    have hle : spaRationalOpen Aplus (i.right.obj.commonRefinement j.right.obj).num
        (i.right.obj.commonRefinement j.right.obj).den ≤ V := by
      rw [PairOfDefinition.Presentation.commonRefinement_num,
        PairOfDefinition.Presentation.commonRefinement_den, ← spaRationalOpen_inf]
      exact inf_le_left.trans (leOfHom i.hom.unop)
    exact ⟨StructuredArrow.mk (Y := (⟨i.right.obj.commonRefinement j.right.obj, hopen⟩ :
        (isRational P).FullSubcategory)) (homOfLE hle).op,
      StructuredArrow.homMk (ObjectProperty.homMk
        (homOfLE (i.right.obj.le_commonRefinement_left j.right.obj))) (Subsingleton.elim _ _),
      StructuredArrow.homMk (ObjectProperty.homMk
        (homOfLE (i.right.obj.le_commonRefinement_right j.right.obj))) (Subsingleton.elim _ _),
      trivial⟩
  cocone_maps _ _ f g := ⟨_, 𝟙 _, by
    rw [StructuredArrow.hom_ext f g (ObjectProperty.hom_ext _ (Subsingleton.elim _ _))]⟩

variable (P) in
/-- **The presentation-indexed presheaf** on the adic spectrum of `Aplus`, valued in
`CompleteSeparatedTopCommRingCat`: Mathlib's pointwise right Kan extension of `rationalDiagram`
along `rationalInclusion`.

Unfolded, its value on `V` is the limit of `A⟨T/s⟩` over the rational presentations whose open is
contained in `V`, and its action on a containment is the reindexing of that limit — the two
descriptions agree definitionally, `StructuredArrow.map` being the reindexing. Taking the
Kan extension as the definition is what makes Mathlib's limit and extension API apply
directly:
`presentationLimitIsLimit` below is Mathlib's, not a reconstruction.

This is the candidate for Wedhorn's `𝒪_X` (§8.1). It is not identified with it here: that needs
the initiality of the forgetful functor to rational opens, which is not proved — see the module
docstring. -/
@[expose]
noncomputable def presentationLimitPresheaf (Aplus : Subring A) :
    (Opens ↥(spa Aplus))ᵒᵖ ⥤ CompleteSeparatedTopCommRingCat.{v} :=
  (rationalInclusion P Aplus).pointwiseRightKanExtension (rationalDiagram P)

variable (P) in
/-- **The value of the presentation-indexed presheaf on an open.** -/
@[expose]
noncomputable def presentationLimitObj (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    CompleteSeparatedTopCommRingCat.{v} :=
  (presentationLimitPresheaf P Aplus).obj (op V)

variable (P) in
/-- **The cone the value is a limit of**: its point is `presentationLimitObj` and its legs are the
projections to the completed rational localizations. This is Mathlib's `RightExtension.coneAt`,
so `presentationLimitIsLimit` and the whole `IsLimit` API are available on it. -/
noncomputable def presentationLimitCone (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    Cone (StructuredArrow.proj (op V) (rationalInclusion P Aplus) ⋙ rationalDiagram P) :=
  limit.cone (StructuredArrow.proj (op V) (rationalInclusion P Aplus) ⋙ rationalDiagram P)

variable (P) in
/-- **The cone is a limit cone**: this is what "pointwise" means for the Kan extension. It is the
whole universal property of `presentationLimitObj`, and consumers use its `.lift`, `.fac` and
`.hom_ext` directly. -/
noncomputable def presentationLimitIsLimit (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    IsLimit (presentationLimitCone P Aplus V) :=
  limit.isLimit (StructuredArrow.proj (op V) (rationalInclusion P Aplus) ⋙ rationalDiagram P)

variable (P) in
/-- **The projection of the presentation-indexed limit at one index**: the leg of
`presentationLimitCone` there. -/
noncomputable def presentationLimitπ (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : RationalIndex P Aplus V) :
    presentationLimitObj P Aplus V ⟶ (rationalDiagram P).obj i.right :=
  (presentationLimitCone P Aplus V).π.app i

variable (P) in
/-- **The projections are compatible with refinement**: this is `Cone.w` for
`presentationLimitCone`, stated through `presentationLimitπ`.

Deliberately **not** `@[simp]`: `rationalDiagram_map` (itself `@[simp]`) rewrites this left-hand
side into `restrictionHom` form, so it is not in simp-normal form.
`presentationLimitπ_restrictionHom` below is the restatement *at* that normal form. -/
theorem presentationLimitπ_map {i j : RationalIndex P Aplus V} (f : i ⟶ j) :
    presentationLimitπ P Aplus V i ≫ (rationalDiagram P).map f.right =
      presentationLimitπ P Aplus V j :=
  (presentationLimitCone P Aplus V).w f

variable (P) in
/-- **The projections are compatible with refinement, at the simp-normal shape.** This is
`presentationLimitπ_map` after `rationalDiagram_map`; a goal that has met `simp` is in this form
and has no other lemma to apply. Not `@[simp]` itself: `restrictionHom` takes the containment as
a proof argument, so simp has no matchable key on the right-hand side. -/
theorem presentationLimitπ_restrictionHom {i j : RationalIndex P Aplus V} (f : i ⟶ j) :
    presentationLimitπ P Aplus V i ≫ PairOfDefinition.Presentation.restrictionHom
        (leOfHom ((isRational P).ι.map f.right)) =
      presentationLimitπ P Aplus V j :=
  presentationLimitπ_map P f

variable (P) in
/-- **The restriction morphism of a containment `W ≤ V`**: the presheaf's action, which unfolds to
the reindexing of the limit along `StructuredArrow.map`. -/
@[expose]
noncomputable def presentationLimitMap {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    presentationLimitObj P Aplus V ⟶ presentationLimitObj P Aplus W :=
  (presentationLimitPresheaf P Aplus).map (homOfLE h).op

variable (P) in
/-- **The characteristic equation of `presentationLimitMap`**: composing with a projection of the
smaller limit is the projection of the larger one at the included index, `StructuredArrow.map`
being the inclusion. -/
@[simp]
theorem presentationLimitMap_π {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (j : RationalIndex P Aplus W) :
    presentationLimitMap P h ≫ presentationLimitπ P Aplus W j =
      presentationLimitπ P Aplus V ((StructuredArrow.map (homOfLE h).op).obj j) :=
  limit.lift_π _ j

variable (P) in
/-- Restricting along `le_refl` is the identity: the presheaf's identity law. -/
@[simp]
theorem presentationLimitMap_refl (V : Opens ↥(spa Aplus)) :
    presentationLimitMap P (le_refl V) = 𝟙 (presentationLimitObj P Aplus V) :=
  (presentationLimitPresheaf P Aplus).map_id (op V)

variable (P) in
/-- Restricting twice is restricting once: the presheaf's composition law. -/
@[reassoc (attr := simp)]
theorem presentationLimitMap_comp {V W X : Opens ↥(spa Aplus)} (h₁ : X ≤ W) (h₂ : W ≤ V) :
    presentationLimitMap P h₂ ≫ presentationLimitMap P h₁ =
      presentationLimitMap P (h₁.trans h₂) :=
  ((presentationLimitPresheaf P Aplus).map_comp (homOfLE h₂).op (homOfLE h₁).op).symm

/-- The presheaf's value on an open is `presentationLimitObj`. -/
@[simp]
theorem presentationLimitPresheaf_obj (P : PairOfDefinition A) (Aplus : Subring A)
    (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheaf P Aplus).obj V = presentationLimitObj P Aplus V.unop := (rfl)

/-- The presheaf's action on a containment is `presentationLimitMap`. -/
@[simp]
theorem presentationLimitPresheaf_map (P : PairOfDefinition A) (Aplus : Subring A)
    {V W : (Opens ↥(spa Aplus))ᵒᵖ} (h : V ⟶ W) :
    (presentationLimitPresheaf P Aplus).map h = presentationLimitMap P (leOfHom h.unop) := (rfl)

/-- **The presentation-indexed presheaf of `P` over `Aplus` is a sheaf**: that presheaf
built from
`P`'s presentations is a sheaf, in the sense of Mathlib's `CategoryTheory.Presheaf.IsSheaf` for
the Grothendieck topology of the adic spectrum of `Aplus`.

The definition is deliberately Mathlib's and not Wedhorn's equalizer condition or a Čech
statement; those are theorems *about* this, to be proved as `iff` lemmas rather than taken as
the definition.

This is a property of the pair `(P, Aplus)`, not yet of a Huber pair `(A, A⁺)`: `Aplus` is an
arbitrary subring, and independence of the chosen pair of definition — that `locTopology` and
`completionLocObj` do not depend on `P` — is outstanding; nothing in the repo yet compares two
pairs of definition. The roadmap's names `IsSheafyPair A Aplus`, `IsSheafyRing A` and
`IsStablySheafyRing A` are all left free for the `P`-independent notions this one feeds once
that independence is available. -/
def _root_.TauCeti.Huber.PairOfDefinition.HasSheafyPresentationLimit (P : PairOfDefinition A)
    (Aplus : Subring A) : Prop :=
  CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
    (presentationLimitPresheaf P Aplus)

/-- `PairOfDefinition.HasSheafyPresentationLimit` unfolds to Mathlib's sheaf condition. The body
is not
exported, so this is how a consumer moves between the two. -/
theorem _root_.TauCeti.Huber.PairOfDefinition.hasSheafyPresentationLimit_iff
    (P : PairOfDefinition A) (Aplus : Subring A) :
    P.HasSheafyPresentationLimit Aplus ↔
      CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (presentationLimitPresheaf P Aplus) := Iff.rfl

end

end TauCeti.ValuationSpectrum
