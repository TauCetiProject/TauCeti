/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Cofinality
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational.Basic

/-!
# The presentation limit is the limit over rational subsets

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and sets
`𝒪_X(V) = lim_U 𝒪_X(U)`, the limit over the rational subsets `U` contained in the open `V`.
`TauCeti.ValuationSpectrum.presentationLimit` takes the same limit over *presentations* `(T, s)`.
This file builds the diagram of coordinate rings on `TauCeti.ValuationSpectrum.RationalSubsetIndex`
— the rational subsets of `V` — identifies the two limits, and assembles the limits over rational
subsets into a presheaf isomorphic to `TauCeti.ValuationSpectrum.presentationLimitPresheaf`.

## The diagram, and why the choice of presentation is invisible

A rational subset carries no presentation, while `A⟨T/s⟩` is built from the data `(T, s)`. So the
diagram sends a rational subset to the coordinate ring of a presentation *chosen* for it, which
`TauCeti.ValuationSpectrum.exists_presentationToRationalSubsetIndex_obj_eq` supplies. The limit
does not see the choice: two presentations of one rational subset have canonically isomorphic
coordinate rings (`TauCeti.ValuationSpectrum.completionLocObjIsoOfRationalSubsetEq`), and a
containment of rational subsets acts by the comparison morphism of Wedhorn's Proposition 8.2(1),
which depends on the two subsets alone.

The identification of the limits then has two inputs. The diagram of presentations is isomorphic
to this diagram restricted along `TauCeti.ValuationSpectrum.presentationToRationalSubsetIndex`,
by presentation independence again; and that functor is initial, so restricting along it leaves
the limit unchanged. That isomorphism of diagrams is stated on its own, as
`TauCeti.ValuationSpectrum.presentationIndexDiagramIso`, so that it is available apart from the
identification of the limits it is used for here.

## The presheaf

For `W ≤ V` every rational subset of `W` is one of `V`, and restriction from `V` to `W` is the map
of limits along that inclusion of index categories. The two diagrams may choose different
presentations of the same rational subset, so the restriction map also applies the comparison
morphisms of Proposition 8.2(1) between them. The value-wise identification of the two limits
commutes with these restriction maps, which makes it an isomorphism of presheaves and lets
sheafhood pass between them.

All coordinate rings here are those of presentations over one pair of definition `P`, so both
presheaves are built from `P`; this file does not compare the presheaves of two pairs of
definition.

## Main definitions

* `TauCeti.ValuationSpectrum.RationalSubsetIndex.presentationIndex` : the admissible presentation
  chosen for a rational subset.
* `TauCeti.ValuationSpectrum.rationalSubsetIndexDiagram` : the diagram of coordinate rings on the
  rational subsets of `V`, with the comparison morphisms of Proposition 8.2(1) as its action on
  containments.
* `TauCeti.ValuationSpectrum.presentationIndexDiagramIso` : **the two diagrams agree** — the
  diagram of presentations is the diagram above, restricted along
  `TauCeti.ValuationSpectrum.presentationToRationalSubsetIndex`.
* `TauCeti.ValuationSpectrum.presentationLimitToRationalSubsetLimit` : the comparison map from
  the presentation-indexed limit to the subset-indexed one.
* `TauCeti.ValuationSpectrum.presentationLimitIsoRationalSubsetLimit` : that comparison map as an
  isomorphism.
* `TauCeti.ValuationSpectrum.rationalSubsetIndexRestrict` : the inclusion of the rational subsets
  of `W` among those of `V`, for `W ≤ V`.
* `TauCeti.ValuationSpectrum.rationalSubsetLimitMap` : the restriction map of the limits over
  rational subsets.
* `TauCeti.ValuationSpectrum.rationalSubsetLimitPresheaf` : the presheaf `V ↦ lim_{U ⊆ V} A⟨U⟩`.
* `TauCeti.ValuationSpectrum.presentationLimitPresheafIsoRationalSubsetLimitPresheaf` : **the
  presentation-indexed presheaf is the presheaf of limits over rational subsets.**

## Main results

* `TauCeti.ValuationSpectrum.rationalSubset_presentationIndex_eq` : the presentation chosen for a
  rational subset has the same rational subset as any other presentation of it.
* `TauCeti.ValuationSpectrum.presentationLimitToRationalSubsetLimit_comp_π` : the comparison map
  projects at a rational subset to the projection at the presentation chosen for it.
* `TauCeti.ValuationSpectrum.isIso_presentationLimitToRationalSubsetLimit` : **the two limits
  agree**, when `A⁺` consists of power-bounded elements.
* `TauCeti.ValuationSpectrum.presentationLimitToRationalSubsetLimit_naturality` : the comparison
  map commutes with restriction.
* `isSheaf_presentationLimitPresheaf_iff_isSheaf_rationalSubsetLimitPresheaf` : the
  presentation-indexed presheaf is a sheaf exactly when the presheaf of limits over rational
  subsets is.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.1 and Proposition 8.2(1).
-/

namespace TauCeti.ValuationSpectrum

open CategoryTheory CategoryTheory.Limits _root_.TopologicalSpace TauCeti.Huber
  TauCeti.Huber.PairOfDefinition

public section

universe v

variable {A : Type v} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : PairOfDefinition A} {Aplus : Subring A} {V : Opens ↥(spa Aplus)}

/-! ### The presentation chosen for a rational subset -/

/-- **A chosen admissible presentation** of a rational subset of `V`. Every object of
`RationalSubsetIndex` has one, by
`TauCeti.ValuationSpectrum.exists_presentationToRationalSubsetIndex_obj_eq`. Two presentations of
one rational subset have canonically isomorphic coordinate rings
(`TauCeti.ValuationSpectrum.completionLocObjIsoOfRationalSubsetEq`), and the diagram below has the
comparison morphisms of Wedhorn's Proposition 8.2(1) for its arrows, so its limit does not see the
choice. -/
noncomputable def RationalSubsetIndex.presentationIndex (U : RationalSubsetIndex Aplus V) :
    PresentationIndex (P := P) Aplus V :=
  (exists_presentationToRationalSubsetIndex_obj_eq (P := P) U).choose

/-- **The choice is a section of `presentationToRationalSubsetIndex`**: forgetting the chosen
presentation returns the rational subset it was chosen for. This is the equation the choice was
made by, so it, and not the open-level equation below, is what pins the choice down. -/
@[simp]
theorem RationalSubsetIndex.presentationToRationalSubsetIndex_obj_presentationIndex
    (U : RationalSubsetIndex Aplus V) :
    (presentationToRationalSubsetIndex Aplus V).obj (U.presentationIndex (P := P)) = U :=
  (exists_presentationToRationalSubsetIndex_obj_eq (P := P) U).choose_spec

/-- The chosen presentation presents the rational subset it was chosen for. -/
@[simp]
theorem RationalSubsetIndex.spaBasicOpen_presentationIndex (U : RationalSubsetIndex Aplus V) :
    spaBasicOpen Aplus (U.presentationIndex (P := P)).pres.num
        (U.presentationIndex (P := P)).pres.den = (OrderDual.ofDual U).1 := by
  rw [← presentationToRationalSubsetIndex_obj_open Aplus V (U.presentationIndex (P := P)),
    RationalSubsetIndex.presentationToRationalSubsetIndex_obj_presentationIndex]

/-- **A containment of rational subsets is a containment of the chosen presentations' rational
subsets**, so the comparison morphism of Wedhorn's Proposition 8.2(1) is available along it. -/
theorem rationalSubset_presentationIndex_subset {U W : RationalSubsetIndex Aplus V} (h : U ≤ W) :
    rationalSubset Aplus (W.presentationIndex (P := P)).pres.num
        (W.presentationIndex (P := P)).pres.den ⊆
      rationalSubset Aplus (U.presentationIndex (P := P)).pres.num
        (U.presentationIndex (P := P)).pres.den :=
  spaBasicOpen_le_spaBasicOpen_iff.mp <| by
    rw [RationalSubsetIndex.spaBasicOpen_presentationIndex,
      RationalSubsetIndex.spaBasicOpen_presentationIndex]
    exact h

/-- **The choice of presentation does not change the rational subset**: a presentation `i` of the
rational subset `U` and the presentation chosen for `U` have the same rational subset, so the
comparison morphisms of Wedhorn's Proposition 8.2(1) run between their coordinate rings in both
directions. -/
theorem rationalSubset_presentationIndex_eq (U : RationalSubsetIndex Aplus V)
    {i : PresentationIndex (P := P) Aplus V}
    (hi : spaBasicOpen Aplus i.pres.num i.pres.den = (OrderDual.ofDual U).1) :
    rationalSubset Aplus (U.presentationIndex (P := P)).pres.num
        (U.presentationIndex (P := P)).pres.den =
      rationalSubset Aplus i.pres.num i.pres.den :=
  rationalSubset_eq_of_spaBasicOpen_eq
    ((RationalSubsetIndex.spaBasicOpen_presentationIndex (P := P) U).trans hi.symm)

/-! ### The diagram of coordinate rings on rational subsets -/

/-- **The diagram the subset-indexed limit is taken over**: each rational subset of `V`
contributes the coordinate ring of its chosen presentation, and a containment contributes the
comparison morphism of Wedhorn's Proposition 8.2(1). -/
noncomputable def rationalSubsetIndexDiagram (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus)) :
    RationalSubsetIndex Aplus V ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj U := (U.presentationIndex (P := P)).pres.completionLocObj
  map h := homOfRationalSubsetSubset Aplus hAplus
    (rationalSubset_presentationIndex_subset (P := P) h.le)
  map_id _ := homOfRationalSubsetSubset_self Aplus hAplus _
  map_comp _ _ := (homOfRationalSubsetSubset_comp Aplus hAplus _ _).symm

-- The body of `rationalSubsetIndexDiagram` is not exposed, so these two equations are the whole
-- interface another module has to its objects and morphisms; both are `(rfl)` rather than `rfl`
-- because an exported `rfl` theorem may not unfold an unexposed definition.
/-- The diagram sends a rational subset to the coordinate ring of its chosen presentation. -/
@[simp]
theorem rationalSubsetIndexDiagram_obj (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus))
    (U : RationalSubsetIndex Aplus V) :
    (rationalSubsetIndexDiagram (P := P) Aplus hAplus V).obj U =
      (U.presentationIndex (P := P)).pres.completionLocObj := (rfl)

/-- The diagram sends a containment to the comparison morphism of Proposition 8.2(1), between the
coordinate rings of the two chosen presentations. -/
@[simp]
theorem rationalSubsetIndexDiagram_map (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus))
    {U W : RationalSubsetIndex Aplus V} (h : U ⟶ W) :
    (rationalSubsetIndexDiagram (P := P) Aplus hAplus V).map h =
      eqToHom (rationalSubsetIndexDiagram_obj Aplus hAplus V U) ≫
        homOfRationalSubsetSubset Aplus hAplus
          (rationalSubset_presentationIndex_subset (P := P) h.le) ≫
        eqToHom (rationalSubsetIndexDiagram_obj Aplus hAplus V W).symm := (rfl)

/-! ### The universal property of `presentationLimit`, recovered -/

-- `presentationIndexCone` takes its naturality hypothesis indexed by morphisms of
-- `PresentationIndex`; this is `presentationLimitπ_comp_restriction` in that shape, named so that
-- the three uses below are the same term and the cone lemmas about it apply.
private theorem presentationLimitπToPresentation_naturality (Aplus : Subring A)
    (V : Opens ↥(spa Aplus)) :
    ∀ {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j),
      presentationLimitπToPresentation Aplus V i ≫ Presentation.restrictionHom f.le =
        presentationLimitπToPresentation Aplus V j :=
  fun f ↦ presentationLimitπ_comp_restriction f.le

-- `presentationLimit` is sealed, so downstream it is not identified with the limit of
-- `presentationIndexDiagram`. Its projection, lift and extensionality lemmas do make it one, and
-- that is what this cone and its universal property record.
private noncomputable def presentationLimitCone (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    Cone (presentationIndexDiagram (P := P) Aplus V) :=
  presentationIndexCone Aplus V (presentationLimit (P := P) Aplus V)
    (presentationLimitπToPresentation Aplus V)
    (presentationLimitπToPresentation_naturality Aplus V)

private theorem presentationLimitCone_pt (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    (presentationLimitCone (P := P) Aplus V).pt = presentationLimit (P := P) Aplus V :=
  presentationIndexCone_pt Aplus V (presentationLimit (P := P) Aplus V)
    (presentationLimitπToPresentation Aplus V)
    (presentationLimitπToPresentation_naturality Aplus V)

private theorem presentationLimitCone_π_app (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    (presentationLimitCone (P := P) Aplus V).π.app i =
      eqToHom (presentationLimitCone_pt (P := P) Aplus V) ≫ presentationLimitπ Aplus V i := by
  have h : eqToHom (presentationLimitCone_pt (P := P) Aplus V).symm ≫
      (presentationLimitCone (P := P) Aplus V).π.app i = presentationLimitπ Aplus V i := by
    rw [← cancel_mono (eqToHom (presentationIndexDiagram_obj Aplus V i)), Category.assoc]
    exact (presentationIndexCone_π_app Aplus V (presentationLimit (P := P) Aplus V)
      (presentationLimitπToPresentation Aplus V)
      (presentationLimitπToPresentation_naturality Aplus V) i).trans
      (presentationLimitπToPresentation_eq Aplus V i)
  rw [← h, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

private noncomputable def presentationLimitIsLimit (Aplus : Subring A) (V : Opens ↥(spa Aplus)) :
    IsLimit (presentationLimitCone (P := P) Aplus V) where
  lift s := presentationLimitLift Aplus V s ≫
    eqToHom (presentationLimitCone_pt (P := P) Aplus V).symm
  fac s i := by
    simp [presentationLimitCone_π_app]
  uniq s m h := by
    rw [← cancel_mono (eqToHom (presentationLimitCone_pt (P := P) Aplus V))]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    refine presentationLimit_hom_ext fun i ↦ ?_
    rw [Category.assoc, ← presentationLimitCone_π_app, h i, presentationLimitLift_comp_π]

private theorem presentationIndexDiagram_map_eq (Aplus : Subring A) (V : Opens ↥(spa Aplus))
    {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j) :
    (presentationIndexDiagram (P := P) Aplus V).map f =
      eqToHom (presentationIndexDiagram_obj Aplus V i) ≫ Presentation.restrictionHom f.le ≫
        eqToHom (presentationIndexDiagram_obj Aplus V j).symm :=
  (conj_eqToHom_iff_heq _ _ (presentationIndexDiagram_obj Aplus V i)
    (presentationIndexDiagram_obj Aplus V j)).mpr (presentationIndexDiagram_map Aplus V f)

/-! ### The comparison of the two diagrams -/

private noncomputable def presentationIndexDiagramIsoApp (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    (presentationIndexDiagram (P := P) Aplus V).obj i ≅
      (presentationToRationalSubsetIndex Aplus V ⋙
        rationalSubsetIndexDiagram (P := P) Aplus hAplus V).obj i :=
  eqToIso (presentationIndexDiagram_obj Aplus V i) ≪≫
    completionLocObjIsoOfRationalSubsetEq Aplus hAplus
      (rationalSubset_presentationIndex_eq _
        (presentationToRationalSubsetIndex_obj_open Aplus V i).symm).symm ≪≫
    eqToIso (rationalSubsetIndexDiagram_obj (P := P) Aplus hAplus V
      ((presentationToRationalSubsetIndex Aplus V).obj i)).symm

private theorem presentationIndexDiagramIsoApp_naturality (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus))
    {i j : PresentationIndex (P := P) Aplus V} (f : i ⟶ j) :
    (presentationIndexDiagram (P := P) Aplus V).map f ≫
        (presentationIndexDiagramIsoApp Aplus hAplus V j).hom =
      (presentationIndexDiagramIsoApp Aplus hAplus V i).hom ≫
        (presentationToRationalSubsetIndex Aplus V ⋙
          rationalSubsetIndexDiagram (P := P) Aplus hAplus V).map f := by
  -- every morphism in sight is a comparison morphism of Proposition 8.2(1), and those compose to
  -- the comparison morphism of the composite containment
  simp [presentationIndexDiagramIsoApp, presentationIndexDiagram_map_eq,
    restrictionHom_eq_homOfRationalSubsetSubset Aplus hAplus]

/-- **The diagram of presentations is the rational-subset diagram, restricted along
`presentationToRationalSubsetIndex`.** This is the compatibility of the new diagram with the
existing one: the coordinate ring of a presentation and the coordinate ring of the presentation
chosen for the rational subset it presents are canonically isomorphic, naturally in the
presentation.

Identifying the two limits is one use of it; as an isomorphism of the diagrams themselves it also
transports cones, restrictions along a functor, and whatever else is built from a diagram. The
body is not exposed; `presentationIndexDiagramIso_hom_app` and
`presentationIndexDiagramIso_inv_app` give its components in both directions. -/
noncomputable def presentationIndexDiagramIso (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus)) :
    presentationIndexDiagram (P := P) Aplus V ≅
      presentationToRationalSubsetIndex Aplus V ⋙
        rationalSubsetIndexDiagram (P := P) Aplus hAplus V :=
  NatIso.ofComponents (presentationIndexDiagramIsoApp Aplus hAplus V)
    (presentationIndexDiagramIsoApp_naturality Aplus hAplus V)

/-- **The comparison at a presentation is a comparison morphism of Proposition 8.2(1)**: at a
presentation `i` the isomorphism of the two diagrams is the comparison morphism of the containment
supplied by `rationalSubset_presentationIndex_eq`, from the coordinate ring of `i` to that of the
presentation chosen for the rational subset `i` presents, transported to the two diagrams'
objects. -/
@[simp]
theorem presentationIndexDiagramIso_hom_app (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    (presentationIndexDiagramIso Aplus hAplus V).hom.app i =
      eqToHom (presentationIndexDiagram_obj Aplus V i) ≫
        homOfRationalSubsetSubset Aplus hAplus
          (rationalSubset_presentationIndex_eq _
            (presentationToRationalSubsetIndex_obj_open Aplus V i).symm).le ≫
        eqToHom (rationalSubsetIndexDiagram_obj (P := P) Aplus hAplus V
          ((presentationToRationalSubsetIndex Aplus V).obj i)).symm := by
  rw [presentationIndexDiagramIso]
  simp [presentationIndexDiagramIsoApp]

/-- **The inverse comparison at a presentation is the comparison morphism of the reverse
containment**: the two rational subsets are equal, so Wedhorn's Proposition 8.2(1) supplies a
morphism each way, and the inverse of the isomorphism of the two diagrams is the one running from
the coordinate ring of the presentation chosen for the rational subset `i` presents back to that
of `i`, transported to the two diagrams' objects. -/
@[simp]
theorem presentationIndexDiagramIso_inv_app (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus))
    (i : PresentationIndex (P := P) Aplus V) :
    (presentationIndexDiagramIso Aplus hAplus V).inv.app i =
      eqToHom (rationalSubsetIndexDiagram_obj (P := P) Aplus hAplus V
          ((presentationToRationalSubsetIndex Aplus V).obj i)) ≫
        homOfRationalSubsetSubset Aplus hAplus
          (rationalSubset_presentationIndex_eq _
            (presentationToRationalSubsetIndex_obj_open Aplus V i).symm).ge ≫
        eqToHom (presentationIndexDiagram_obj Aplus V i).symm := by
  rw [presentationIndexDiagramIso]
  simp [presentationIndexDiagramIsoApp]

/-! ### The comparison map of the two limits -/

private noncomputable def rationalSubsetCone (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus)) :
    Cone (rationalSubsetIndexDiagram (P := P) Aplus hAplus V) where
  pt := presentationLimit (P := P) Aplus V
  π :=
    { app := fun U ↦ presentationLimitπToPresentation Aplus V (U.presentationIndex (P := P)) ≫
        eqToHom (rationalSubsetIndexDiagram_obj (P := P) Aplus hAplus V U).symm
      naturality := fun U W h ↦ by
        simp [presentationLimitπ_eq_π_comp hAplus (U.presentationIndex (P := P))
          (W.presentationIndex (P := P))
          (rationalSubset_presentationIndex_subset (P := P) h.le)] }

/-- **The comparison map of the two limits**: the map to the limit over the rational subsets of
`V` whose component at a rational subset is the projection of `presentationLimit` at the
presentation chosen for that subset. It is an isomorphism
(`isIso_presentationLimitToRationalSubsetLimit`). -/
noncomputable def presentationLimitToRationalSubsetLimit (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus)) :
    presentationLimit (P := P) Aplus V ⟶
      limit (rationalSubsetIndexDiagram (P := P) Aplus hAplus V) :=
  limit.lift _ (rationalSubsetCone Aplus hAplus V)

/-- **The comparison map projects to the chosen presentations**: its component at a rational
subset of `V` is the projection of `presentationLimit` at the presentation chosen for that
subset, transported to the diagram object. -/
@[simp]
theorem presentationLimitToRationalSubsetLimit_comp_π (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus))
    (U : RationalSubsetIndex Aplus V) :
    presentationLimitToRationalSubsetLimit Aplus hAplus V ≫
        limit.π (rationalSubsetIndexDiagram (P := P) Aplus hAplus V) U =
      presentationLimitπToPresentation Aplus V (U.presentationIndex (P := P)) ≫
        eqToHom (rationalSubsetIndexDiagram_obj (P := P) Aplus hAplus V U).symm :=
  limit.lift_π _ _

private theorem presentationLimitToRationalSubsetLimit_comp_pre (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus)) :
    presentationLimitToRationalSubsetLimit Aplus hAplus V ≫
        limit.pre (rationalSubsetIndexDiagram (P := P) Aplus hAplus V)
          (presentationToRationalSubsetIndex Aplus V) =
      (eqToIso (presentationLimitCone_pt (P := P) Aplus V).symm ≪≫
        IsLimit.conePointsIsoOfNatIso (presentationLimitIsLimit Aplus V) (limit.isLimit _)
          (presentationIndexDiagramIso Aplus hAplus V)).hom := by
  refine limit.hom_ext fun i ↦ ?_
  have key : (eqToIso (presentationLimitCone_pt (P := P) Aplus V).symm ≪≫
      IsLimit.conePointsIsoOfNatIso (presentationLimitIsLimit Aplus V) (limit.isLimit _)
        (presentationIndexDiagramIso Aplus hAplus V)).hom ≫
        limit.π (presentationToRationalSubsetIndex Aplus V ⋙
          rationalSubsetIndexDiagram (P := P) Aplus hAplus V) i =
      eqToHom (presentationLimitCone_pt (P := P) Aplus V).symm ≫
        (presentationLimitCone (P := P) Aplus V).π.app i ≫
          (presentationIndexDiagramIso Aplus hAplus V).hom.app i := by
    rw [Iso.trans_hom, eqToIso.hom, Category.assoc]
    exact congrArg (eqToHom (presentationLimitCone_pt (P := P) Aplus V).symm ≫ ·)
      (IsLimit.conePointsIsoOfNatIso_hom_comp (presentationLimitIsLimit Aplus V)
        (limit.isLimit _) (presentationIndexDiagramIso Aplus hAplus V) i)
  rw [Category.assoc, limit.pre_π, presentationLimitToRationalSubsetLimit_comp_π,
    presentationLimitπ_eq_π_comp hAplus i _ (rationalSubset_presentationIndex_eq _
      (presentationToRationalSubsetIndex_obj_open Aplus V i).symm).le, key,
    presentationLimitCone_π_app]
  simp [presentationLimitπToPresentation_eq]

/-- **The two limits agree.** The comparison map from the presentation-indexed limit to the limit
over the rational subsets of `V` is an isomorphism, when `A⁺` consists of power-bounded elements:
the presentations are cofinal among the rational subsets, and the two diagrams agree up to
canonical isomorphism. -/
theorem isIso_presentationLimitToRationalSubsetLimit (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus)) :
    IsIso (presentationLimitToRationalSubsetLimit (P := P) Aplus hAplus V) :=
  -- the isomorphism's own `IsIso` instance is passed by hand: its endpoints are the cone point of
  -- `presentationLimitCone`, which instance search does not reduce to `presentationLimit`
  IsIso.of_isIso_fac_right (hh := Iso.isIso_hom _)
    (presentationLimitToRationalSubsetLimit_comp_pre (P := P) Aplus hAplus V)

/-- **The presentation-indexed limit is the limit over rational subsets**, as an isomorphism of
complete separated topological rings. Its forward map is
`presentationLimitToRationalSubsetLimit`. -/
noncomputable def presentationLimitIsoRationalSubsetLimit (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus)) :
    presentationLimit (P := P) Aplus V ≅
      limit (rationalSubsetIndexDiagram (P := P) Aplus hAplus V) :=
  haveI := isIso_presentationLimitToRationalSubsetLimit (P := P) Aplus hAplus V
  asIso (presentationLimitToRationalSubsetLimit (P := P) Aplus hAplus V)

/-- The isomorphism of the two limits is the comparison map. -/
@[simp]
theorem presentationLimitIsoRationalSubsetLimit_hom (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : Opens ↥(spa Aplus)) :
    (presentationLimitIsoRationalSubsetLimit (P := P) Aplus hAplus V).hom =
      presentationLimitToRationalSubsetLimit Aplus hAplus V := (rfl)

/-! ### The presheaf of limits over rational subsets -/

/-- **The inclusion of the rational subsets of `W` among those of `V`**, for `W ≤ V`, as a functor
of index categories: precomposing with it restricts a diagram on the rational subsets of `V` to
those of `W`. -/
def rationalSubsetIndexRestrict {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    RationalSubsetIndex Aplus W ⥤ RationalSubsetIndex Aplus V :=
  (Subtype.orderEmbedding fun _ hU ↦ ⟨hU.1, hU.2.trans h⟩).dual.monotone.functor

omit [IsTopologicalRing A] in
/-- Including a rational subset of `W` among those of `V` keeps its underlying open. -/
@[simp]
theorem rationalSubsetIndexRestrict_obj_open {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (U : RationalSubsetIndex Aplus W) :
    (OrderDual.ofDual ((rationalSubsetIndexRestrict h).obj U)).1 = (OrderDual.ofDual U).1 := (rfl)

omit [IsTopologicalRing A] in
/-- Including a rational subset of `U` among those of `W`, and then among those of `V`, is including
it among those of `V` directly. -/
theorem rationalSubsetIndexRestrict_obj_restrict {U V W : Opens ↥(spa Aplus)} (h₁ : W ≤ V)
    (h₂ : U ≤ W) (X : RationalSubsetIndex Aplus U) :
    (rationalSubsetIndexRestrict h₁).obj ((rationalSubsetIndexRestrict h₂).obj X) =
      (rationalSubsetIndexRestrict (h₂.trans h₁)).obj X :=
  (rfl)

/-- For `W ≤ V`, the presentations chosen for a rational subset `U` of `W` in `W` and in `V` both
present `U`, so the comparison morphism of Proposition 8.2(1) runs from the second to the first. -/
theorem rationalSubset_presentationIndex_subset_restrict {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (U : RationalSubsetIndex Aplus W) : rationalSubset Aplus (U.presentationIndex (P := P)).pres.num
      (U.presentationIndex (P := P)).pres.den ⊆ rationalSubset Aplus
        (((rationalSubsetIndexRestrict h).obj U).presentationIndex (P := P)).pres.num
        (((rationalSubsetIndexRestrict h).obj U).presentationIndex (P := P)).pres.den :=
  spaBasicOpen_le_spaBasicOpen_iff.mp <| by simp

/-- **The comparison of the two diagrams on the rational subsets of `W`**, for `W ≤ V`: from the
diagram of `V`, restricted to the rational subsets of `W`, to the diagram of `W`. The body is not
exposed; `rationalSubsetIndexDiagramRestrictComparison_app` gives the components. -/
noncomputable def rationalSubsetIndexDiagramRestrictComparison
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    rationalSubsetIndexRestrict h ⋙ rationalSubsetIndexDiagram (P := P) Aplus hAplus V ⟶
      rationalSubsetIndexDiagram (P := P) Aplus hAplus W where
  app U := homOfRationalSubsetSubset Aplus hAplus
    (rationalSubset_presentationIndex_subset_restrict (P := P) h U)
  -- all four maps in the square are comparison morphisms of Proposition 8.2(1), which compose
  naturality _ _ _ := by simp [rationalSubsetIndexDiagram]

/-- At a rational subset `U` of `W`, the comparison of the two diagrams is the comparison morphism
of Proposition 8.2(1) from the coordinate ring of the presentation chosen for `U` in `V` to that of
the one chosen in `W`, transported to the diagram objects. -/
@[simp]
theorem rationalSubsetIndexDiagramRestrictComparison_app
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) {V W : Opens ↥(spa Aplus)} (h : W ≤ V)
    (U : RationalSubsetIndex Aplus W) :
    (rationalSubsetIndexDiagramRestrictComparison (P := P) hAplus h).app U =
      eqToHom (rationalSubsetIndexDiagram_obj Aplus hAplus V _) ≫
        homOfRationalSubsetSubset Aplus hAplus
          (rationalSubset_presentationIndex_subset_restrict (P := P) h U) ≫
        eqToHom (rationalSubsetIndexDiagram_obj Aplus hAplus W U).symm := (rfl)

/-- **The restriction map of the limit over rational subsets**, for `W ≤ V`: the map
`lim_{U ⊆ V} A⟨U⟩ ⟶ lim_{U ⊆ W} A⟨U⟩` of Wedhorn §8.1, reindexing along
`rationalSubsetIndexRestrict h` followed by `rationalSubsetIndexDiagramRestrictComparison`. The
body is not exposed; `rationalSubsetLimitMap_comp_π` gives its projections. -/
noncomputable def rationalSubsetLimitMap (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a)
    {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    limit (rationalSubsetIndexDiagram (P := P) Aplus hAplus V) ⟶
      limit (rationalSubsetIndexDiagram (P := P) Aplus hAplus W) :=
  limit.pre _ (rationalSubsetIndexRestrict h) ≫
    limMap (rationalSubsetIndexDiagramRestrictComparison (P := P) hAplus h)

/-- **Restriction then projection**: projecting the restriction at a rational subset `U` of `W` is
projecting at `U` as a rational subset of `V`, then comparing the two diagrams at `U`. -/
@[simp]
theorem rationalSubsetLimitMap_comp_π (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a)
    {V W : Opens ↥(spa Aplus)} (h : W ≤ V) (U : RationalSubsetIndex Aplus W) :
    rationalSubsetLimitMap (P := P) hAplus h ≫
        limit.π (rationalSubsetIndexDiagram (P := P) Aplus hAplus W) U =
      limit.π (rationalSubsetIndexDiagram (P := P) Aplus hAplus V)
          ((rationalSubsetIndexRestrict h).obj U) ≫
        (rationalSubsetIndexDiagramRestrictComparison (P := P) hAplus h).app U := by
  simp [rationalSubsetLimitMap]

/-- **The comparison of the two limits commutes with restriction**: for `W ≤ V`, restricting the
presentation-indexed limit from `V` to `W` and then comparing agrees with comparing at `V` and then
restricting the limit over rational subsets. -/
theorem presentationLimitToRationalSubsetLimit_naturality
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) {V W : Opens ↥(spa Aplus)} (h : W ≤ V) :
    presentationLimitMap (P := P) h ≫ presentationLimitToRationalSubsetLimit Aplus hAplus W =
      presentationLimitToRationalSubsetLimit Aplus hAplus V ≫ rationalSubsetLimitMap hAplus h := by
  refine limit.hom_ext fun U ↦ ?_
  -- both sides project to a comparison morphism out of the presentation chosen for `U` in `V`
  have hU := rationalSubset_presentationIndex_subset_restrict (P := P) h U
  have hπ := presentationLimitπ_eq_π_comp hAplus _
    ((presentationIndexRestrict h).obj (U.presentationIndex (P := P))) (hU.trans_eq' <| by simp)
  -- on the left, the transport between the two equal presentations of `U` is absorbed into it
  simp only [Category.assoc, presentationLimitToRationalSubsetLimit_comp_π,
    reassoc_of% presentationLimitMap_comp_πToPresentation, hπ,
    reassoc_of% homOfRationalSubsetSubset_comp_eqToHom hAplus
      (presentationIndexRestrict_obj_pres h _) _ hU]
  -- on the right, it is the comparison of the two diagrams at `U`
  simp [reassoc_of% presentationLimitToRationalSubsetLimit_comp_π Aplus hAplus]

/-- **Restricting along `le_refl` is the identity.** -/
@[simp]
theorem rationalSubsetLimitMap_refl (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a)
    (V : Opens ↥(spa Aplus)) : rationalSubsetLimitMap (P := P) hAplus (le_refl V) = 𝟙 _ := by
  refine limit.hom_ext fun U ↦ ?_
  -- `(rationalSubsetIndexRestrict (le_refl V)).obj U` is `U`, and the comparison there is the
  -- diagram's own map along that equality
  rw [rationalSubsetLimitMap_comp_π, Category.id_comp,
    ← limit.w _ (homOfLE le_rfl : (rationalSubsetIndexRestrict (le_refl V)).obj U ⟶ U)]
  simp

/-- **Successive restrictions compose** to the restriction along the transitive containment. -/
@[simp]
theorem rationalSubsetLimitMap_comp (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a)
    {U V W : Opens ↥(spa Aplus)} (h₁ : W ≤ V) (h₂ : U ≤ W) :
    rationalSubsetLimitMap (P := P) hAplus h₁ ≫ rationalSubsetLimitMap hAplus h₂ =
      rationalSubsetLimitMap hAplus (h₂.trans h₁) := by
  refine limit.hom_ext fun U' ↦ ?_
  -- both sides are one comparison morphism out of the same rational subset of `V`, reached by
  -- restricting along `h₂` and then `h₁`, or along `h₂.trans h₁`
  rw [Category.assoc, rationalSubsetLimitMap_comp_π, reassoc_of% rationalSubsetLimitMap_comp_π,
    rationalSubsetLimitMap_comp_π,
    ← limit.w _ (homOfLE (rationalSubsetIndexRestrict_obj_restrict h₁ h₂ U').le), Category.assoc]
  simp

/-- **The presheaf `V ↦ lim_{U ⊆ V} A⟨U⟩`** on `Spa(A,A⁺)` of Wedhorn §8.1, valued in
`CompleteSeparatedTopCommRingCat`, with the coordinate rings of presentations over `P` and
restriction maps `rationalSubsetLimitMap`. The body is not exposed;
`rationalSubsetLimitPresheaf_obj` and `rationalSubsetLimitPresheaf_map` give its values and
restriction maps. -/
noncomputable def rationalSubsetLimitPresheaf (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) :
    (Opens ↥(spa Aplus))ᵒᵖ ⥤ CompleteSeparatedTopCommRingCat.{v} where
  obj V := limit (rationalSubsetIndexDiagram (P := P) Aplus hAplus V.unop)
  map h := rationalSubsetLimitMap hAplus (leOfHom h.unop)
  map_id V := rationalSubsetLimitMap_refl hAplus V.unop
  map_comp f g := (rationalSubsetLimitMap_comp hAplus (leOfHom f.unop) (leOfHom g.unop)).symm

/-- Evaluating the presheaf on an open is the limit over the rational subsets it contains. -/
@[simp]
theorem rationalSubsetLimitPresheaf_obj (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (rationalSubsetLimitPresheaf P Aplus hAplus).obj V =
      limit (rationalSubsetIndexDiagram (P := P) Aplus hAplus V.unop) :=
  (rfl)

/-- The presheaf's action on a containment is `rationalSubsetLimitMap`, transported along
`rationalSubsetLimitPresheaf_obj`. -/
@[simp]
theorem rationalSubsetLimitPresheaf_map (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) {V W : (Opens ↥(spa Aplus))ᵒᵖ} (h : V ⟶ W) :
    (rationalSubsetLimitPresheaf P Aplus hAplus).map h =
      eqToHom (rationalSubsetLimitPresheaf_obj P Aplus hAplus V) ≫
        rationalSubsetLimitMap hAplus (leOfHom h.unop) ≫
          eqToHom (rationalSubsetLimitPresheaf_obj P Aplus hAplus W).symm :=
  (rfl)

/-- **The presentation-indexed presheaf is the presheaf of limits over rational subsets**, when
`A⁺` consists of power-bounded elements; at an open `V` it is
`presentationLimitIsoRationalSubsetLimit`. Both presheaves are built from the pair of definition
`P`. The body is not exposed; `presentationLimitPresheafIsoRationalSubsetLimitPresheaf_hom_app`
gives its components. -/
noncomputable def presentationLimitPresheafIsoRationalSubsetLimitPresheaf (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) :
    presentationLimitPresheaf P Aplus ≅ rationalSubsetLimitPresheaf P Aplus hAplus :=
  NatIso.ofComponents
    (fun V ↦ eqToIso (presentationLimitPresheaf_obj P Aplus V) ≪≫
      presentationLimitIsoRationalSubsetLimit Aplus hAplus V.unop ≪≫
      eqToIso (rationalSubsetLimitPresheaf_obj P Aplus hAplus V).symm)
    -- instantiating the naturality lemma at `hAplus` keeps this `simp` fast
    (by simp [reassoc_of% presentationLimitToRationalSubsetLimit_naturality hAplus])

-- Deliberately not `@[simp]`: `simp` would rewrite the forward component before
-- `Iso.hom_inv_id_app` or `Iso.inv_hom_id_app` could cancel it against the inverse component.
/-- At an open `V`, the forward map of the isomorphism of the two presheaves is the comparison map
`presentationLimitToRationalSubsetLimit` of the two limits at `V`, transported along
`presentationLimitPresheaf_obj` and `rationalSubsetLimitPresheaf_obj`. -/
theorem presentationLimitPresheafIsoRationalSubsetLimitPresheaf_hom_app (P : PairOfDefinition A)
    (Aplus : Subring A) (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a)
    (V : (Opens ↥(spa Aplus))ᵒᵖ) :
    (presentationLimitPresheafIsoRationalSubsetLimitPresheaf P Aplus hAplus).hom.app V =
      eqToHom (presentationLimitPresheaf_obj P Aplus V) ≫
        presentationLimitToRationalSubsetLimit Aplus hAplus V.unop ≫
          eqToHom (rationalSubsetLimitPresheaf_obj P Aplus hAplus V).symm :=
  (rfl)

/-- **Sheafhood transfers between the two presheaves**: when `A⁺` consists of power-bounded
elements, `presentationLimitPresheaf P Aplus` is a sheaf exactly when
`rationalSubsetLimitPresheaf P Aplus hAplus` is. -/
theorem isSheaf_presentationLimitPresheaf_iff_isSheaf_rationalSubsetLimitPresheaf
    (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a : A⦄, a ∈ Aplus → IsPowerBounded a) : Presheaf.IsSheaf
      (Opens.grothendieckTopology ↥(spa Aplus)) (presentationLimitPresheaf P Aplus) ↔
      Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Aplus))
        (rationalSubsetLimitPresheaf P Aplus hAplus) :=
  Presheaf.isSheaf_of_iso_iff (presentationLimitPresheafIsoRationalSubsetLimitPresheaf _ _ _)

end

end TauCeti.ValuationSpectrum
