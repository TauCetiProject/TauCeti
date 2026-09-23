/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Cofinality
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Rational

/-!
# The presentation limit is the limit over rational subsets

Wedhorn §8.1 assigns `A⟨T/s⟩` to the rational subset `R(T/s)` and sets
`𝒪_X(V) = lim_U 𝒪_X(U)`, the limit over the rational subsets `U` contained in the open `V`.
`TauCeti.ValuationSpectrum.presentationLimit` takes the same limit over *presentations* `(T, s)`.
This file builds the diagram of coordinate rings on `TauCeti.ValuationSpectrum.RationalSubsetIndex`
— the rational subsets of `V` — and identifies the two limits.

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

## Main results

* `TauCeti.ValuationSpectrum.rationalSubset_presentationIndex_eq` : the presentation chosen for a
  rational subset has the same rational subset as any other presentation of it.
* `TauCeti.ValuationSpectrum.presentationLimitToRationalSubsetLimit_comp_π` : the comparison map
  projects at a rational subset to the projection at the presentation chosen for it.
* `TauCeti.ValuationSpectrum.isIso_presentationLimitToRationalSubsetLimit` : **the two limits
  agree**, when `A⁺` consists of power-bounded elements.

## What this does not give

The identification is of *values* — it is not known to commute with the restriction maps, so the
two presheaves are not identified.

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

end

end TauCeti.ValuationSpectrum
