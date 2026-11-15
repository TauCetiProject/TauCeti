/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.CompactlyGenerated
public import TauCeti.Topology.Convenient.Category
public import TauCeti.Topology.Convenient.CompactlyGenerated

/-!
# Equivalence with `GeneratedByTopCat` and coreflection of `CompactlyGenerated` in `TopCat`

Evaluating `GeneratedByTopCat` at the generating family `fun K : CompHaus.{u} ↦ K` of compact
Hausdorff spaces in universe `u` yields a strict equivalence of categories
`CompactlyGenerated.equivGeneratedByTopCat : CompactlyGenerated.{u, w} ≌ GeneratedByTopCat.{w} ...`
over `TopCat.{w}`, with `u` independent of `w`.

Transporting the general convenient-category coreflection along this equivalence establishes:

* `TopCat.toCompactlyGenerated` and `CompactlyGenerated.adj`: `CompactlyGenerated.{u, w}` is a
  coreflective full subcategory of `TopCat.{w}`
  (`CompactlyGenerated.instCoreflectiveCompactlyGeneratedToTop`), creating all colimits and
  admitting all small limits and colimits.
* `CompactlyGenerated.isIso_adjCounit_app_iff` and `CompactlyGenerated.instIsIsoAdjCounitApp`:
  the coreflection counit at `X : TopCat.{w}` is an isomorphism if and only if `X` is
  `u`-compactly generated, and in particular synthesizes automatically via
  `TauCeti.uCompactlyGeneratedSpace_of_compactlyCoherentSpace` whenever `X` is `u`-small,
  Hausdorff, and compactly coherent (including every `u`-small Hausdorff weakly locally compact
  space or `CompactlyGeneratedSpace`).

## References

* R. M. Vogt, *Convenient categories of topological spaces for homotopy theory*, Arch. Math.
  (Basel) 22 (1971), 545–555.
* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
-/

public section

universe w' v' u v w

open CategoryTheory Limits Topology

namespace CompactlyGenerated

/-- Construct a morphism in `CompactlyGenerated` from a `ContinuousMap`. -/
abbrev homMk {X Y : CompactlyGenerated.{u, w}} (f : C(X.toTop, Y.toTop)) : X ⟶ Y :=
  ConcreteCategory.ofHom f

theorem homMk_apply {X Y : CompactlyGenerated.{u, w}} (f : C(X.toTop, Y.toTop)) (x : X) :
    homMk f x = f x :=
  (rfl)

@[simp]
theorem hom_apply {X Y : CompactlyGenerated.{u, w}} (f : X ⟶ Y) (x : X) :
    f.hom x = f x :=
  (rfl)

@[ext]
theorem hom_ext {X Y : CompactlyGenerated.{u, w}} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g :=
  InducedCategory.hom_ext (TopCat.ext h)

/-- The canonical functor identifying `CompactlyGenerated.{u, w}` with
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`.

Exposed so that downstream modules and code generation agree on transported object carriers. -/
@[expose]
def toGeneratedByTopCat :
    CompactlyGenerated.{u, w} ⥤ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) where
  obj X := ⟨X.toTop, inferInstance⟩
  map f := InducedCategory.homMk f.hom

@[simp]
theorem toGeneratedByTopCat_obj_obj (X : CompactlyGenerated.{u, w}) :
    (toGeneratedByTopCat.obj X).obj = X.toTop :=
  (rfl)

@[simp]
theorem toGeneratedByTopCat_map_apply {X Y : CompactlyGenerated.{u, w}} (f : X ⟶ Y) (x : X) :
    toGeneratedByTopCat.map f x = f x :=
  (rfl)

instance (X : CompactlyGenerated.{u, w}) [LocallyCompactSpace X] :
    LocallyCompactSpace (toGeneratedByTopCat.obj X) :=
  ‹LocallyCompactSpace X›

instance (X : CompactlyGenerated.{u, w}) [T2Space X] :
    T2Space (toGeneratedByTopCat.obj X) :=
  ‹T2Space X›

instance (X : CompactlyGenerated.{u, w}) [Small.{v} X] :
    Small.{v} (toGeneratedByTopCat.obj X) :=
  ‹Small.{v} X›

/-- The canonical inverse functor from `GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)` to
`CompactlyGenerated.{u, w}`.

Exposed so that downstream modules and code generation agree on transported object carriers. -/
@[expose]
def fromGeneratedByTopCat :
    GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) ⥤ CompactlyGenerated.{u, w} where
  obj Y :=
    { toTop := Y.obj
      is_compactly_generated := (Topology.isGeneratedBy_compHaus_iff Y.obj).1 Y.property }
  map f := InducedCategory.homMk f.hom

@[simp]
theorem fromGeneratedByTopCat_obj_toTop
    (Y : GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)) :
    (fromGeneratedByTopCat.obj Y).toTop = Y.obj :=
  (rfl)

@[simp]
theorem fromGeneratedByTopCat_map_apply
    {Y Z : GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)} (f : Y ⟶ Z) (y : Y) :
    fromGeneratedByTopCat.map f y = f y :=
  (rfl)

/-- `CompactlyGenerated.{u, w}` is strictly equivalent to
`GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K)`. -/
@[expose, simps]
def equivGeneratedByTopCat :
    CompactlyGenerated.{u, w} ≌ GeneratedByTopCat.{w} (fun K : CompHaus.{u} ↦ K) where
  functor := toGeneratedByTopCat
  inverse := fromGeneratedByTopCat
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := Category.comp_id (𝟙 (toGeneratedByTopCat.obj X))

instance : toGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivGeneratedByTopCat.isEquivalence_functor

instance : fromGeneratedByTopCat.{u, w}.IsEquivalence :=
  equivGeneratedByTopCat.isEquivalence_inverse

@[simp]
theorem toGeneratedByTopCat_comp_toTopCat :
    toGeneratedByTopCat.{u, w} ⋙ GeneratedByTopCat.toTopCat = compactlyGeneratedToTop.{u, w} :=
  (rfl)

@[simp]
theorem fromGeneratedByTopCat_comp_compactlyGeneratedToTop :
    fromGeneratedByTopCat.{u, w} ⋙ compactlyGeneratedToTop.{u, w} =
      GeneratedByTopCat.toTopCat (X := fun K : CompHaus.{u} ↦ K) :=
  (rfl)

end CompactlyGenerated

/-- The compactly generated coreflection `TopCat.{w} ⥤ CompactlyGenerated.{u, w}`, endowing a
topological space with its `u`-compactly generated topology. -/
@[expose]
def TopCat.toCompactlyGenerated : TopCat.{w} ⥤ CompactlyGenerated.{u, w} :=
  TopCat.toGeneratedByTopCat (X := fun K : CompHaus.{u} ↦ K) ⋙
    CompactlyGenerated.fromGeneratedByTopCat.{u, w}

@[simp]
theorem TopCat.toCompactlyGenerated_obj_toTop (X : TopCat.{w}) :
    (TopCat.toCompactlyGenerated.{u, w}.obj X).toTop =
      TopCat.of (WithGeneratedByTopology (fun K : CompHaus.{u} ↦ K) X) :=
  (rfl)

@[simp]
theorem TopCat.toCompactlyGenerated_map_apply {X Y : TopCat.{w}} (f : X ⟶ Y)
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    TopCat.toCompactlyGenerated.{u, w}.map f x =
      (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K)).symm
        (f (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) x)) :=
  (rfl)

namespace CompactlyGenerated

/-- The unit isomorphism of the coreflective adjunction `CompactlyGenerated.adj`. -/
def adjUnitIso :
    𝟭 CompactlyGenerated.{u, w} ≅ compactlyGeneratedToTop.{u, w} ⋙ TopCat.toCompactlyGenerated :=
  Functor.isoWhiskerLeft toGeneratedByTopCat
    (Functor.isoWhiskerRight
      (GeneratedByTopCat.adjUnitIso (X := fun K : CompHaus.{u} ↦ K)) fromGeneratedByTopCat)

@[simp]
theorem adjUnitIso_hom_app_apply (X : CompactlyGenerated.{u, w}) (x : X) :
    ConcreteCategory.hom (X := X)
      (Y := TopCat.toCompactlyGenerated.{u, w}.obj (compactlyGeneratedToTop.obj X))
      (adjUnitIso.{u, w}.hom.app X) x =
      (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K)).symm x :=
  (rfl)

@[simp]
theorem adjUnitIso_inv_app_apply (X : CompactlyGenerated.{u, w})
    (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj (compactlyGeneratedToTop.obj X))) :
    ConcreteCategory.hom
      (X := TopCat.toCompactlyGenerated.{u, w}.obj (compactlyGeneratedToTop.obj X)) (Y := X)
      (adjUnitIso.{u, w}.inv.app X) x =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X) x :=
  (rfl)

/-- The counit of the coreflective adjunction `CompactlyGenerated.adj`. -/
def adjCounit :
    TopCat.toCompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w} ⟶ 𝟭 TopCat.{w} :=
  GeneratedByTopCat.adjCounit (X := fun K : CompHaus.{u} ↦ K)

theorem adjCounit_app (X : TopCat.{w}) :
    adjCounit.{u, w}.app X =
      (GeneratedByTopCat.adjCounit (X := fun K : CompHaus.{u} ↦ K)).app X :=
  (rfl)

@[simp]
theorem adjCounit_app_apply (X : TopCat.{w}) (x : ↑(TopCat.toCompactlyGenerated.{u, w}.obj X)) :
    ConcreteCategory.hom
      (X := compactlyGeneratedToTop.{u, w}.obj (TopCat.toCompactlyGenerated.{u, w}.obj X)) (Y := X)
      (adjCounit.{u, w}.app X) x =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := X) x :=
  GeneratedByTopCat.adjCounit_app_apply (fun K : CompHaus.{u} ↦ K) X x

/-- The coreflective adjunction `compactlyGeneratedToTop ⊣ TopCat.toCompactlyGenerated`. -/
def adj : compactlyGeneratedToTop.{u, w} ⊣ TopCat.toCompactlyGenerated.{u, w} where
  unit := adjUnitIso.hom
  counit := adjCounit
  left_triangle_components X :=
    (GeneratedByTopCat.adj (X := fun K : CompHaus.{u} ↦ K)).left_triangle_components
      (toGeneratedByTopCat.obj X)
  right_triangle_components Y :=
    congrArg fromGeneratedByTopCat.map <|
      (GeneratedByTopCat.adj (X := fun K : CompHaus.{u} ↦ K)).right_triangle_components Y

@[simp]
theorem adj_unit : adj.{u, w}.unit = adjUnitIso.hom := by
  rfl

@[simp]
theorem adj_counit : adj.{u, w}.counit = adjCounit := by
  rfl

@[simp]
theorem adj_homEquiv_apply {X : CompactlyGenerated.{u, w}} {Y : TopCat.{w}}
    (f : compactlyGeneratedToTop.{u, w}.obj X ⟶ Y) (x : X) :
    (adj.{u, w}.homEquiv X Y f) x =
      (WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K)).symm (f x) :=
  GeneratedByTopCat.adj_homEquiv_apply (G := fun K : CompHaus.{u} ↦ K)
    (Y := toGeneratedByTopCat.obj X) (X := Y) f x

@[simp]
theorem adj_homEquiv_symm_apply {X : CompactlyGenerated.{u, w}} {Y : TopCat.{w}}
    (g : X ⟶ TopCat.toCompactlyGenerated.{u, w}.obj Y) (x : X) :
    ((adj.{u, w}.homEquiv X Y).symm g) x =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} ↦ K) (Y := Y) (g x) :=
  GeneratedByTopCat.adj_homEquiv_symm_apply (G := fun K : CompHaus.{u} ↦ K)
    (Y := toGeneratedByTopCat.obj X) (X := Y) (toGeneratedByTopCat.map g) x

instance : IsIso adj.{u, w}.unit :=
  inferInstanceAs (IsIso adjUnitIso.{u, w}.hom)

instance : compactlyGeneratedToTop.{u, w}.IsLeftAdjoint :=
  adj.isLeftAdjoint

instance : TopCat.toCompactlyGenerated.{u, w}.IsRightAdjoint :=
  adj.isRightAdjoint

instance : TopCat.toCompactlyGenerated.{u, w}.Faithful :=
  Functor.Faithful.comp _ _

/-- `CompactlyGenerated.{u, w}` is a coreflective subcategory of `TopCat.{w}`. -/
instance instCoreflectiveCompactlyGeneratedToTop :
    Coreflective compactlyGeneratedToTop.{u, w} where
  R := TopCat.toCompactlyGenerated
  adj := adj

noncomputable instance instCreatesColimitsOfSizeCompactlyGeneratedToTop :
    CreatesColimitsOfSize.{w', v'} compactlyGeneratedToTop.{u, w} :=
  comonadicCreatesColimits _

instance {J : Type v'} [Category.{w'} J] [Small.{w} J] :
    HasLimitsOfShape J CompactlyGenerated.{u, w} :=
  hasLimitsOfShape_of_coreflective compactlyGeneratedToTop

instance {J : Type v'} [Category.{w'} J] [Small.{w} J] :
    HasColimitsOfShape J CompactlyGenerated.{u, w} :=
  hasColimitsOfShape_of_coreflective compactlyGeneratedToTop

instance [UnivLE.{v', w}] : HasLimitsOfSize.{w', v'} CompactlyGenerated.{u, w} :=
  hasLimits_of_coreflective compactlyGeneratedToTop

instance [UnivLE.{v', w}] : HasColimitsOfSize.{w', v'} CompactlyGenerated.{u, w} :=
  hasColimits_of_coreflective compactlyGeneratedToTop

/-- The underlying continuous map of the categorical counit is the generated-topology counit. -/
theorem adjCounit_app_hom (X : TopCat.{w}) :
    (adjCounit.{u, w}.app X).hom =
      WithGeneratedByTopology.counit (fun K : CompHaus.{u} ↦ K) X :=
  GeneratedByTopCat.adjCounit_app_hom (fun K : CompHaus.{u} ↦ K) X

/-- The compact-generation counit at `X` is an isomorphism in `TopCat` if and only if `X` is
`u`-compactly generated. -/
theorem isIso_adjCounit_app_iff (X : TopCat.{w}) :
    IsIso (adjCounit.{u, w}.app X) ↔ UCompactlyGeneratedSpace.{u} X :=
  (GeneratedByTopCat.isIso_adjCounit_app_iff (fun K : CompHaus.{u} ↦ K) X).trans
    (Topology.isGeneratedBy_compHaus_iff X)

/-- On a space already `u`-compactly generated, the counit is an isomorphism in `TopCat`. -/
instance instIsIsoAdjCounitApp (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    IsIso (adjCounit.{u, w}.app X) :=
  (isIso_adjCounit_app_iff X).2 inferInstance

instance (X : TopCat.{w}) [UCompactlyGeneratedSpace.{u} X] :
    IsIso (adj.{u, w}.counit.app X) := by
  rw [adj_counit]
  infer_instance

instance (X : TopCat.{w}) :
    IsIso (TopCat.toCompactlyGenerated.{u, w}.map (adjCounit.{u, w}.app X)) := by
  rw [← adj_counit]
  infer_instance

end CompactlyGenerated
