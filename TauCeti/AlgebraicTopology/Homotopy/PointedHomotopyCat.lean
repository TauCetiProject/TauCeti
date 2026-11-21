/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Quotient
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.Topology.Category.BasedTopologicalSpace
public import TauCeti.Topology.Homotopy.Extension.Basic
public import TauCeti.Topology.Homotopy.Homotopic.Rel
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homotopy

import TauCeti.Topology.Homotopy.Extension.HomotopyEquivRel

/-!
# The pointed homotopy category

The pointed homotopy category `TauCeti.PointedHomotopyCat` has the based topological spaces as
objects, and as morphisms the pointed homotopy classes of base-point-preserving continuous maps:
two based maps are identified when they are homotopic relative to the base point of the source.
It is the quotient of the category `TauCeti.BasedTopologicalSpace` by the congruence
`TauCeti.BasedTopologicalSpace.homotopicRel`, built with Mathlib's `CategoryTheory.Quotient`, so a
functor into based spaces that is defined strictly descends to the pointed homotopy category by
composing with `TauCeti.PointedHomotopyCat.quotient`.

Pointed-homotopic maps induce the same homomorphism of fundamental groups, so the fundamental
group at the base point is a functor `TauCeti.PointedHomotopyCat.fundamentalGroupFunctor` on the
pointed homotopy category. It factors the fundamental-group functor
`TauCeti.BasedTopologicalSpace.fundamentalGroupFunctor` of based spaces through the quotient.

An isomorphism in `PointedHomotopyCat` is a pointed homotopy equivalence: mutually inverse based
maps whose composites are homotopic to the identities relative to the base points
(`TauCeti.PointedHomotopyCat.isIso_quotient_map_iff`, `TauCeti.PointedHomotopyCat.isoMk`,
`TauCeti.PointedHomotopyCat.exists_homotopyEquiv_of_iso`). Between well-pointed spaces — spaces
whose base points have the homotopy extension property — any based map whose underlying continuous
map is a homotopy equivalence becomes an isomorphism in `PointedHomotopyCat`
(`TauCeti.PointedHomotopyCat.isIso_quotient_map_of_homotopyEquiv`,
`TauCeti.PointedHomotopyCat.isoOfHomotopyEquiv`), by upgrading its unbased homotopy inverse via
`TauCeti.HasHomotopyExtensionProperty.exists_basedInverse_homotopicRel`.

## Main definitions

* `TauCeti.BasedTopologicalSpace.homotopicRel`: pointed homotopy, as a congruence on based maps.
* `TauCeti.PointedHomotopyCat`: the pointed homotopy category.
* `TauCeti.PointedHomotopyCat.quotient`: the quotient functor from based spaces.
* `TauCeti.PointedHomotopyCat.as`: the underlying based space of an object.
* `TauCeti.BasedTopologicalSpace.fundamentalGroupFunctor`: the fundamental group at the base
  point, as a functor on based spaces.
* `TauCeti.PointedHomotopyCat.fundamentalGroupFunctor`: the induced functor on the pointed
  homotopy category.
* `TauCeti.PointedHomotopyCat.isoMk`: constructs an isomorphism from mutually inverse based maps up
  to pointed homotopy.
* `TauCeti.PointedHomotopyCat.isoOfHomotopyEquiv`: the isomorphism induced by a based homotopy
  equivalence between well-pointed spaces.

## Main results

* `TauCeti.PointedHomotopyCat.quotient_map_eq_iff`: two based maps have the same class exactly
  when they are homotopic relative to the base point.
* `TauCeti.PointedHomotopyCat.quotient_comp_fundamentalGroupFunctor`: the fundamental group of
  based spaces factors through the pointed homotopy category.
* `TauCeti.PointedHomotopyCat.isIso_quotient_map_iff`: **characterization of isomorphisms in the
  pointed homotopy category** as pointed homotopy equivalences.
* `TauCeti.PointedHomotopyCat.isIso_quotient_map_of_homotopyEquiv`: a based map between
  well-pointed spaces that is an unbased homotopy equivalence is an isomorphism in the pointed
  homotopy category.
* `TauCeti.PointedHomotopyCat.exists_homotopyEquiv_of_iso`: every isomorphism is represented by a
  based homotopy equivalence with both composites homotopic to the identities relative to the base
  points.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (Proposition 0.19)
  and Section 1.1.
-/

public section

noncomputable section

universe u

open CategoryTheory

namespace TauCeti

namespace BasedTopologicalSpace

/-- **Pointed homotopy** of based maps: two morphisms `f g : X ⟶ Y` of based spaces are related
when their underlying continuous maps are homotopic relative to the base point of `X`. -/
def homotopicRel : HomRel BasedTopologicalSpace.{u} := fun X _ f g ↦
  f.toContinuousMap.HomotopicRel g.toContinuousMap {X.basepoint}

theorem homotopicRel_iff {X Y : BasedTopologicalSpace.{u}} {f g : X ⟶ Y} :
    homotopicRel f g ↔ f.toContinuousMap.HomotopicRel g.toContinuousMap {X.basepoint} :=
  Iff.rfl

instance : Congruence homotopicRel.{u} where
  equivalence := ⟨fun f ↦ .refl f.toContinuousMap, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  comp_left f g g' h := by
    simp only [homotopicRel_iff, comp_eq_hom_comp, Hom.toContinuousMap_comp]
    -- Precomposing with `f` gives a homotopy relative to `f ⁻¹' {basepoint}`, which contains the
    -- base point of the source.
    exact (h.precomp f.toContinuousMap).mono (by simp)
  comp_right g h := by
    simp only [homotopicRel_iff, comp_eq_hom_comp, Hom.toContinuousMap_comp]
    exact h.comp_continuousMap g.toContinuousMap

/-- **The fundamental group at the base point**, as a functor from based spaces to groups. A based
map induces `FundamentalGroup.mapOfEq` along its base-point equation. -/
@[expose] def fundamentalGroupFunctor : BasedTopologicalSpace.{u} ⥤ GrpCat.{u} where
  obj X := GrpCat.of (FundamentalGroup X.carrier X.basepoint)
  map f := GrpCat.ofHom (FundamentalGroup.mapOfEq f.toContinuousMap f.map_basepoint)
  map_id X := by
    refine GrpCat.hom_ext (MonoidHom.ext fun a ↦ ?_)
    rw [GrpCat.hom_ofHom, GrpCat.hom_id, MonoidHom.id_apply]
    exact (FundamentalGroup.mapOfEq_congr (Hom.toContinuousMap_id X) _ rfl a).trans
      (FundamentalGroup.mapOfEq_id rfl a)
  map_comp f g := by
    refine GrpCat.hom_ext (MonoidHom.ext fun a ↦ ?_)
    simp only [GrpCat.hom_comp, MonoidHom.comp_apply, GrpCat.hom_ofHom]
    exact (FundamentalGroup.mapOfEq_congr (Hom.toContinuousMap_comp g f) _ _ a).trans
      (FundamentalGroup.mapOfEq_comp _ _ _ _ a).symm

@[simp]
theorem fundamentalGroupFunctor_obj (X : BasedTopologicalSpace.{u}) :
    fundamentalGroupFunctor.obj X = GrpCat.of (FundamentalGroup X.carrier X.basepoint) :=
  (rfl)

@[simp]
theorem fundamentalGroupFunctor_map_hom {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) :
    (fundamentalGroupFunctor.map f).hom =
      FundamentalGroup.mapOfEq f.toContinuousMap f.map_basepoint :=
  (rfl)

/-- Pointed-homotopic based maps induce the same homomorphism of fundamental groups. -/
theorem fundamentalGroupFunctor_map_eq_of_homotopicRel {X Y : BasedTopologicalSpace.{u}}
    {f g : X ⟶ Y} (h : homotopicRel f g) :
    fundamentalGroupFunctor.map f = fundamentalGroupFunctor.map g :=
  GrpCat.hom_ext (FundamentalGroup.mapOfEq_eq_of_homotopicRel _ _ rfl h)

end BasedTopologicalSpace

/-- **The pointed homotopy category.** Its objects are the based topological spaces, and its
morphisms are the classes of based maps up to homotopy relative to the base point. -/
@[expose] def PointedHomotopyCat : Type (u + 1) :=
  CategoryTheory.Quotient BasedTopologicalSpace.homotopicRel.{u}

namespace PointedHomotopyCat

instance : Category PointedHomotopyCat.{u} :=
  inferInstanceAs (Category (CategoryTheory.Quotient BasedTopologicalSpace.homotopicRel.{u}))

/-- The functor sending a based space to itself and a based map to its pointed homotopy class. -/
@[expose] def quotient : BasedTopologicalSpace.{u} ⥤ PointedHomotopyCat.{u} :=
  CategoryTheory.Quotient.functor _

/-- The underlying based topological space of an object of `PointedHomotopyCat`. -/
-- Exposed so dependent types over `X.as` reduce to `X₀` on `quotient.obj X₀`.
@[expose] def as (X : PointedHomotopyCat.{u}) : BasedTopologicalSpace.{u} :=
  CategoryTheory.Quotient.as X

@[simp]
theorem as_quotient_obj (X : BasedTopologicalSpace.{u}) : (quotient.obj X).as = X :=
  (rfl)

@[simp]
theorem quotient_obj_as (X : PointedHomotopyCat.{u}) : quotient.obj X.as = X :=
  (rfl)

instance : quotient.{u}.Full :=
  inferInstanceAs (CategoryTheory.Quotient.functor _).Full

instance : quotient.{u}.EssSurj :=
  inferInstanceAs (CategoryTheory.Quotient.functor _).EssSurj

/-- **Two based maps have the same pointed homotopy class exactly when they are homotopic
relative to the base point.** -/
theorem quotient_map_eq_iff {X Y : BasedTopologicalSpace.{u}} (f g : X ⟶ Y) :
    quotient.map f = quotient.map g ↔
      f.toContinuousMap.HomotopicRel g.toContinuousMap {X.basepoint} :=
  CategoryTheory.Quotient.functor_map_eq_iff _ f g

/-- **The fundamental group on the pointed homotopy category**, induced by the fundamental group of
based spaces: pointed-homotopic maps induce the same homomorphism. -/
@[expose] def fundamentalGroupFunctor : PointedHomotopyCat.{u} ⥤ GrpCat.{u} :=
  CategoryTheory.Quotient.lift _ BasedTopologicalSpace.fundamentalGroupFunctor
    fun _ _ _ _ h ↦ BasedTopologicalSpace.fundamentalGroupFunctor_map_eq_of_homotopicRel h

/-- The fundamental group of based spaces factors through the pointed homotopy category. -/
theorem quotient_comp_fundamentalGroupFunctor :
    quotient.{u} ⋙ fundamentalGroupFunctor = BasedTopologicalSpace.fundamentalGroupFunctor :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp]
theorem fundamentalGroupFunctor_obj_quotient_obj (X : BasedTopologicalSpace.{u}) :
    fundamentalGroupFunctor.obj (quotient.obj X) =
      GrpCat.of (FundamentalGroup X.carrier X.basepoint) :=
  (rfl)

@[simp]
theorem fundamentalGroupFunctor_map_quotient_map {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) :
    fundamentalGroupFunctor.map (quotient.map f) =
      BasedTopologicalSpace.fundamentalGroupFunctor.map f :=
  (rfl)

open scoped ContinuousMap

/-- Construct an isomorphism in `PointedHomotopyCat` from mutually inverse based maps up to
pointed homotopy. -/
def isoMk {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hgf : (g.toContinuousMap.comp f.toContinuousMap).HomotopicRel
      (ContinuousMap.id X.carrier) {X.basepoint})
    (hfg : (f.toContinuousMap.comp g.toContinuousMap).HomotopicRel
      (ContinuousMap.id Y.carrier) {Y.basepoint}) :
    quotient.obj X ≅ quotient.obj Y where
  hom := quotient.map f
  inv := quotient.map g
  hom_inv_id := by
    rw [← quotient.map_comp, ← quotient.map_id]
    exact (quotient_map_eq_iff (f ≫ g) (𝟙 X)).2 <| by
      simpa only [BasedTopologicalSpace.comp_eq_hom_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_id] using hgf
  inv_hom_id := by
    rw [← quotient.map_comp, ← quotient.map_id]
    exact (quotient_map_eq_iff (g ≫ f) (𝟙 Y)).2 <| by
      simpa only [BasedTopologicalSpace.comp_eq_hom_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_id] using hfg

@[simp]
theorem isoMk_hom {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hgf : (g.toContinuousMap.comp f.toContinuousMap).HomotopicRel
      (ContinuousMap.id X.carrier) {X.basepoint})
    (hfg : (f.toContinuousMap.comp g.toContinuousMap).HomotopicRel
      (ContinuousMap.id Y.carrier) {Y.basepoint}) :
    (isoMk f g hgf hfg).hom = quotient.map f :=
  (rfl)

@[simp]
theorem isoMk_inv {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ X)
    (hgf : (g.toContinuousMap.comp f.toContinuousMap).HomotopicRel
      (ContinuousMap.id X.carrier) {X.basepoint})
    (hfg : (f.toContinuousMap.comp g.toContinuousMap).HomotopicRel
      (ContinuousMap.id Y.carrier) {Y.basepoint}) :
    (isoMk f g hgf hfg).inv = quotient.map g :=
  (rfl)

/-- **Isomorphisms in the pointed homotopy category are pointed homotopy equivalences.**
A based map `f : X ⟶ Y` becomes an isomorphism in `PointedHomotopyCat` exactly when it has a
based map `g : Y ⟶ X` with both composites homotopic to the identities relative to the base
points. -/
theorem isIso_quotient_map_iff {X Y : BasedTopologicalSpace.{u}} (f : X ⟶ Y) :
    IsIso (quotient.map f) ↔
      ∃ g : Y ⟶ X,
        (g.toContinuousMap.comp f.toContinuousMap).HomotopicRel
          (ContinuousMap.id X.carrier) {X.basepoint} ∧
        (f.toContinuousMap.comp g.toContinuousMap).HomotopicRel
          (ContinuousMap.id Y.carrier) {Y.basepoint} := by
  constructor
  · intro _
    obtain ⟨g, hg⟩ := quotient.map_surjective (inv (quotient.map f))
    refine ⟨g, ?_, ?_⟩
    · have h : quotient.map (f ≫ g) = quotient.map (𝟙 X) := by
        rw [quotient.map_comp, hg, IsIso.hom_inv_id, quotient.map_id]
      simpa only [BasedTopologicalSpace.comp_eq_hom_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_id] using (quotient_map_eq_iff _ _).1 h
    · have h : quotient.map (g ≫ f) = quotient.map (𝟙 Y) := by
        rw [quotient.map_comp, hg, IsIso.inv_hom_id, quotient.map_id]
      simpa only [BasedTopologicalSpace.comp_eq_hom_comp, BasedTopologicalSpace.id_eq_hom_id,
        BasedTopologicalSpace.Hom.toContinuousMap_comp,
        BasedTopologicalSpace.Hom.toContinuousMap_id] using (quotient_map_eq_iff _ _).1 h
  · rintro ⟨g, hgf, hfg⟩
    exact (isoMk f g hgf hfg).isIso_hom

/-- **Between well-pointed spaces, a based homotopy equivalence is an isomorphism in the pointed
homotopy category.** If both base points have the homotopy extension property and `f : X ⟶ Y` is
the underlying continuous map of a homotopy equivalence `h : X.carrier ≃ₕ Y.carrier`, then
`quotient.map f` is an isomorphism. -/
theorem isIso_quotient_map_of_homotopyEquiv {X Y : BasedTopologicalSpace.{u}}
    (hx : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    {f : X ⟶ Y} (h : X.carrier ≃ₕ Y.carrier) (hf : f.toContinuousMap = h.toFun) :
    IsIso (quotient.map f) := by
  have hh : h X.basepoint = Y.basepoint :=
    (DFunLike.congr_fun hf.symm X.basepoint).trans f.map_basepoint
  obtain ⟨g, hg, hgf, hfg⟩ := hx.exists_basedInverse_homotopicRel hy h hh
  exact (isIso_quotient_map_iff f).2 ⟨⟨g, hg⟩, hf ▸ hgf, hf ▸ hfg⟩

/-- The isomorphism in `PointedHomotopyCat` induced by a based map `f : X ⟶ Y` between
well-pointed spaces whose underlying continuous map is a homotopy equivalence. -/
def isoOfHomotopyEquiv {X Y : BasedTopologicalSpace.{u}}
    (hx : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (f : X ⟶ Y) (h : X.carrier ≃ₕ Y.carrier) (hf : f.toContinuousMap = h.toFun) :
    quotient.obj X ≅ quotient.obj Y :=
  haveI : IsIso (quotient.map f) := isIso_quotient_map_of_homotopyEquiv hx hy h hf
  asIso (quotient.map f)

@[simp]
theorem isoOfHomotopyEquiv_hom {X Y : BasedTopologicalSpace.{u}}
    (hx : HasHomotopyExtensionProperty ({X.basepoint} : Set X.carrier))
    (hy : HasHomotopyExtensionProperty ({Y.basepoint} : Set Y.carrier))
    (f : X ⟶ Y) (h : X.carrier ≃ₕ Y.carrier) (hf : f.toContinuousMap = h.toFun) :
    (isoOfHomotopyEquiv hx hy f h hf).hom = quotient.map f :=
  (rfl)

/-- Every isomorphism `e : quotient.obj X ≅ quotient.obj Y` in `PointedHomotopyCat` is represented
by a homotopy equivalence `F : X.carrier ≃ₕ Y.carrier` whose forward and inverse maps preserve
base points, with both composites homotopic to the identities relative to the base points. -/
theorem exists_homotopyEquiv_of_iso {X Y : BasedTopologicalSpace.{u}}
    (e : quotient.obj X ≅ quotient.obj Y) :
    ∃ (F : X.carrier ≃ₕ Y.carrier)
      (hF : F.toFun X.basepoint = Y.basepoint) (hFinv : F.invFun Y.basepoint = X.basepoint),
      quotient.map ⟨F.toFun, hF⟩ = e.hom ∧
      quotient.map ⟨F.invFun, hFinv⟩ = e.inv ∧
      (F.invFun.comp F.toFun).HomotopicRel (ContinuousMap.id X.carrier) {X.basepoint} ∧
      (F.toFun.comp F.invFun).HomotopicRel (ContinuousMap.id Y.carrier) {Y.basepoint} := by
  obtain ⟨f, hf⟩ := quotient.map_surjective e.hom
  obtain ⟨g, hg⟩ := quotient.map_surjective e.inv
  have hgf : (g.toContinuousMap.comp f.toContinuousMap).HomotopicRel
      (ContinuousMap.id X.carrier) {X.basepoint} := by
    have h : quotient.map (f ≫ g) = quotient.map (𝟙 X) := by
      rw [quotient.map_comp, hf, hg, e.hom_inv_id, quotient.map_id]
    simpa only [BasedTopologicalSpace.comp_eq_hom_comp, BasedTopologicalSpace.id_eq_hom_id,
      BasedTopologicalSpace.Hom.toContinuousMap_comp,
      BasedTopologicalSpace.Hom.toContinuousMap_id] using (quotient_map_eq_iff _ _).1 h
  have hfg : (f.toContinuousMap.comp g.toContinuousMap).HomotopicRel
      (ContinuousMap.id Y.carrier) {Y.basepoint} := by
    have h : quotient.map (g ≫ f) = quotient.map (𝟙 Y) := by
      rw [quotient.map_comp, hg, hf, e.inv_hom_id, quotient.map_id]
    simpa only [BasedTopologicalSpace.comp_eq_hom_comp, BasedTopologicalSpace.id_eq_hom_id,
      BasedTopologicalSpace.Hom.toContinuousMap_comp,
      BasedTopologicalSpace.Hom.toContinuousMap_id] using (quotient_map_eq_iff _ _).1 h
  exact ⟨⟨f.toContinuousMap, g.toContinuousMap, hgf.homotopic, hfg.homotopic⟩,
    f.map_basepoint, g.map_basepoint, hf, hg, hgf, hfg⟩

end PointedHomotopyCat

end TauCeti
