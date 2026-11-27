/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.ULift
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.Basic
import TauCeti.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

/-!
# Fundamental groupoid of the nerve of a category

Every category `C` maps canonically to the simplicial fundamental groupoid
`SSet.FundamentalGroupoid (nerve C)` via `CategoryTheory.nerve.toFundamentalGroupoid`, sending each
object `X` to `SSet.FundamentalGroupoid.mk (nerveEquiv.symm X)` and each morphism `f : X ⟶ Y` to
`SSet.FundamentalGroupoid.homMk (nerve.edgeMk f)`. This construction is compatible up to natural
isomorphism with `nerveMap` (`CategoryTheory.nerve.toFundamentalGroupoidNatIso`) and with universe
lifting via `AsSmall.up` and `CategoryTheory.nerve.asSmallIso`
(`CategoryTheory.nerve.toFundamentalGroupoidAsSmallIso`).

## Main declarations

* `CategoryTheory.nerve.toFundamentalGroupoid`: canonical functor
  `C ⥤ SSet.FundamentalGroupoid (nerve C)`.
* `CategoryTheory.nerve.toFundamentalGroupoidNatIso`: naturality with respect to `nerveMap F`.
* `CategoryTheory.nerve.toFundamentalGroupoidAsSmallIso`: compatibility with `AsSmall.up`,
  `SSet.uliftFundamentalGroupoid`, and `CategoryTheory.nerve.asSmallIso`.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section I.7.
-/

public section

open CategoryTheory Opposite Simplicial

namespace CategoryTheory.nerve

universe w v u

variable {C : Type u} [Category.{v} C]

-- `@[expose]` is required by `module` so dependent morphism equalities over
-- `(toFundamentalGroupoid C).obj` typecheck in downstream public statements.
/-- The canonical functor `C ⥤ SSet.FundamentalGroupoid (nerve C)` sending `X` to
`.mk (nerveEquiv.symm X)` and `f : X ⟶ Y` to `SSet.FundamentalGroupoid.homMk (edgeMk f)`. -/
@[expose, implicit_reducible, simps]
def toFundamentalGroupoid (C : Type u) [Category.{v} C] :
    C ⥤ SSet.FundamentalGroupoid (nerve C) where
  obj X := .mk (nerveEquiv.symm X)
  map f := SSet.FundamentalGroupoid.homMk (edgeMk f)
  map_id X := (congrArg SSet.FundamentalGroupoid.homMk (edgeMk_id X)).trans
    (SSet.FundamentalGroupoid.homMk_id _)
  map_comp f g := ((nonempty_compStruct_iff f g (f ≫ g)).2 rfl).some.homMk_comp.symm

/-- Object equality underlying `toFundamentalGroupoidNatIso F`. -/
lemma toFundamentalGroupoidNatIso_obj {D : Type u} [Category.{v} D] (F : C ⥤ D) (X : C) :
    (F ⋙ toFundamentalGroupoid D).obj X =
      (toFundamentalGroupoid C ⋙ SSet.mapFundamentalGroupoid (nerveMap F)).obj X :=
  congrArg (SSet.FundamentalGroupoid.mk (X := nerve D)) (nerveMap_app_mk₀ F X).symm

/-- Naturality isomorphism comparing `nerve.toFundamentalGroupoid` along `F : C ⥤ D` with
`SSet.mapFundamentalGroupoid (nerveMap F)`. -/
def toFundamentalGroupoidNatIso {D : Type u} [Category.{v} D] (F : C ⥤ D) :
    F ⋙ toFundamentalGroupoid D ≅
      toFundamentalGroupoid C ⋙ SSet.mapFundamentalGroupoid (nerveMap F) :=
  NatIso.ofComponents (fun X ↦ eqToIso (toFundamentalGroupoidNatIso_obj F X))
    fun f ↦
      (SSet.FundamentalGroupoid.homMk_comp_eqToHom (edgeMk (F.map f)) ((edgeMk f).map (nerveMap F))
        (nerveMap_app_mk₁ F f).symm).trans
        (congrArg (eqToHom _ ≫ ·)
          (SSet.mapFundamentalGroupoid_map_homMk (nerveMap F) (edgeMk f)).symm)

@[simp] lemma toFundamentalGroupoidNatIso_hom_app {D : Type u} [Category.{v} D] (F : C ⥤ D)
    (X : C) :
    (toFundamentalGroupoidNatIso F).hom.app X = eqToHom (toFundamentalGroupoidNatIso_obj F X) :=
  (rfl)

@[simp] lemma toFundamentalGroupoidNatIso_inv_app {D : Type u} [Category.{v} D] (F : C ⥤ D)
    (X : C) :
    (toFundamentalGroupoidNatIso F).inv.app X =
      eqToHom (toFundamentalGroupoidNatIso_obj F X).symm :=
  (rfl)

/-- Object equality underlying `toFundamentalGroupoidAsSmallIso C`. -/
lemma toFundamentalGroupoidAsSmallIso_obj (C : Type u) [Category.{v} C] (X : C) :
    ((AsSmall.up : C ⥤ AsSmall.{w} C) ⋙ toFundamentalGroupoid (AsSmall.{w} C)).obj X =
      (toFundamentalGroupoid C ⋙ SSet.uliftFundamentalGroupoid.{w} (nerve C) ⋙
        SSet.mapFundamentalGroupoid (asSmallIso.{w} C).inv).obj X :=
  congrArg (SSet.FundamentalGroupoid.mk (X := nerve (AsSmall.{w} C)))
    (asSmallIso_inv_app_ulift_nerveEquiv_symm.{w} C X).symm

private lemma edgeMk_asSmallUp_edge {X Y : C} (f : X ⟶ Y) :
    (edgeMk ((AsSmall.up : C ⥤ AsSmall.{w} C).map f)).edge =
      ((edgeMk f).ulift.{w}.map (asSmallIso.{w} C).inv).edge := by
  have he : (edgeMk f).ulift.{w}.edge =
      (nerve C).uliftFunctorObjEquiv (op ⦋1⦌) (objEquiv.symm (ComposableArrows.mk₁ f)) :=
    (SSet.Edge.ulift_edge (edgeMk f)).trans
      (congrArg ((nerve C).uliftFunctorObjEquiv (op ⦋1⦌))
        ((edgeMk_edge f).trans (objEquiv_symm_eq _).symm))
  rw [SSet.Edge.map_edge, he, asSmallIso_inv_app, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply, Functor.mapComposableArrows_obj_mk₁, objEquiv_symm_eq,
    edgeMk_edge]

/-- Compatibility isomorphism comparing `nerve.toFundamentalGroupoid` along `AsSmall.up` with
`SSet.uliftFundamentalGroupoid` and `SSet.mapFundamentalGroupoid (asSmallIso C).inv`. -/
def toFundamentalGroupoidAsSmallIso (C : Type u) [Category.{v} C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C) ⋙ toFundamentalGroupoid (AsSmall.{w} C) ≅
      toFundamentalGroupoid C ⋙ SSet.uliftFundamentalGroupoid.{w} (nerve C) ⋙
        SSet.mapFundamentalGroupoid (asSmallIso.{w} C).inv :=
  NatIso.ofComponents (fun X ↦ eqToIso (toFundamentalGroupoidAsSmallIso_obj.{w} C X))
    fun f ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map, toFundamentalGroupoid_map, eqToIso.hom]
      rw [SSet.FundamentalGroupoid.homMk_comp_eqToHom
        (edgeMk ((AsSmall.up : C ⥤ AsSmall.{w} C).map f))
        ((edgeMk f).ulift.map (asSmallIso.{w} C).inv) (edgeMk_asSmallUp_edge f),
        ← SSet.mapFundamentalGroupoid_map_homMk (asSmallIso.{w} C).inv (edgeMk f).ulift,
        ← SSet.uliftFundamentalGroupoid_map_homMk (nerve C) (edgeMk f)]

@[simp] lemma toFundamentalGroupoidAsSmallIso_hom_app (C : Type u) [Category.{v} C] (X : C) :
    (toFundamentalGroupoidAsSmallIso.{w} C).hom.app X =
      eqToHom (toFundamentalGroupoidAsSmallIso_obj.{w} C X) := (rfl)

@[simp] lemma toFundamentalGroupoidAsSmallIso_inv_app (C : Type u) [Category.{v} C] (X : C) :
    (toFundamentalGroupoidAsSmallIso.{w} C).inv.app X =
      eqToHom (toFundamentalGroupoidAsSmallIso_obj.{w} C X).symm := (rfl)

end CategoryTheory.nerve
