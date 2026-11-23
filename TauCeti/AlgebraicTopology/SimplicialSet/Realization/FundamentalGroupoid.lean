/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.ULift
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Edge
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Fundamental groupoid functor for geometric realization

By `SSet.FundamentalGroupoid.desc`, edge paths (`SSet.Edge.toTopPath`) and their composition
homotopies (`SSet.Edge.CompStruct.toTopPath_trans_homotopic`) assemble into
`SSet.toTopFundamentalGroupoid X : SSet.FundamentalGroupoid X ⥤ _root_.FundamentalGroupoid |X|`,
compatible up to natural isomorphism with simplicial maps (`SSet.mapFundamentalGroupoidToTopIso`)
and universe lifting (`SSet.Edge.toTopPath_ulift`, `SSet.uliftFundamentalGroupoidToTopIso`).

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section III.1.
-/

public section

open CategoryTheory Opposite Simplicial Convexity

universe v u

namespace SSet

section EdgePath

variable {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}

/-- Lifting an edge `e` along `uliftFunctor` pushes `e.toTopPath` forward along
`toTopUliftHomeomorph X`. -/
lemma Edge.toTopPath_ulift (e : X.Edge x₀ x₁) :
    e.ulift.{v}.toTopPath =
      (e.toTopPath.map (toTopUliftHomeomorph.{v, u} X).continuous).cast
        (toTopUliftHomeomorph_toTopPoint.{v, u} x₀).symm
        (toTopUliftHomeomorph_toTopPoint.{v, u} x₁).symm := by
  ext t; simp [Edge.ulift_edge]

end EdgePath

section FundamentalGroupoid

-- `@[expose]` is required by `module` so dependent morphism equalities over
-- `(toTopFundamentalGroupoid X).obj` typecheck in downstream public statements.
/-- The canonical functor `SSet.FundamentalGroupoid X ⥤ _root_.FundamentalGroupoid |X|` sending
`.mk x` to `.mk (toTopPoint x)` and `homMk e` to `FundamentalGroupoid.fromPath (.mk e.toTopPath)`.
-/
@[expose, implicit_reducible]
noncomputable def toTopFundamentalGroupoid (X : SSet.{u}) :
    SSet.FundamentalGroupoid X ⥤ _root_.FundamentalGroupoid |X| :=
  FundamentalGroupoid.desc (fun x ↦ .mk (toTopPoint x))
    (fun e ↦ _root_.FundamentalGroupoid.fromPath (.mk e.toTopPath))
    (fun h ↦ Quotient.sound h.toTopPath_trans_homotopic)

@[simp]
lemma toTopFundamentalGroupoid_obj_mk (X : SSet.{u}) (x : X _⦋0⦌) :
    (toTopFundamentalGroupoid X).obj (.mk x) = .mk (toTopPoint x) := (rfl)

@[simp]
lemma toTopFundamentalGroupoid_map_homMk (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (toTopFundamentalGroupoid X).map (FundamentalGroupoid.homMk e) =
      _root_.FundamentalGroupoid.fromPath (.mk e.toTopPath) :=
  FundamentalGroupoid.desc_map_homMk _ _ (fun h ↦ Quotient.sound h.toTopPath_trans_homotopic) e

private lemma mapFundamentalGroupoid_toTop_obj {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (mapFundamentalGroupoid f ⋙ toTopFundamentalGroupoid Y).obj (.mk x) =
      (toTopFundamentalGroupoid X ⋙ _root_.FundamentalGroupoid.map (toTop.map f).hom).obj (.mk x) :=
  _root_.FundamentalGroupoid.ext (toTop_map_toTopPoint f x).symm

/-- Naturality isomorphism comparing `toTopFundamentalGroupoid` along `f : X ⟶ Y` with the
topological fundamental groupoid functor induced by `toTop.map f`. -/
noncomputable def mapFundamentalGroupoidToTopIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    mapFundamentalGroupoid f ⋙ toTopFundamentalGroupoid Y ≅
      toTopFundamentalGroupoid X ⋙ _root_.FundamentalGroupoid.map (toTop.map f).hom :=
  FundamentalGroupoid.natIsoMk (fun x ↦ eqToIso (mapFundamentalGroupoid_toTop_obj f x))
    fun e ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [mapFundamentalGroupoid_map_homMk, toTopFundamentalGroupoid_map_homMk,
        toTopFundamentalGroupoid_map_homMk]
      exact _root_.FundamentalGroupoid.fromPath_naturality_eqToHom (φ := (toTop.map f).hom)
        (toTop_map_toTopPoint f _) (toTop_map_toTopPoint f _)
        e.toTopPath (e.map f).toTopPath (by ext t; simp [Edge.map_edge])

@[simp] lemma mapFundamentalGroupoidToTopIso_hom_app {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : SSet.FundamentalGroupoid X) :
    (mapFundamentalGroupoidToTopIso f).hom.app x = eqToHom (by cases x; ext; simp) := by
  cases x; rfl

@[simp] lemma mapFundamentalGroupoidToTopIso_inv_app {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : SSet.FundamentalGroupoid X) :
    (mapFundamentalGroupoidToTopIso f).inv.app x = eqToHom (by cases x; ext; simp) := by
  cases x; rfl

private lemma uliftFundamentalGroupoid_toTop_obj (X : SSet.{u}) (x : X _⦋0⦌) :
    (uliftFundamentalGroupoid.{v} X ⋙ toTopFundamentalGroupoid (uliftFunctor.{v, u}.obj X)).obj
        (.mk x) =
      (toTopFundamentalGroupoid X ⋙
        _root_.FundamentalGroupoid.map (toTopUliftHomeomorph.{v, u} X : C(_, _))).obj (.mk x) :=
  _root_.FundamentalGroupoid.ext (toTopUliftHomeomorph_toTopPoint.{v, u} x).symm

/-- Compatibility isomorphism comparing `toTopFundamentalGroupoid` along `uliftFunctor` with the
topological fundamental groupoid functor induced by `toTopUliftHomeomorph X`. -/
noncomputable def uliftFundamentalGroupoidToTopIso (X : SSet.{u}) :
    uliftFundamentalGroupoid.{v} X ⋙ toTopFundamentalGroupoid (uliftFunctor.{v, u}.obj X) ≅
      toTopFundamentalGroupoid X ⋙
        _root_.FundamentalGroupoid.map (toTopUliftHomeomorph.{v, u} X : C(_, _)) :=
  FundamentalGroupoid.natIsoMk (fun x ↦ eqToIso (uliftFundamentalGroupoid_toTop_obj.{v} X x))
    fun e ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [uliftFundamentalGroupoid_map_homMk, toTopFundamentalGroupoid_map_homMk,
        toTopFundamentalGroupoid_map_homMk]
      exact _root_.FundamentalGroupoid.fromPath_naturality_eqToHom
        (φ := (toTopUliftHomeomorph.{v, u} X : C(_, _)))
        (toTopUliftHomeomorph_toTopPoint.{v, u} _) (toTopUliftHomeomorph_toTopPoint.{v, u} _)
        e.toTopPath e.ulift.{v}.toTopPath (e.toTopPath_ulift.{v})

@[simp] lemma uliftFundamentalGroupoidToTopIso_hom_app (X : SSet.{u})
    (x : SSet.FundamentalGroupoid X) :
    (uliftFundamentalGroupoidToTopIso.{v} X).hom.app x = eqToHom (by cases x; ext; simp) := by
  cases x; rfl

@[simp] lemma uliftFundamentalGroupoidToTopIso_inv_app (X : SSet.{u})
    (x : SSet.FundamentalGroupoid X) :
    (uliftFundamentalGroupoidToTopIso.{v} X).inv.app x = eqToHom (by cases x; ext; simp) := by
  cases x; rfl

end FundamentalGroupoid

end SSet
