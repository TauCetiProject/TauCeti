/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.HomGroupoid
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# The sheaves of fibre morphisms of band-preserving transformations

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` carry `A`-bandings `bF`, `bG`, let `G` be a prestack for a
Grothendieck topology `J`, and fix objects `x` of the fibre of `F` and `y` of the fibre of `G`
over `U`. For a band-preserving transformation `X : F ⟶ G`, the sheaf `H_X` on `(Over U, J.over U)`
of local morphisms from `y` to `X_U x` is Mathlib's `G.sheafHom J y (X_U x)`. An arrow
`m : X ⟶ Y` of `BandedMorphism.HomCategory bF bG` acts on these sheaves by postcomposition with the
pullback of its component `m_U x`, and this makes `X ↦ H_X` a functor
`BandedMorphism.fiberHomSheafFunctor` from band-preserving transformations to sheaves of types
(Olsson, Remark 31.5; Groechenig, Wyss and Ziegler, §2.2.1). It is the composite of the
evaluation functor `BandedMorphism.componentFunctor bF bG U x : X ↦ X_U x` with Mathlib's sheaf of
morphisms out of `y`, made functorial in its target by `Pseudofunctor.sheafHomFunctor`.

When the fibres of `G` are groupoids, every arrow of `HomCategory` is invertible, so it acts by an
isomorphism of sheaves (`BandedMorphism.fiberHomSheafMapIso`). The sections of `H_X` over
`t : T ⟶ U` are then isomorphisms `G(t) y ≅ G(t) (X_U x)` by Mathlib's `Groupoid.isoEquivHom`, and
when `G` is a gerbe they exist locally over every `t : T ⟶ U`, by
`Pseudofunctor.coversTop_presheafHom` applied to `IsGerbe.exists_covering_hom`, though possibly
with no global section.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `fiberHomSheafFunctor bF bG J U x y`: `X ↦ G.sheafHom J y (X_U x)`, with
  `fiberHomSheafFunctor_obj`, `fiberHomSheafFunctor_obj_obj`, `fiberHomSheafFunctor_map_hom_app`.
* `fiberHomSheafMapIso`, with `fiberHomSheafMapIso_hom` and `fiberHomSheafMapIso_inv`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Remark 31.5
* [Michael Groechenig, Dimitri Wyss and Paul Ziegler](https://link.springer.com/content/pdf/10.1007/s00222-020-00957-8.pdf),
  §2.2.1
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.BandedMorphism

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat.{w}} {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}

variable (bF bG) in
/-- **The sheaf of fibre morphisms**, as a functor of the band-preserving transformation: for a
prestack `G`, the functor sending `X` to the sheaf `G.sheafHom J y (X_U x)` of local morphisms
from `y` to `X_U x` on `(Over U, J.over U)`, an arrow `m : X ⟶ Y` acting by postcomposition with
the pullback of `m_U x`. -/
noncomputable abbrev fiberHomSheafFunctor (J : GrothendieckTopology C) [G.IsPrestack J] (U : C)
    (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U))) :
    HomCategory bF bG ⥤ Sheaf (J.over U) (Type v') :=
  componentFunctor bF bG U x ⋙ G.sheafHomFunctor J y

variable [G.IsPrestack J] {U : C} (x : F.obj (.mk (op U))) (y : G.obj (.mk (op U)))

/-- The sheaf assigned to `X` is Mathlib's sheaf of morphisms from `y` to `X_U x`. -/
theorem fiberHomSheafFunctor_obj (X : HomCategory bF bG) :
    (fiberHomSheafFunctor bF bG J U x y).obj X =
      G.sheafHom J y ((X.obj.app (.mk (op U))).toFunctor.obj x) :=
  (rfl)

/-- The underlying presheaf of the sheaf assigned to `X` is Mathlib's presheaf of morphisms from
`y` to `X_U x`. -/
theorem fiberHomSheafFunctor_obj_obj (X : HomCategory bF bG) :
    ((fiberHomSheafFunctor bF bG J U x y).obj X).obj =
      G.presheafHom y ((X.obj.app (.mk (op U))).toFunctor.obj x) :=
  (rfl)

/-- An arrow `m : X ⟶ Y` sends a local morphism `p` over `t : T ⟶ U` to `p` followed by the
pullback of `m_U x` along `t`. -/
theorem fiberHomSheafFunctor_map_hom_app {X Y : HomCategory bF bG} (m : X ⟶ Y)
    (T : (Over U)ᵒᵖ) (p : (G.presheafHom y ((X.obj.app (.mk (op U))).toFunctor.obj x)).obj T) :
    ((fiberHomSheafFunctor bF bG J U x y).map m).hom.app T p =
      p ≫ (G.map T.unop.hom.op.toLoc).toFunctor.map
        ((m.hom.as.app (.mk (op U))).toNatTrans.app x) :=
  G.presheafHomPostcomp_app_apply y _ T p

variable [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]

/-- **An arrow of band-preserving transformations acts by an isomorphism of fibre morphism
sheaves**: the image of `homIso m` under `fiberHomSheafFunctor`. -/
noncomputable def fiberHomSheafMapIso {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (fiberHomSheafFunctor bF bG J U x y).obj X ≅ (fiberHomSheafFunctor bF bG J U x y).obj Y :=
  (fiberHomSheafFunctor bF bG J U x y).mapIso (homIso m)

@[simp]
theorem fiberHomSheafMapIso_hom {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (fiberHomSheafMapIso x y m).hom = (fiberHomSheafFunctor bF bG J U x y).map m := by
  rw [fiberHomSheafMapIso, Functor.mapIso_hom, homIso_hom]

/-- The inverse of `fiberHomSheafMapIso m` is the action of the inverse arrow `(homIso m).inv`. -/
@[simp]
theorem fiberHomSheafMapIso_inv {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (fiberHomSheafMapIso x y m).inv =
      (fiberHomSheafFunctor bF bG J U x y).map (homIso m).inv :=
  (rfl)

end CategoryTheory.Pseudofunctor.BandedMorphism
