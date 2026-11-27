/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.HomGroupoid
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
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
evaluation functor `BandedMorphism.componentFunctor U x : X ↦ X_U x` with Mathlib's sheaf of
morphisms out of `y`, made functorial in its target by `Pseudofunctor.sheafHomFunctor`.

When the fibres of `G` are groupoids, every arrow of `HomCategory` is invertible, so it acts by an
isomorphism of sheaves (`BandedMorphism.fiberHomSheafMapIso`), and the sections of `H_X` over
`t : T ⟶ U` are isomorphisms `G(t) y ≅ G(t) (X_U x)` (`BandedMorphism.fiberHomSectionIsoEquiv`).
When `G` is a gerbe, `H_X` has sections locally over every `t : T ⟶ U`
(`BandedMorphism.fiberHomSheaf_locallyNonempty`), though possibly no global section.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.BandedMorphism`:

* `componentFunctor U x`: evaluation `X ↦ X_U x` of band-preserving transformations, with
  `componentFunctor_map_eq_componentIso_hom`.
* `fiberHomSheafFunctor J U x y`: `X ↦ G.sheafHom J y (X_U x)`, with
  `fiberHomSheafFunctor_obj`, `fiberHomSheafFunctor_obj_obj`, `fiberHomSheafFunctor_map_hom_app`.
* `fiberHomSheafMapIso`, with `fiberHomSheafMapIso_hom` and `fiberHomSheafMapIso_inv`.
* `fiberHomSectionIsoEquiv`, with `fiberHomSectionIsoEquiv_hom` and
  `fiberHomSectionIsoEquiv_symm_apply`.
* `fiberHomSheaf_locallyNonempty`.

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
/-- **Evaluation at `x`**: the functor from band-preserving transformations to the fibre of `G`
over `U` sending `X` to `X_U x` and an arrow `m` to its component `m_U x`. -/
@[expose, simps]
def componentFunctor (U : C) (x : F.obj (.mk (op U))) :
    HomCategory bF bG ⥤ G.obj (.mk (op U)) where
  obj X := (X.obj.app (.mk (op U))).toFunctor.obj x
  map m := (m.hom.as.app (.mk (op U))).toNatTrans.app x
  map_id _ := rfl
  map_comp _ _ := rfl

/-- On arrows, evaluation at `x` is the forward arrow of the component isomorphism. -/
theorem componentFunctor_map_eq_componentIso_hom [∀ U : C, IsGroupoid (G.obj (.mk (op U)))]
    (U : C) (x : F.obj (.mk (op U))) {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (componentFunctor bF bG U x).map m = (componentIso m U x).hom :=
  (componentIso_hom m U x).symm

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
  (rfl)

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
theorem fiberHomSheafMapIso_inv {X Y : HomCategory bF bG} (m : X ⟶ Y) :
    (fiberHomSheafMapIso x y m).inv =
      (fiberHomSheafFunctor bF bG J U x y).map (homIso m).inv :=
  (rfl)

omit [G.IsPrestack J] in
/-- **Sections of the fibre morphism sheaf are isomorphisms**: when the fibres of `G` are
groupoids, a local morphism `G(t) y ⟶ G(t) (X_U x)` over `t : T ⟶ U` is the same as an isomorphism
`G(t) y ≅ G(t) (X_U x)`. -/
noncomputable def fiberHomSectionIsoEquiv (X : HomCategory bF bG) (T : (Over U)ᵒᵖ) :
    (G.presheafHom y ((X.obj.app (.mk (op U))).toFunctor.obj x)).obj T ≃
      ((G.map T.unop.hom.op.toLoc).toFunctor.obj y ≅
        (G.map T.unop.hom.op.toLoc).toFunctor.obj ((X.obj.app (.mk (op U))).toFunctor.obj x)) where
  toFun p := asIso p
  invFun q := q.hom
  left_inv _ := rfl
  right_inv _ := Iso.ext rfl

omit [G.IsPrestack J] in
theorem fiberHomSectionIsoEquiv_hom (X : HomCategory bF bG) (T : (Over U)ᵒᵖ)
    (p : (G.presheafHom y ((X.obj.app (.mk (op U))).toFunctor.obj x)).obj T) :
    (fiberHomSectionIsoEquiv x y X T p).hom = p :=
  (rfl)

omit [G.IsPrestack J] in
theorem fiberHomSectionIsoEquiv_symm_apply (X : HomCategory bF bG) (T : (Over U)ᵒᵖ)
    (q : (G.map T.unop.hom.op.toLoc).toFunctor.obj y ≅
      (G.map T.unop.hom.op.toLoc).toFunctor.obj ((X.obj.app (.mk (op U))).toFunctor.obj x)) :
    (fiberHomSectionIsoEquiv x y X T).symm q = q.hom :=
  (rfl)

omit [G.IsPrestack J] [∀ U : C, IsGroupoid (G.obj (.mk (op U)))] in
/-- **The fibre morphism sheaf is locally nonempty** when `G` is a gerbe: for every `t : T ⟶ U`
there is a covering sieve of `T` over each of whose arrows `g` the sheaf `H_X` has a section over
`g ≫ t`. It comes from a local isomorphism between `G(t) y` and `G(t) (X_U x)`, transported along
the composition isomorphisms of `G`. -/
theorem fiberHomSheaf_locallyNonempty [G.IsGerbe J] (X : HomCategory bF bG) {T : C} (t : T ⟶ U) :
    ∃ R ∈ J T, ∀ ⦃V : C⦄ (g : V ⟶ T), R g →
      Nonempty ((G.presheafHom y ((X.obj.app (.mk (op U))).toFunctor.obj x)).obj
        (op (Over.mk (g ≫ t)))) := by
  obtain ⟨R, hR, h⟩ := IsGerbe.exists_covering_iso (J := J) ((G.map t.op.toLoc).toFunctor.obj y)
    ((G.map t.op.toLoc).toFunctor.obj ((X.obj.app (.mk (op U))).toFunctor.obj x))
  refine ⟨R, hR, fun V g hg ↦ (h g hg).map fun e ↦ ?_⟩
  let c := Cat.Hom.toNatIso (G.mapComp' t.op.toLoc g.op.toLoc (g ≫ t).op.toLoc)
  exact (c.app y ≪≫ e ≪≫ (c.app _).symm).hom

end CategoryTheory.Pseudofunctor.BandedMorphism
