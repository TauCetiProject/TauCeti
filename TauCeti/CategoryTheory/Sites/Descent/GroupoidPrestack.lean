/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import TauCeti.CategoryTheory.Sites.GroupoidObject
public import TauCeti.CategoryTheory.Sites.Over.Basic

/-!
# The prestack of a groupoid object in sheaves

A groupoid object `G = (X, R, s, t, e, c, i)` in `J`-sheaves of sets defines a `Cat`-valued
pseudofunctor on `LocallyDiscrete Cᵒᵖ`, `GroupoidObject.toPseudofunctor G`, whose fibre over `U`
is the groupoid `GroupoidObject.Fiber G U` with objects the sections of `X` over `U` and arrows
the sections of `R` over `U`, and whose pullback along `V ⟶ U` restricts sections. It comes from
the functor `GroupoidObject.fiberFunctor G : Cᵒᵖ ⥤ Cat`, so its comparison isomorphisms are
identities.

Its fibres are groupoids, and it is a prestack for `J`: for objects `x` and `y` over `S`, the
presheaf of morphisms from `x` to `y` on `Over S` sends `T ⟶ S` to the sections `r` of `R` over
`T` with `s r = x|_T` and `t r = y|_T`, the fibre of `(s, t) : R ⟶ X × X` over `(x, y)`; it is a
sheaf because `R` is a sheaf and `X` is separated. Its stackification is the quotient stack
`[X/R]` (Stacks, Definition 78.20.1 (044Q), there for groupoids in algebraic spaces).

The construction follows the discrete pseudofunctor `CategoryTheory.Pseudofunctor.ofPresheaf` of
a presheaf of types (`TauCeti.CategoryTheory.Sites.Descent.Discrete`), which is likewise the
pseudofunctor `Functor.toPseudofunctor'` of a functor to `Cat` built by restriction of sections.
This file generalizes its discrete case, where every arrow is an identity, to groupoids with a
sheaf of arrows `R`.

## Main declarations

* `TauCeti.CategoryTheory.GroupoidObject.pullFunctor`: restriction of sections, a functor between
  groupoids of sections.
* `TauCeti.CategoryTheory.GroupoidObject.fiberFunctor`: the functor `U ↦ Fiber G U` to `Cat`.
* `TauCeti.CategoryTheory.GroupoidObject.toPseudofunctor`: the pseudofunctor of a groupoid
  object, with `isGroupoid_toPseudofunctor_obj`.
* `TauCeti.CategoryTheory.GroupoidObject.pullHom_arr`: pulling back a morphism restricts the
  underlying section of `R`.
* `TauCeti.CategoryTheory.GroupoidObject.presheafHomIso`: the presheaf of morphisms between two
  objects is the fibre of `(s, t)` over them.
* `TauCeti.CategoryTheory.GroupoidObject.isPrestack_toPseudofunctor`: the pseudofunctor of a
  groupoid object is a prestack.

## References

* [Stacks Project, Definition 78.20.1](https://stacks.math.columbia.edu/tag/044Q)
-/

public section

universe w' w v u

open CategoryTheory Opposite Bicategory Pseudofunctor LocallyDiscreteOpToCat

namespace TauCeti.CategoryTheory.GroupoidObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (G : GroupoidObject.{w} J)

/-- Restriction of sections along `φ : U ⟶ V` in `Cᵒᵖ`, a functor from the groupoid of sections
over `U` to the groupoid of sections over `V`. -/
def pullFunctor {U V : Cᵒᵖ} (φ : U ⟶ V) : Fiber.{w'} G U ⥤ Fiber.{w'} G V where
  obj x := ⟨G.X.obj.map φ x.as⟩
  map f := ⟨G.R.obj.map φ f.arr, by rw [NatTrans.naturality_apply, f.s_arr],
    by rw [NatTrans.naturality_apply, f.t_arr]⟩
  map_id x := Fiber.hom_ext (NatTrans.naturality_apply G.e.hom φ x.as).symm
  map_comp f g := Fiber.hom_ext (G.map_c φ f.arr g.arr _)

variable {G}

/-- Restriction of an object restricts the underlying section of `X`. -/
@[simp]
lemma pullFunctor_obj_as {U V : Cᵒᵖ} (φ : U ⟶ V) (x : Fiber.{w'} G U) :
    ((G.pullFunctor φ).obj x).as = G.X.obj.map φ x.as :=
  (rfl)

/-- Restriction of a morphism restricts the underlying section of `R`. -/
@[simp]
lemma pullFunctor_map_arr {U V : Cᵒᵖ} (φ : U ⟶ V) {x y : Fiber.{w'} G U} (f : x ⟶ y) :
    ((G.pullFunctor φ).map f).arr = G.R.obj.map φ f.arr :=
  (rfl)

variable (G)

/-- The functor `Cᵒᵖ ⥤ Cat` sending `U` to the groupoid of sections of `G` over `U`, with objects
lifted to the universe `max w w'`, and `φ` to the restriction functor. Its body is exposed
because its value at `U` is, by definition, `Fiber G U`, whose objects and morphisms are
sections of `X` and `R`. -/
@[expose]
def fiberFunctor : Cᵒᵖ ⥤ Cat.{w, max w w'} where
  obj U := Cat.of (Fiber.{w'} G U)
  map φ := (G.pullFunctor φ).toCatHom
  map_id U := by
    ext
    exact _root_.CategoryTheory.Functor.ext (fun x ↦ Fiber.ext (by simp))
      (fun x y f ↦ Fiber.hom_eq_eqToHom_comp _ _ (Fiber.ext (by simp)) (Fiber.ext (by simp))
        (by simp))
  map_comp φ ψ := by
    ext
    exact _root_.CategoryTheory.Functor.ext (fun x ↦ Fiber.ext (by simp))
      (fun x y f ↦ Fiber.hom_eq_eqToHom_comp _ _ (Fiber.ext (by simp)) (Fiber.ext (by simp))
        (by simp))

/-- The pseudofunctor of a groupoid object `G` in `J`-sheaves of sets: its fibre over `U` is the
groupoid of sections of `G` over `U`, with objects the sections of `X` and morphisms the sections
of `R`, lifted to the universe `max w w'`, and pullback along `f` restricts sections. On the big
site `Over S` of `S : Scheme.{u}`, with sheaves of sets in `Type u`, take `w = u` and `w' = u + 1`
to obtain values in `Cat.{u, u + 1}`. Its body is exposed for the same reason as that of
`fiberFunctor`. -/
@[expose]
def toPseudofunctor : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, max w w'} :=
  (fiberFunctor.{w'} G).toPseudofunctor'

/-- The fibres of the pseudofunctor of a groupoid object are groupoids. -/
instance isGroupoid_toPseudofunctor_obj (U : LocallyDiscrete Cᵒᵖ) :
    IsGroupoid ((toPseudofunctor.{w'} G).obj U) :=
  inferInstanceAs (IsGroupoid (Fiber.{w'} G U.as))

variable {G}

/-- The identity of an object of the pseudofunctor of `G` is the identity arrow `e x`. This is
`Fiber.id_arr` for the category structure of the fibres of `toPseudofunctor G`, which `simp`
does not identify syntactically with that of `Fiber G U`. -/
@[simp]
lemma toPseudofunctor_id_arr {U : LocallyDiscrete Cᵒᵖ} (x : (toPseudofunctor.{w'} G).obj U) :
    Fiber.Hom.arr (𝟙 x) = G.e.hom.app U.as x.as :=
  (rfl)

/-- The composite of morphisms of the pseudofunctor of `G` is the composite `c φ ψ` of the
underlying arrows (`Fiber.comp_arr` for the fibres of `toPseudofunctor G`). -/
@[simp]
lemma toPseudofunctor_comp_arr {U : LocallyDiscrete Cᵒᵖ} {x y z : (toPseudofunctor.{w'} G).obj U}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    (φ ≫ ψ).arr = G.c φ.arr ψ.arr (φ.t_arr.trans ψ.s_arr.symm) :=
  (rfl)

/-- The morphism `eqToHom h` of the pseudofunctor of `G` is the identity arrow of its source
(`Fiber.eqToHom_arr` for the fibres of `toPseudofunctor G`). -/
@[simp]
lemma toPseudofunctor_eqToHom_arr {U : LocallyDiscrete Cᵒᵖ} {x y : (toPseudofunctor.{w'} G).obj U}
    (h : x = y) : (eqToHom h).arr = G.e.hom.app U.as x.as :=
  Fiber.eqToHom_arr h

/-- Pulling back an object of the pseudofunctor of `G` restricts the underlying section of
`X`. -/
@[simp]
lemma toPseudofunctor_map_obj_as {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (x : (toPseudofunctor.{w'} G).obj U) :
    (((toPseudofunctor.{w'} G).map f).toFunctor.obj x).as = G.X.obj.map f.as x.as :=
  (rfl)

/-- Pulling back a morphism of the pseudofunctor of `G` restricts the underlying section of
`R`. -/
@[simp]
lemma toPseudofunctor_map_map_arr {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    {x y : (toPseudofunctor.{w'} G).obj U} (φ : x ⟶ y) :
    (((toPseudofunctor.{w'} G).map f).toFunctor.map φ).arr = G.R.obj.map f.as φ.arr :=
  (rfl)

/-- The comparison isomorphisms of the pseudofunctor of `G` for composites are identities. -/
lemma toPseudofunctor_mapComp' {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W)
    (fg : U ⟶ W) (h : f ≫ g = fg) :
    (toPseudofunctor.{w'} G).mapComp' f g fg h =
      eqToIso (by subst h; exact (fiberFunctor.{w'} G).map_comp f.as g.as) := by
  subst h
  rw [mapComp'_eq_mapComp]
  exact Functor.toPseudofunctor'_mapComp _ _ _

/-- Pulling back a morphism `φ` between pullbacks of objects of the pseudofunctor of `G` along
`g` restricts the underlying section of `R`. -/
@[simp]
lemma pullHom_arr ⦃X₁ X₂ : C⦄ ⦃M₁ : (toPseudofunctor.{w'} G).obj (.mk (op X₁))⦄
    ⦃M₂ : (toPseudofunctor.{w'} G).obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : ((toPseudofunctor.{w'} G).map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      ((toPseudofunctor.{w'} G).map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄ (g : Y' ⟶ Y)
    (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (pullHom φ g gf₁ gf₂ hgf₁ hgf₂).arr = G.R.obj.map g.op φ.arr := by
  simp only [pullHom, toPseudofunctor_comp_arr, toPseudofunctor_mapComp', eqToIso.hom,
    eqToIso.inv, Cat.eqToHom_app, toPseudofunctor_eqToHom_arr, toPseudofunctor_map_map_arr,
    c_e_left, c_e_right]
  rfl

variable (G) in
/-- For sections `x` and `y` of the sheaf of objects of `G` over `S`, the subfunctor of the
restriction of the sheaf of arrows to `Over S` whose sections over `T ⟶ S` are the arrows from
`x|_T` to `y|_T`: the fibre of `(s, t) : R ⟶ X × X` over `(x, y)`. -/
def homSubfunctor {S : C} (x y : G.X.obj.obj (op S)) :
    Subfunctor ((Over.forget S).op ⋙ G.R.obj) where
  obj T := {r | G.s.hom.app _ r = G.X.obj.map T.unop.hom.op x ∧
    G.t.hom.app _ r = G.X.obj.map T.unop.hom.op y}
  map p r hr :=
    ⟨(NatTrans.naturality_apply G.s.hom p.unop.left.op r).trans
        ((congrArg _ hr.1).trans (Over.map_left_op_map_hom_op G.X.obj p.unop x)),
      (NatTrans.naturality_apply G.t.hom p.unop.left.op r).trans
        ((congrArg _ hr.2).trans (Over.map_left_op_map_hom_op G.X.obj p.unop y))⟩

/-- A section of `R` over `T ⟶ S` lies in `homSubfunctor G x y` iff it is an arrow from `x|_T` to
`y|_T`. -/
@[simp]
lemma mem_homSubfunctor_obj_iff {S : C} (x y : G.X.obj.obj (op S)) {T : (Over S)ᵒᵖ}
    (r : G.R.obj.obj (op T.unop.left)) :
    r ∈ (homSubfunctor G x y).obj T ↔ G.s.hom.app _ r = G.X.obj.map T.unop.hom.op x ∧
      G.t.hom.app _ r = G.X.obj.map T.unop.hom.op y :=
  Iff.rfl

/-- The presheaf of morphisms between two objects `x` and `y` of the pseudofunctor of `G` over
`S` is the fibre of `(s, t) : R ⟶ X × X` over `(x, y)`: a morphism from `x|_T` to `y|_T` is a
section of `R` over `T` from `x|_T` to `y|_T`. -/
def presheafHomIso {S : C} (x y : (toPseudofunctor.{w'} G).obj (.mk (op S))) :
    (toPseudofunctor.{w'} G).presheafHom x y ≅ (homSubfunctor G x.as y.as).toFunctor :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun φ := ⟨φ.arr, φ.s_arr, φ.t_arr⟩
      invFun r := ⟨r.val, r.property.1, r.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl })
    (fun p ↦ by
      ext φ
      exact Subtype.ext (pullHom_arr φ p.unop.left _ _ (Over.w p.unop) (Over.w p.unop)))

/-- The section of `R` attached to a morphism by `presheafHomIso` is its underlying arrow. -/
lemma presheafHomIso_hom_app_coe {S : C} (x y : (toPseudofunctor.{w'} G).obj (.mk (op S)))
    (T : (Over S)ᵒᵖ) (φ : ((toPseudofunctor.{w'} G).presheafHom x y).obj T) :
    ((presheafHomIso x y).hom.app T φ).val = φ.arr :=
  (rfl)

/-- The pseudofunctor of a groupoid object in `J`-sheaves of sets is a prestack for `J`: the
presheaves of morphisms are the fibres of `(s, t) : R ⟶ X × X`, which are sheaves because `R` is
a sheaf and `X` is separated. -/
instance isPrestack_toPseudofunctor : (toPseudofunctor.{w'} G).IsPrestack J where
  isSheaf {S} x y := by
    rw [isSheaf_iff_isSheaf_of_type]
    refine Presieve.isSheaf_iso (J.over S) (presheafHomIso x y).symm ?_
    have hX : Presieve.IsSeparated (J.over S) ((Over.forget S).op ⋙ G.X.obj) :=
      ((isSheaf_iff_isSheaf_of_type _ _).1 (G.X.over S).property).isSeparated
    refine (Subfunctor.isSheaf_iff _
      ((isSheaf_iff_isSheaf_of_type _ _).1 (G.R.over S).property)).2 fun T r hr ↦ ?_
    refine ⟨(hX _ hr).ext fun Y f hf ↦ ?_, (hX _ hr).ext fun Y f hf ↦ ?_⟩
    · exact (NatTrans.naturality_apply G.s.hom f.left.op r).symm.trans
        (hf.1.trans (Over.map_left_op_map_hom_op G.X.obj f x.as).symm)
    · exact (NatTrans.naturality_apply G.t.hom f.left.op r).symm.trans
        (hf.2.trans (Over.map_left_op_map_hom_op G.X.obj f y.as).symm)

end TauCeti.CategoryTheory.GroupoidObject
