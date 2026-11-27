/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# The prestack of an internal group action

For a group object acting on an object in a cartesian monoidal category,
`CategoryTheory.ModObj.actionCategory` assembles Mathlib's `ActionCategory` of the
actions on points into a pseudofunctor. The construction also works for a monoid object.
`CategoryTheory.ModObj.isPrestack_actionCategory` proves descent for morphisms for a
subcanonical topology by gluing their labels. For a group object the fibres are groupoids.
The computation of restriction on labels uses `Functor.pullHom_toPseudofunctor'_eq`.
This gives the prestack whose stackification is the quotient stack of a group action,
as in [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q).
-/

public section

namespace CategoryTheory.ModObj

open Limits Opposite Bicategory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (G X : C) [MonObj G] [ModObj G X]

/-- The presheaf of action categories constructed using `ActionCategory.map`.
Restriction along a map of test objects precomposes points and arrow labels. -/
abbrev actionCategoryFunctor : Cᵒᵖ ⥤ Cat.{v, v} where
  obj T := Cat.of (ActionCategory (unop T ⟶ G) (unop T ⟶ X))
  map f := (ActionCategory.map
    { toFun := (f.unop ≫ ·)
      map_one' := MonObj.comp_one f.unop
      map_mul' := MonObj.comp_mul f.unop }
    { toFun := (f.unop ≫ ·)
      map_smul' := fun g x ↦ comp_smul f.unop g x }).toCatHom
  map_id T := by
    apply congrArg Functor.toCatHom
    refine Functor.ext (fun a ↦ (ActionCategory.objEquiv _ _).symm.injective ?_) ?_
    · simp only [ActionCategory.objEquiv, Equiv.coe_fn_symm_mk,
        ActionCategory.back_map_obj, Functor.id_obj, unop_id]
      exact Category.id_comp a.back
    · intro a b f
      apply Functor.Elements.hom_ext
      simp
  map_comp f g := by
    apply congrArg Functor.toCatHom
    refine Functor.ext (fun a ↦ (ActionCategory.objEquiv _ _).symm.injective ?_) ?_
    · simp only [ActionCategory.objEquiv, Equiv.coe_fn_symm_mk,
        Functor.comp_obj, Functor.toCatHom_toFunctor, ActionCategory.back_map_obj, unop_comp]
      exact Category.assoc _ _ _
    · intro a b h
      apply Functor.Elements.hom_ext
      simp [Category.assoc]

/-- The category-valued pseudofunctor of the action on points. Its arrows over `T`
from `x` to `y` are maps `g : T ⟶ G` satisfying `g • x = y`. -/
abbrev actionCategory : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v, v} :=
  (actionCategoryFunctor G X).toPseudofunctor'

/-- Restriction of an object precomposes its point. -/
lemma actionCategory_map_obj_back {U V : C} (f : V ⟶ U)
    (M : (actionCategory G X).obj (.mk (op U))) :
    (((actionCategory G X).map f.op.toLoc).toFunctor.obj M).back = f ≫ M.back :=
  ActionCategory.back_map_obj _ _ M

/-- Restriction of a morphism precomposes its label. -/
@[simp]
lemma actionCategory_map_map_hom {U V : C} (f : V ⟶ U)
    {M N : (actionCategory G X).obj (.mk (op U))} (a : M ⟶ N) :
    (((actionCategory G X).map f.op.toLoc).toFunctor.map a).hom = f ≫ a.hom :=
  ActionCategory.map_map_hom _ _ a

/-- An arrow between the restrictions along `p` and `q` is restricted by
precomposing its label. -/
@[simp]
lemma actionCategory_pullHom_hom {U V W : C} {M N : (actionCategory G X).obj (.mk (op U))}
    {p q : V ⟶ U}
    (a : ((actionCategory G X).map p.op.toLoc).toFunctor.obj M ⟶
      ((actionCategory G X).map q.op.toLoc).toFunctor.obj N)
    (f : W ⟶ V) {p' q' : W ⟶ U} (hp : f ≫ p = p') (hq : f ≫ q = q') :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom a f p' q' hp hq).hom = f ≫ a.hom := by
  subst p' q'
  let h (r : V ⟶ U) : (actionCategory G X).map (f ≫ r).op.toLoc =
      (actionCategory G X).map r.op.toLoc ≫ (actionCategory G X).map f.op.toLoc :=
    (actionCategoryFunctor G X).map_comp r.op f.op
  have hEq := Functor.pullHom_toPseudofunctor'_eq
    (actionCategoryFunctor G X) a f
  rw [hEq]
  have hlabel {x₁ x₂ y₁ y₂ : ActionCategory (W ⟶ G) (W ⟶ X)}
      (hx : x₁ = x₂) (hy : y₁ = y₂) (b : x₂ ⟶ y₁) :
      (eqToHom hx ≫ b ≫ eqToHom hy).hom = b.hom := by
    simp
  refine Eq.trans ?_ (actionCategory_map_map_hom G X f a)
  let K := actionCategory G X
  let x₁ : ActionCategory (W ⟶ G) (W ⟶ X) := (K.map (f ≫ p).op.toLoc).toFunctor.obj M
  let x₂ : ActionCategory (W ⟶ G) (W ⟶ X) :=
    (K.map f.op.toLoc).toFunctor.obj ((K.map p.op.toLoc).toFunctor.obj M)
  let y₁ : ActionCategory (W ⟶ G) (W ⟶ X) :=
    (K.map f.op.toLoc).toFunctor.obj ((K.map q.op.toLoc).toFunctor.obj N)
  let y₂ : ActionCategory (W ⟶ G) (W ⟶ X) := (K.map (f ≫ q).op.toLoc).toFunctor.obj N
  have hx : x₁ = x₂ := congrArg (fun k ↦ k.toFunctor.obj M) (h p)
  have hy : y₁ = y₂ := congrArg (fun k ↦ k.toFunctor.obj N) (h q).symm
  let b : x₂ ⟶ y₁ := (K.map f.op.toLoc).toFunctor.map a
  exact hlabel hx hy b

/-- For a group object, each fibre of the action category is a groupoid. -/
instance isGroupoid_actionCategory_obj (G X : C) [GrpObj G] [ModObj G X] (T : Cᵒᵖ) :
    IsGroupoid ((actionCategory G X).obj (.mk T)) :=
  inferInstanceAs (IsGroupoid (ActionCategory (unop T ⟶ G) (unop T ⟶ X)))

/-- The action category has descent for morphisms in every subcanonical topology.
Arrow labels glue in the representable presheaf of the acting monoid. -/
instance isPrestack_actionCategory (J : GrothendieckTopology C)
    [J.Subcanonical] : (actionCategory G X).IsPrestack J where
  isSheaf {U} M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    intro T R hR arrows harrows
    let labels : Presieve.FamilyOfElements ((Over.forget U).op ⋙ yoneda.obj G) R.arrows :=
      fun _ f hf ↦ (arrows f hf).hom
    have hlabels : labels.Compatible := (Presieve.compatible_iff_sieveCompatible _).2
      (by
        intro V W f g hf
        have h := congrArg Functor.Elements.Hom.hom (harrows.to_sieveCompatible f g hf)
        exact h.trans (actionCategory_pullHom_hom G X (arrows f hf) g.left (Over.w g) (Over.w g)))
    have hsheaf (Y : C) : Presieve.IsSheaf (J.over U) ((Over.forget U).op ⋙ yoneda.obj Y) :=
      (isSheaf_iff_isSheaf_of_type _ _).1 (((J.overPullback (Type v) U).obj
        (J.yoneda.obj Y)).property)
    have hG := (hsheaf G).isSheafFor R.arrows (by simpa using hR)
    obtain ⟨g, hg, huniq⟩ := hG labels hlabels
    let label : T.left ⟶ G := g
    have ha : label • (((actionCategory G X).map T.hom.op.toLoc).toFunctor.obj M).back =
        (((actionCategory G X).map T.hom.op.toLoc).toFunctor.obj N).back := by
      rw [actionCategory_map_obj_back G X T.hom M, actionCategory_map_obj_back G X T.hom N]
      apply ((hsheaf X).isSheafFor R.arrows (by simpa using hR)).isSeparatedFor.ext
      intro V f hf
      let m : V.left ⟶ G := (arrows f hf).hom
      have hgf : f.left ≫ label = m := hg f hf
      have hlocal : m • (((actionCategory G X).map V.hom.op.toLoc).toFunctor.obj M).back =
          (((actionCategory G X).map V.hom.op.toLoc).toFunctor.obj N).back :=
        (arrows f hf).map_val
      rw [actionCategory_map_obj_back G X V.hom M,
        actionCategory_map_obj_back G X V.hom N] at hlocal
      -- The restricted sheaf of points acts on arrows by precomposition.
      change f.left ≫ (label • (T.hom ≫ M.back)) = f.left ≫ T.hom ≫ N.back
      simpa only [comp_smul, hgf, Over.w_assoc] using hlocal
    let a : ((actionCategory G X).presheafHom M N).obj (op T) :=
      Functor.Elements.homMk label ha
    refine ⟨a, ?_, ?_⟩
    · intro V f hf
      apply Functor.Elements.hom_ext
      exact (actionCategory_pullHom_hom G X a f.left (Over.w f) (Over.w f)).trans (hg f hf)
    · intro b hb
      apply Functor.Elements.hom_ext
      apply huniq
      intro V f hf
      have h := congrArg Functor.Elements.Hom.hom (hb f hf)
      exact (actionCategory_pullHom_hom G X b f.left (Over.w f) (Over.w f)).symm.trans h

end CategoryTheory.ModObj
