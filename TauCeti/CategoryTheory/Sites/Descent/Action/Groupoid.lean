/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# The prestack of an internal group action

For a group object acting on an object in a cartesian monoidal category,
`CategoryTheory.ModObj.actionCategory` assembles Mathlib's `ActionCategory` of the
actions on points into a pseudofunctor. The construction also works for a monoid object.
`CategoryTheory.ModObj.actionCategory_map_obj_back` and
`CategoryTheory.ModObj.actionCategory_pullHom_hom` describe restriction of points and labels.
`CategoryTheory.ModObj.isPrestack_actionCategory_of_isSheaf` gives descent for morphisms when
the representable presheaf of labels is a sheaf and that of points is separated.
In particular, `CategoryTheory.ModObj.isPrestack_actionCategory` applies to subcanonical
topologies, and `CategoryTheory.ModObj.isGroupoid_actionCategory_obj` gives groupoid fibres for a
group object.
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

/-- The presheaf of action categories on points, whose restriction maps precompose
points and arrow labels. Its promotion to a pseudofunctor is `actionCategory`. -/
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
    refine Functor.ext (fun a ↦ ActionCategory.back_injective ?_) ?_
    · simp only [ActionCategory.back_map_obj, Functor.id_obj, unop_id]
      exact Category.id_comp a.back
    · intro a b f
      apply Functor.Elements.hom_ext
      simp
  map_comp f g := by
    apply congrArg Functor.toCatHom
    refine Functor.ext (fun a ↦ ActionCategory.back_injective ?_) ?_
    · simp only [Functor.comp_obj, Functor.toCatHom_toFunctor,
        ActionCategory.back_map_obj, unop_comp]
      exact Category.assoc _ _ _
    · intro a b h
      apply Functor.Elements.hom_ext
      simp [Category.assoc]

/-- The category-valued pseudofunctor of the action on points, induced by
`ActionCategory.map`. Its arrows over `T` from `x` to `y` are maps `g : T ⟶ G`
satisfying `g • x = y`. -/
abbrev actionCategory : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v, v} :=
  (actionCategoryFunctor G X).toPseudofunctor'

-- The generic simp rule `Functor.toPseudofunctor'_map` rewrites the left-hand side first.
/-- Restriction of an object precomposes its point. -/
lemma actionCategory_map_obj_back {U V : C} (f : V ⟶ U)
    (M : (actionCategory G X).obj (.mk (op U))) :
    (((actionCategory G X).map f.op.toLoc).toFunctor.obj M).back = f ≫ M.back :=
  ActionCategory.back_map_obj _ _ M

/-- Restricting the action object corresponding to `x` gives the action object of `f ≫ x`. -/
lemma actionCategory_map_obj_objEquiv {U V : C} {X : C} [ModObj G X] (x : U ⟶ X) (f : V ⟶ U) :
    ((actionCategory G X).map f.op.toLoc).toFunctor.obj (ActionCategory.objEquiv _ _ x) =
      ActionCategory.objEquiv (V ⟶ G) (V ⟶ X) (f ≫ x) :=
  ActionCategory.map_obj _ _ x

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
  have h := Functor.pullHom_toPseudofunctor'_eq (actionCategoryFunctor G X) a f
  rw [h]
  have hlabel {x y x' y' : ActionCategory (W ⟶ G) (W ⟶ X)}
      (hx : x = x') (hy : y' = y) (b : x' ⟶ y') :
      (eqToHom hx ≫ b ≫ eqToHom hy).hom = b.hom := by
    simp only [ActionCategory.comp_hom, ActionCategory.eqToHom_hom, mul_one, one_mul]
  let K := actionCategory G X
  let x₁ : ActionCategory (W ⟶ G) (W ⟶ X) := (K.map (f ≫ p).op.toLoc).toFunctor.obj M
  let x₂ : ActionCategory (W ⟶ G) (W ⟶ X) :=
    (K.map f.op.toLoc).toFunctor.obj ((K.map p.op.toLoc).toFunctor.obj M)
  let y₁ : ActionCategory (W ⟶ G) (W ⟶ X) :=
    (K.map f.op.toLoc).toFunctor.obj ((K.map q.op.toLoc).toFunctor.obj N)
  let y₂ : ActionCategory (W ⟶ G) (W ⟶ X) := (K.map (f ≫ q).op.toLoc).toFunctor.obj N
  -- Maps of the promoted pseudofunctor are definitionally the maps of the presheaf.
  have hx : x₁ = x₂ := congrArg (fun k ↦ k.toFunctor.obj M)
    ((actionCategoryFunctor G X).map_comp p.op f.op)
  have hy : y₁ = y₂ := congrArg (fun k ↦ k.toFunctor.obj N)
    ((actionCategoryFunctor G X).map_comp q.op f.op).symm
  let b : x₂ ⟶ y₁ := ((actionCategoryFunctor G X).map f.op).toFunctor.map a
  have hb : b.hom = f ≫ a.hom := ActionCategory.map_map_hom _ _ a
  exact (hlabel hx hy b).trans hb

/-- For a group object, each fibre of the action category is a groupoid. -/
instance isGroupoid_actionCategory_obj (G X : C) [GrpObj G] [ModObj G X] (T : Cᵒᵖ) :
    IsGroupoid ((actionCategory G X).obj (.mk T)) :=
  inferInstanceAs (IsGroupoid (ActionCategory (unop T ⟶ G) (unop T ⟶ X)))

/-- The action category has descent for morphisms when the representable presheaf of
labels is a sheaf and the representable presheaf of points is separated. -/
lemma isPrestack_actionCategory_of_isSheaf (J : GrothendieckTopology C)
    (hG : Presieve.IsSheaf J (yoneda.obj G)) (hX : Presieve.IsSeparated J (yoneda.obj X)) :
    (actionCategory G X).IsPrestack J where
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
    have hGOver : Presieve.IsSheaf (J.over U) ((Over.forget U).op ⋙ yoneda.obj G) :=
      (isSheaf_iff_isSheaf_of_type _ _).1 (((J.overPullback (Type v) U).obj
        ⟨yoneda.obj G, (isSheaf_iff_isSheaf_of_type _ _).2 hG⟩).property)
    obtain ⟨g, hg, huniq⟩ := hGOver.isSheafFor R.arrows (by simpa using hR) labels hlabels
    let label : T.left ⟶ G := g
    have ha : label • (((actionCategory G X).map T.hom.op.toLoc).toFunctor.obj M).back =
        (((actionCategory G X).map T.hom.op.toLoc).toFunctor.obj N).back := by
      rw [actionCategory_map_obj_back G X T.hom M, actionCategory_map_obj_back G X T.hom N]
      apply (hX _ ((J.mem_over_iff R).1 hR)).ext
      intro V f hf
      let k : Over.mk (f ≫ T.hom) ⟶ T := Over.homMk f
      have hk : R k := (Sieve.overEquiv_iff R f).1 hf
      let m : V ⟶ G := (arrows k hk).hom
      have hgf : f ≫ label = m := hg k hk
      have hlocal : m •
          (((actionCategory G X).map (f ≫ T.hom).op.toLoc).toFunctor.obj M).back =
          (((actionCategory G X).map (f ≫ T.hom).op.toLoc).toFunctor.obj N).back :=
        (arrows k hk).map_val
      rw [actionCategory_map_obj_back G X (f ≫ T.hom) M,
        actionCategory_map_obj_back G X (f ≫ T.hom) N] at hlocal
      simpa only [yoneda_obj_map, Quiver.Hom.unop_op, TypeCat.ofHom_apply, comp_smul, hgf,
        Category.assoc] using hlocal
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

/-- The action category of a monoid object has descent for morphisms in a subcanonical
topology. -/
instance isPrestack_actionCategory (J : GrothendieckTopology C)
    [J.Subcanonical] : (actionCategory G X).IsPrestack J :=
  isPrestack_actionCategory_of_isSheaf G X J
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSeparated

end CategoryTheory.ModObj
