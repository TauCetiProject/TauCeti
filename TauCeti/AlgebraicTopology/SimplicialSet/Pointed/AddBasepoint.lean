/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Basic

import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
-- The degreewise formulas below compute through the native undercategory presentation.
import all TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Basic

/-!
# Adjoining a disjoint basepoint to a simplicial set

The functor `K ↦ K₊` adjoins a disjoint basepoint degreewise to a simplicial set. It is left
adjoint to forgetting the basepoint of a pointed simplicial set: based maps `K₊ ⟶ X` are the
same as unpointed maps `K ⟶ X`. On underlying simplicial sets, `K₊` is the disjoint union of `K`
with a point, so `K ↦ K₊` preserves monomorphisms, sends every map `f : K ⟶ L` to a pushout of
`f` along the inclusion `K ⟶ K₊`, and preserves anodyne extensions on underlying simplicial sets.

## Main definitions

* `PointedSSet.addBasepoint`: adjoin a disjoint basepoint to a simplicial set.
* `PointedSSet.addBasepointHomEquiv`: based maps from `K₊` are unpointed maps from `K`.
* `PointedSSet.addBasepointForgetAdjunction`: the adjunction `(-)₊ ⊣ forget`.
* `PointedSSet.addBasepointι`: the inclusion `K ⟶ K₊` of non-basepoint simplices, with
  `PointedSSet.isPushout_addBasepoint_map` and
  `PointedSSet.anodyneExtensions_addBasepoint_map_right`.
-/

public section

universe u

open CategoryTheory CategoryTheory.ConcreteCategory

namespace TauCeti.PointedSSet

/-- Adjoin a disjoint basepoint degreewise to a simplicial set. -/
@[expose]
def addBasepoint : SSet.{u} ⥤ PointedSSet.{u} where
  obj K := Under.mk (Y := K ⋙ typeToPointed ⋙ forget Pointed)
    { app := fun _ ↦ ↾fun _ ↦ none
      naturality := fun _ _ _ ↦ rfl }
  map {K L} f := Under.homMk
    { app := fun n ↦ (typeToPointed ⋙ forget Pointed).map (f.app n)
      naturality := fun n m g ↦ by
        ext x
        cases x with
        | none => rfl
        | some x => exact congrArg some (congr_hom (f.naturality g) x) }
    rfl
  map_id K := by
    ext n x
    cases x <;> rfl
  map_comp f g := by
    ext n x
    cases x <;> rfl

@[simp]
lemma addBasepoint_obj_right_obj (K : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    ((addBasepoint.obj K).right.obj n) = Option (K.obj n) :=
  (rfl)

@[simp]
lemma addBasepoint_obj_point (K : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    (addBasepoint.obj K).point n = none :=
  (rfl)

@[simp]
lemma addBasepoint_obj_map_none (K : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (addBasepoint.obj K).right.map f none = none :=
  (rfl)

@[simp]
lemma addBasepoint_obj_map_some (K : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (x : K.obj n) :
    (addBasepoint.obj K).right.map f (some x) = some (K.map f x) :=
  (rfl)

@[simp]
lemma addBasepoint_map_right_app_none {K L : SSet.{u}} (f : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) :
    (addBasepoint.map f).right.app n none = none :=
  (rfl)

@[simp]
lemma addBasepoint_map_right_app_some {K L : SSet.{u}} (f : K ⟶ L)
    (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    (addBasepoint.map f).right.app n (some x) = some (f.app n x) :=
  (rfl)

/-- Based maps from `K₊` are the same as unpointed maps from `K`. -/
def addBasepointHomEquiv (K : SSet.{u}) (X : PointedSSet.{u}) :
    (addBasepoint.obj K ⟶ X) ≃ (K ⟶ X.right) where
  toFun f :=
    { app := fun n ↦ ↾fun x ↦ f.right.app n (some x)
      naturality := fun _ _ g ↦ by
        ext x
        -- The ascription makes `some x` a simplex of `K₊`, whose type is `Option (K.obj _)`.
        exact congr_hom (f.right.naturality g) (some x : Option (K.obj _)) }
  invFun f := Under.homMk
    { app := fun n ↦ ↾fun x ↦ x.elim (X.point n) (f.app n)
      naturality := fun n m g ↦ by
        ext x
        cases x with
        | none => exact (X.map_point g).symm
        | some x => exact congr_hom (f.naturality g) x }
    (by
      ext n x
      exact (hom_app X n x).symm)
  left_inv f := by
    ext n x
    cases x with
    | none => exact (app_point f n).symm
    | some _ => rfl
  right_inv _ := rfl

@[simp]
lemma addBasepointHomEquiv_apply_app {K : SSet.{u}} {X : PointedSSet.{u}}
    (f : addBasepoint.obj K ⟶ X) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    (addBasepointHomEquiv K X f).app n x = f.right.app n (some x) :=
  (rfl)

@[simp]
lemma addBasepointHomEquiv_symm_app_none {K : SSet.{u}} {X : PointedSSet.{u}}
    (f : K ⟶ X.right) (n : SimplexCategoryᵒᵖ) :
    ((addBasepointHomEquiv K X).symm f).right.app n none = X.point n :=
  (rfl)

@[simp]
lemma addBasepointHomEquiv_symm_app_some {K : SSet.{u}} {X : PointedSSet.{u}}
    (f : K ⟶ X.right) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    ((addBasepointHomEquiv K X).symm f).right.app n (some x) = f.app n x :=
  (rfl)

/-- `addBasepointHomEquiv` is natural in the source: precomposition with `g` corresponds to
precomposition with `g₊`. -/
lemma addBasepointHomEquiv_map_comp {K' K : SSet.{u}} {X : PointedSSet.{u}} (g : K' ⟶ K)
    (f : addBasepoint.obj K ⟶ X) :
    addBasepointHomEquiv K' X (addBasepoint.map g ≫ f) = g ≫ addBasepointHomEquiv K X f :=
  (rfl)

/-- `addBasepointHomEquiv` is natural in the target: postcomposition with `g` corresponds to
postcomposition with its underlying map. -/
lemma addBasepointHomEquiv_comp {K : SSet.{u}} {X Y : PointedSSet.{u}}
    (f : addBasepoint.obj K ⟶ X) (g : X ⟶ Y) :
    addBasepointHomEquiv K Y (f ≫ g) = addBasepointHomEquiv K X f ≫ g.right :=
  (rfl)

/-- Extending an unpointed map to `K₊` is natural in the source: precomposing with `g₊`
corresponds to precomposing with `g`. -/
@[reassoc]
lemma addBasepoint_map_comp_addBasepointHomEquiv_symm {K' K : SSet.{u}} {X : PointedSSet.{u}}
    (g : K' ⟶ K) (f : K ⟶ X.right) :
    addBasepoint.map g ≫ (addBasepointHomEquiv K X).symm f =
      (addBasepointHomEquiv K' X).symm (g ≫ f) := by
  apply (addBasepointHomEquiv K' X).injective
  rw [addBasepointHomEquiv_map_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Extending an unpointed map to `K₊` is natural in the target: postcomposing with a based map
`g` corresponds to postcomposing with `g.right`. -/
@[reassoc]
lemma addBasepointHomEquiv_symm_comp {K : SSet.{u}} {X Y : PointedSSet.{u}}
    (f : K ⟶ X.right) (g : X ⟶ Y) :
    (addBasepointHomEquiv K X).symm f ≫ g =
      (addBasepointHomEquiv K Y).symm (f ≫ g.right) := by
  apply (addBasepointHomEquiv K Y).injective
  rw [addBasepointHomEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Forget the basepoint of a pointed simplicial set. -/
abbrev forgetBasepoint : PointedSSet.{u} ⥤ SSet.{u} :=
  Under.forget _

/-- Adjoining a disjoint basepoint is left adjoint to forgetting the basepoint. -/
def addBasepointForgetAdjunction :
    addBasepoint ⊣ forgetBasepoint :=
  Adjunction.mkOfHomEquiv
    { homEquiv := addBasepointHomEquiv
      homEquiv_naturality_right := addBasepointHomEquiv_comp
      homEquiv_naturality_left_symm := fun f g ↦
        (addBasepoint_map_comp_addBasepointHomEquiv_symm f g).symm }

/-- The hom-set bijection of `addBasepointForgetAdjunction` is `addBasepointHomEquiv`. -/
@[simp]
lemma addBasepointForgetAdjunction_homEquiv :
    addBasepointForgetAdjunction.{u}.homEquiv = addBasepointHomEquiv :=
  Adjunction.mkOfHomEquiv_homEquiv _

/-- The counit of `addBasepointForgetAdjunction` sends the adjoined basepoint to the basepoint of
`X` and is the identity on non-basepoint simplices. -/
@[simp]
lemma addBasepointForgetAdjunction_counit_app (X : PointedSSet.{u}) :
    addBasepointForgetAdjunction.counit.app X = (addBasepointHomEquiv X.right X).symm (𝟙 X.right) :=
  Adjunction.mkOfHomEquiv_counit_app _ X

instance : addBasepoint.{u}.IsLeftAdjoint :=
  addBasepointForgetAdjunction.isLeftAdjoint

instance : forgetBasepoint.{u}.IsRightAdjoint :=
  addBasepointForgetAdjunction.isRightAdjoint

/-- The inclusion `K ⟶ K₊` of a simplicial set as the non-basepoint simplices of `K₊`: the unit of
`addBasepointForgetAdjunction`. -/
def addBasepointι (K : SSet.{u}) : K ⟶ (addBasepoint.obj K).right :=
  addBasepointHomEquiv K (addBasepoint.obj K) (𝟙 _)

@[simp]
lemma addBasepointForgetAdjunction_unit_app (K : SSet.{u}) :
    addBasepointForgetAdjunction.unit.app K = addBasepointι K :=
  Adjunction.mkOfHomEquiv_unit_app _ K

@[simp]
lemma addBasepointι_app (K : SSet.{u}) (n : SimplexCategoryᵒᵖ) (x : K.obj n) :
    (addBasepointι K).app n x = some x :=
  (rfl)

@[reassoc (attr := simp)]
lemma addBasepointι_naturality {K L : SSet.{u}} (f : K ⟶ L) :
    f ≫ addBasepointι L = addBasepointι K ≫ (addBasepoint.map f).right :=
  (rfl)

/-- `addBasepointHomEquiv` restricts a based map `K₊ ⟶ X` along the inclusion `K ⟶ K₊`. -/
lemma addBasepointHomEquiv_apply {K : SSet.{u}} {X : PointedSSet.{u}}
    (f : addBasepoint.obj K ⟶ X) :
    addBasepointHomEquiv K X f = addBasepointι K ≫ f.right :=
  (rfl)

/-- Extending an unpointed map `K ⟶ X` to `K₊ ⟶ X` recovers the original map on `K`. -/
@[reassoc (attr := simp)]
lemma addBasepointι_comp_addBasepointHomEquiv_symm_right {K : SSet.{u}} {X : PointedSSet.{u}}
    (f : K ⟶ X.right) :
    addBasepointι K ≫ ((addBasepointHomEquiv K X).symm f).right = f := by
  simpa only [addBasepointHomEquiv_apply] using (addBasepointHomEquiv K X).apply_symm_apply f

/-- Based maps out of `K₊` are determined by their restrictions along `K ⟶ K₊`. -/
@[ext]
lemma addBasepoint_hom_ext {K : SSet.{u}} {X : PointedSSet.{u}}
    {f g : addBasepoint.obj K ⟶ X}
    (h : addBasepointι K ≫ f.right = addBasepointι K ≫ g.right) : f = g := by
  apply (addBasepointHomEquiv K X).injective
  simpa only [addBasepointHomEquiv_apply] using h

instance (K : SSet.{u}) : Mono (addBasepointι K) :=
  ⟨fun _ _ e ↦ by
    ext n z
    exact Option.some.inj (congr_hom (congr_app e n) z)⟩

/-- On underlying simplicial sets, `L₊` is the pushout of `K₊` and `L` along `K`, identifying the
non-basepoint simplices of `K₊` with `K` and retaining the disjoint basepoint. -/
lemma isPushout_addBasepoint_map {K L : SSet.{u}} (f : K ⟶ L) :
    IsPushout (addBasepointι K) f (addBasepoint.map f).right (addBasepointι L) where
  w := (addBasepointι_naturality f).symm
  isColimit' := ⟨Limits.PushoutCocone.isColimitAux' _ fun s ↦
    ⟨{ app n := ↾fun x ↦ x.elim (s.inl.app n none) (s.inr.app n)
       naturality n m g := by
         ext x
         cases x with
         | none => exact congr_hom (s.inl.naturality g) (none : Option (K.obj n))
         | some y => exact congr_hom (s.inr.naturality g) y },
     by
       ext n x
       cases x with
       | none => rfl
       | some x => exact (congr_hom (congr_app s.condition n) x).symm,
     rfl,
     fun hm₁ hm₂ ↦ by
       ext n x
       cases x with
       | none => exact congr_hom (congr_app hm₁ n) (none : Option (K.obj n))
       | some y => exact congr_hom (congr_app hm₂ n) y⟩⟩

instance {K L : SSet.{u}} (f : K ⟶ L) [Mono f] : Mono (addBasepoint.map f).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  exact (mono_iff_injective _).2
    (Option.map_injective ((mono_iff_injective (f.app n)).1 inferInstance))

instance : addBasepoint.{u}.PreservesMonomorphisms where
  preserves f _ :=
    (Under.forget _).mono_of_mono_map (inferInstance : Mono (addBasepoint.map f).right)

/-- Adjoining a disjoint basepoint preserves anodyne extensions on underlying simplicial sets. -/
lemma anodyneExtensions_addBasepoint_map_right {K L : SSet.{u}} {i : K ⟶ L}
    (hi : SSet.anodyneExtensions i) : SSet.anodyneExtensions (addBasepoint.map i).right :=
  MorphismProperty.of_isPushout (isPushout_addBasepoint_map i) hi

end TauCeti.PointedSSet
