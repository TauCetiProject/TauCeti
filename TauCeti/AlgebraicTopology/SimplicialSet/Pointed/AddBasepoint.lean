/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Basic

-- The degreewise formulas below compute through the native undercategory presentation.
import all TauCeti.AlgebraicTopology.SimplicialSet.Pointed.Basic

/-!
# Adjoining a disjoint basepoint to a simplicial set

The functor `K ↦ K₊` adjoins a disjoint basepoint degreewise to a simplicial set. It is left
adjoint to forgetting the basepoint of a pointed simplicial set: based maps `K₊ ⟶ X` are the
same as unpointed maps `K ⟶ X`.

On underlying simplicial sets, the naturality square of the adjunction unit `K ⟶ K₊` is a
pushout square (`PointedSSet.isPushout_addBasepointForgetAdjunction_unit`). Consequently,
adjoining a disjoint basepoint preserves every morphism property of simplicial sets that is
stable under cobase change, such as monomorphisms and anodyne extensions.

## Main definitions

* `PointedSSet.addBasepoint`: adjoin a disjoint basepoint to a simplicial set.
* `PointedSSet.addBasepointHomEquiv`: based maps from `K₊` are unpointed maps from `K`.
* `PointedSSet.addBasepointForgetAdjunction`: the adjunction `(-)₊ ⊣ forget`.
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

/-- Forget the basepoint of a pointed simplicial set. -/
abbrev forgetBasepoint : PointedSSet.{u} ⥤ SSet.{u} :=
  Under.forget _

/-- Adjoining a disjoint basepoint is left adjoint to forgetting the basepoint. -/
def addBasepointForgetAdjunction :
    addBasepoint ⊣ forgetBasepoint :=
  Adjunction.mkOfHomEquiv
    { homEquiv := addBasepointHomEquiv
      homEquiv_naturality_right := addBasepointHomEquiv_comp
      homEquiv_naturality_left_symm := fun f g ↦ by
        ext n x
        cases x <;> rfl }

/-- The hom-set bijection of `(-)₊ ⊣ forget` is `addBasepointHomEquiv`. -/
lemma addBasepointForgetAdjunction_homEquiv (K : SSet.{u}) (X : PointedSSet.{u}) :
    addBasepointForgetAdjunction.homEquiv K X = addBasepointHomEquiv K X := by
  rw [addBasepointForgetAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- Adjoining a disjoint basepoint is a left adjoint, hence preserves colimits of all sizes. -/
instance : addBasepoint.{u}.IsLeftAdjoint :=
  addBasepointForgetAdjunction.isLeftAdjoint

/-- Forgetting the basepoint of a pointed simplicial set is a right adjoint, hence preserves limits
of all sizes. -/
instance : forgetBasepoint.{u}.IsRightAdjoint :=
  addBasepointForgetAdjunction.isRightAdjoint

/-- The unit `K ⟶ K₊` of `(-)₊ ⊣ forget` sends every simplex `x` to `some x`. -/
@[simp]
lemma addBasepointForgetAdjunction_unit_app_app (K : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x : K.obj n) :
    dsimp% (addBasepointForgetAdjunction.unit.app K).app n x = some x := by
  rw [addBasepointForgetAdjunction, Adjunction.mkOfHomEquiv_unit_app]
  rfl

/-- For any map `f : K ⟶ L` of simplicial sets, the naturality square of the unit `K ⟶ K₊`
is a pushout square on underlying simplicial sets: `L₊` is obtained from `L` and `K₊` by
attaching the disjoint basepoint along `K`. -/
lemma isPushout_addBasepointForgetAdjunction_unit {K L : SSet.{u}} (f : K ⟶ L) :
    IsPushout f (addBasepointForgetAdjunction.unit.app K)
      (addBasepointForgetAdjunction.unit.app L) (addBasepoint.map f).right where
  w := addBasepointForgetAdjunction.unit.naturality f
  isColimit' := ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun s ↦
      { app := fun n ↦ ↾fun x ↦ x.elim (s.inr.app n none) (s.inl.app n)
        naturality := fun n m g ↦ by
          ext x
          cases x with
          | none => exact congr_hom (s.inr.naturality g) (none : Option (K.obj n))
          | some y => exact congr_hom (s.inl.naturality g) y })
    (fun _ ↦ by
      ext _ _
      rfl)
    (fun s ↦ by
      ext n x
      cases x with
      | none => rfl
      | some x => exact congr_hom (NatTrans.congr_app s.condition n) x)
    (fun s m hl hr ↦ by
      ext n x
      cases x with
      | none => exact congr_hom (NatTrans.congr_app hr n) (none : Option (K.obj n))
      | some y => exact congr_hom (NatTrans.congr_app hl n) y)⟩

/-- Adjoining a disjoint basepoint preserves any morphism property of simplicial sets that is
stable under cobase change. -/
lemma addBasepoint_map_right_mem (W : MorphismProperty SSet.{u})
    [W.IsStableUnderCobaseChange] {K L : SSet.{u}} {f : K ⟶ L} (hf : W f) :
    W (addBasepoint.map f).right :=
  W.of_isPushout (isPushout_addBasepointForgetAdjunction_unit f).flip hf

/-- Adjoining a disjoint basepoint preserves monomorphisms on underlying simplicial sets. -/
instance mono_addBasepoint_map_right {K L : SSet.{u}} (f : K ⟶ L) [Mono f] :
    Mono (addBasepoint.map f).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  exact Option.map_injective ((mono_iff_injective (f.app n)).1 inferInstance)

end TauCeti.PointedSSet
