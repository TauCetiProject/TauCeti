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

On underlying simplicial sets, the naturality square of the adjunction unit at any map `f : K ⟶ L`
is a pushout (`PointedSSet.isPushout_unit_addBasepoint`), so adjoining a disjoint basepoint
preserves monomorphisms and every cobase-change-stable class of morphisms of simplicial sets.

## Main definitions

* `PointedSSet.addBasepoint`: adjoin a disjoint basepoint to a simplicial set.
* `PointedSSet.addBasepointHomEquiv`: based maps from `K₊` are unpointed maps from `K`.
* `PointedSSet.addBasepointForgetAdjunction`: the adjunction `(-)₊ ⊣ forget`.
* `PointedSSet.isPushout_unit_addBasepoint`: the unit naturality square at `f : K ⟶ L` is a
  pushout on underlying simplicial sets.
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

/-- The hom-equivalence of `addBasepointForgetAdjunction` is `addBasepointHomEquiv`. -/
@[simp]
lemma addBasepointForgetAdjunction_homEquiv (K : SSet.{u}) (X : PointedSSet.{u}) :
    addBasepointForgetAdjunction.homEquiv K X = addBasepointHomEquiv K X := by
  rw [addBasepointForgetAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The unit of `(-)₊ ⊣ forget` embeds each simplex `x` as `some x`. -/
lemma addBasepointForgetAdjunction_unit_app_app (K : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (x : K.obj n) :
    (addBasepointForgetAdjunction.unit.app K).app n x = some x :=
  (rfl)

/-- On underlying simplicial sets, the naturality square of the unit of `(-)₊ ⊣ forget` at any map
`f : K ⟶ L` is a pushout: `(L₊)` is obtained from `(K₊)` and `L` by identifying `K` with its
unbased summand in `(K₊)`. -/
theorem isPushout_unit_addBasepoint {K L : SSet.{u}} (f : K ⟶ L) :
    IsPushout (addBasepointForgetAdjunction.unit.app K) f
      (addBasepoint.map f).right (addBasepointForgetAdjunction.unit.app L) where
  w := (addBasepointForgetAdjunction.unit.naturality f).symm
  isColimit' := ⟨Limits.PushoutCocone.IsColimit.mk _
    (fun s ↦
      { app n := ↾fun y ↦ y.elim (s.inl.app n none) (s.inr.app n)
        naturality n m g := by
          ext y
          cases y with
          | none => exact congr_hom (s.inl.naturality g) (none : Option (K.obj n))
          | some y => exact congr_hom (s.inr.naturality g) y })
    (fun s ↦ by
      ext n x
      cases x with
      | none => rfl
      | some x => exact (congr_hom (NatTrans.congr_app s.condition n) x).symm)
    (fun _ ↦ rfl)
    (fun s m h₁ h₂ ↦ by
      ext n y
      cases y with
      | none => exact congr_hom (NatTrans.congr_app h₁ n) (none : Option (K.obj n))
      | some y => exact congr_hom (NatTrans.congr_app h₂ n) y)⟩

/-- Adjoining a disjoint basepoint preserves every cobase-change-stable class of morphisms on
underlying simplicial sets. -/
lemma addBasepoint_map_right_mem_of_isStableUnderCobaseChange
    (W : MorphismProperty SSet.{u}) [W.IsStableUnderCobaseChange]
    {K L : SSet.{u}} {f : K ⟶ L} (hf : W f) :
    W (addBasepoint.map f).right :=
  W.of_isPushout (isPushout_unit_addBasepoint f) hf

/-- Adjoining a disjoint basepoint preserves monomorphisms on underlying simplicial sets. -/
instance mono_addBasepoint_map_right {K L : SSet.{u}} (f : K ⟶ L) [Mono f] :
    Mono (addBasepoint.map f).right := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  have hf : Function.Injective (f.app n) :=
    (mono_iff_injective (f.app n)).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance n)
  rw [mono_iff_injective]
  rintro (_ | x₁) (_ | x₂) h
  · rfl
  · cases h
  · cases h
  · exact congrArg some (hf (Option.some.inj h))

/-- Adjoining a disjoint basepoint preserves monomorphisms of pointed simplicial sets. -/
instance mono_addBasepoint_map {K L : SSet.{u}} (f : K ⟶ L) [Mono f] :
    Mono (addBasepoint.map f) :=
  forgetBasepoint.mono_of_mono_map (mono_addBasepoint_map_right f)

end TauCeti.PointedSSet
