/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Quotient
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Homotopy.Basic

/-!
# The homotopy category of paracompact Hausdorff spaces

`TauCeti.ParacompactHomotopyCat`, written `HoPara`, is the `CategoryTheory.Quotient` of the full
subcategory of `TopCat` on the paracompact Hausdorff spaces (`TauCeti.isParacompactT2`) by
homotopy of continuous maps. Its morphisms are the homotopy classes of continuous maps
(`TauCeti.ParacompactHomotopyCat.homMk`, `homMk_surjective`, `homMk_eq_homMk_iff`).

## Main definitions

* `TauCeti.isParacompactT2`: the paracompact Hausdorff spaces.
* `TauCeti.paracompactHomotopicRel`: homotopy of maps, a congruence.
* `TauCeti.ParacompactHomotopyCat`: the homotopy category.
* `TauCeti.ParacompactHomotopyCat.homMk`: the homotopy class of a continuous map.
* `TauCeti.ParacompactHomotopyCat.homEquivQuotient`: morphisms are the free homotopy classes.

## Main results

* `TauCeti.ParacompactHomotopyCat.homMk_surjective`: every morphism is a homotopy class.
* `TauCeti.ParacompactHomotopyCat.homMk_eq_homMk_iff`: two maps have the same class iff they are
  homotopic.
* `TauCeti.ParacompactHomotopyCat.homMk_id`, `TauCeti.ParacompactHomotopyCat.homMk_comp`: `homMk`
  is functorial.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

/-- The paracompact Hausdorff spaces. -/
def isParacompactT2 : ObjectProperty TopCat.{u} :=
  fun X ↦ ParacompactSpace X ∧ T2Space X

theorem isParacompactT2_iff {X : TopCat.{u}} :
    isParacompactT2 X ↔ ParacompactSpace X ∧ T2Space X :=
  Iff.rfl

instance (X : isParacompactT2.{u}.FullSubcategory) : ParacompactSpace X.obj :=
  (isParacompactT2_iff.1 X.property).1

instance (X : isParacompactT2.{u}.FullSubcategory) : T2Space X.obj :=
  (isParacompactT2_iff.1 X.property).2

/-- Homotopy of continuous maps between paracompact Hausdorff spaces. -/
def paracompactHomotopicRel : HomRel isParacompactT2.{u}.FullSubcategory :=
  fun _ _ f g ↦ ContinuousMap.Homotopic f.hom.hom g.hom.hom

theorem paracompactHomotopicRel_iff {X Y : isParacompactT2.{u}.FullSubcategory} {f g : X ⟶ Y} :
    paracompactHomotopicRel f g ↔ ContinuousMap.Homotopic f.hom.hom g.hom.hom :=
  Iff.rfl

instance : Congruence paracompactHomotopicRel.{u} where
  equivalence := ⟨fun f ↦ .refl f.hom.hom, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩
  comp_left f _ _ h := h.comp (.refl f.hom.hom)
  comp_right g h := (ContinuousMap.Homotopic.refl g.hom.hom).comp h

/-- **The homotopy category of paracompact Hausdorff spaces**, `HoPara`: paracompact Hausdorff
spaces and homotopy classes of continuous maps. -/
abbrev ParacompactHomotopyCat : Type (u + 1) :=
  CategoryTheory.Quotient paracompactHomotopicRel.{u}

namespace ParacompactHomotopyCat

/-- A paracompact Hausdorff space as an object of the homotopy category. -/
abbrev of (X : TopCat.{u}) [ParacompactSpace X] [T2Space X] : ParacompactHomotopyCat.{u} :=
  ⟨⟨X, isParacompactT2_iff.2 ⟨‹_›, ‹_›⟩⟩⟩

/-- The homotopy class of a continuous map. -/
abbrev homMk {X Y : ParacompactHomotopyCat.{u}} (f : C(X.as.obj, Y.as.obj)) : X ⟶ Y :=
  (CategoryTheory.Quotient.functor _).map (ObjectProperty.homMk (TopCat.ofHom f))

/-- Every morphism of `HoPara` is the homotopy class of a continuous map. -/
theorem homMk_surjective {X Y : ParacompactHomotopyCat.{u}} :
    Function.Surjective (homMk : C(X.as.obj, Y.as.obj) → (X ⟶ Y)) := fun g ↦ by
  obtain ⟨f, rfl⟩ := (CategoryTheory.Quotient.functor paracompactHomotopicRel).map_surjective g
  exact ⟨f.hom.hom, rfl⟩

/-- Two continuous maps have the same homotopy class iff they are homotopic. -/
@[simp]
theorem homMk_eq_homMk_iff {X Y : ParacompactHomotopyCat.{u}} {f g : C(X.as.obj, Y.as.obj)} :
    homMk f = homMk g ↔ f.Homotopic g :=
  CategoryTheory.Quotient.functor_map_eq_iff _ _ _

/-- The class of the identity map is the identity. -/
@[simp]
theorem homMk_id (X : ParacompactHomotopyCat.{u}) : homMk (ContinuousMap.id X.as.obj) = 𝟙 X :=
  (CategoryTheory.Quotient.functor _).map_id X.as

/-- The class of a composite is the composite of the classes. -/
@[simp]
theorem homMk_comp {X Y Z : ParacompactHomotopyCat.{u}} (f : C(X.as.obj, Y.as.obj))
    (g : C(Y.as.obj, Z.as.obj)) : homMk (g.comp f) = homMk f ≫ homMk g :=
  (CategoryTheory.Quotient.functor _).map_comp
    (ObjectProperty.homMk (TopCat.ofHom f)) (ObjectProperty.homMk (TopCat.ofHom g))

/-- The morphisms `X ⟶ Y` of `HoPara` are the free homotopy classes of continuous maps. -/
noncomputable def homEquivQuotient (X Y : ParacompactHomotopyCat.{u}) :
    Quotient (⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩ :
      Setoid C(X.as.obj, Y.as.obj)) ≃ (X ⟶ Y) :=
  Equiv.ofBijective (Quotient.lift homMk fun _ _ h ↦ homMk_eq_homMk_iff.2 h)
    ⟨Quotient.ind₂ fun _ _ h ↦ Quotient.sound (homMk_eq_homMk_iff.1 h),
      fun g ↦ let ⟨f, hf⟩ := homMk_surjective g; ⟨Quotient.mk _ f, hf⟩⟩

@[simp]
theorem homEquivQuotient_mk {X Y : ParacompactHomotopyCat.{u}} (f : C(X.as.obj, Y.as.obj)) :
    homEquivQuotient X Y (Quotient.mk _ f) = homMk f :=
  (rfl)

@[simp]
theorem homEquivQuotient_symm_homMk {X Y : ParacompactHomotopyCat.{u}}
    (f : C(X.as.obj, Y.as.obj)) :
    (homEquivQuotient X Y).symm (homMk f) = Quotient.mk _ f :=
  (homEquivQuotient X Y).symm_apply_eq.2 (homEquivQuotient_mk f).symm

end ParacompactHomotopyCat

end TauCeti
