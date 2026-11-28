/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Expansion.Basic
public import TauCeti.CategoryTheory.DoubleCategory.Implicit.Functor

/-!
# Functorial expansion of strict double categories

A strict double functor extends to the path expansions by applying its edge maps to each
generator. Its action on a path cell is its original cell map, transported along naturality
of path evaluation. This construction preserves both pastings and identities, and preserves
identity and composite double functors as equalities of generator-preserving functors.
Double isomorphisms therefore expand to double isomorphisms, with the original inverse laws
holding on arbitrary path cells.

The expansion follows A. D. Fairbanks and M. Shulman, *Doubly weak double categories*,
Applied Categorical Structures **34** (2026), article 26; arXiv:2506.23651, Definition 3.12.
Path evaluation and its naturality are Mathlib's `composePath` and
`CategoryTheory.Quiv.pathComposition_naturality`.
-/

public section

universe s₁ s₂ s₃ u₁ u₂ u₃ h₁ h₂ h₃ v₁ v₂ v₃

namespace TauCeti

open CategoryTheory StrictDoubleCategory DoubleCategoryStruct

variable {O₁ : Type u₁} {H₁ : Category.{h₁} O₁} {V₁ : Category.{v₁} O₁}
  {O₂ : Type u₂} {H₂ : Category.{h₂} O₂} {V₂ : Category.{v₂} O₂}
  {O₃ : Type u₃} {H₃ : Category.{h₃} O₃} {V₃ : Category.{v₃} O₃}
  {D₁ : StrictDoubleCategory.{s₁} O₁ H₁ V₁}
  {D₂ : StrictDoubleCategory.{s₂} O₂ H₂ V₂}
  {D₃ : StrictDoubleCategory.{s₃} O₃ H₃ V₃}

namespace StrictDoubleFunctor

/-- Mapping horizontal edges commutes with evaluating a path. -/
theorem hMap_composePath (F : StrictDoubleFunctor D₁ D₂) {a b : O₁}
    (p : Edge (pathCategory O₁ H₁.toQuiver) a b) :
    F.hMap (@composePath O₁ H₁ _ _ p) = @composePath O₂ H₂ _ _
      (@Prefunctor.mapPath O₁ H₁.toQuiver O₂ H₂.toQuiver
        (@Prefunctor.mk O₁ H₁.toQuiver O₂ H₂.toQuiver F.obj
          (fun {_ _} f ↦ F.hMap f)) _ _ p) :=
  (eq_of_heq (@Functor.hcongr_hom O₁ (pathCategory O₁ H₁.toQuiver) O₂ H₂ _ _
    (@Quiv.pathComposition_naturality O₁ O₂ H₁ H₂ F.hFunctor) _ _ p)).symm

/-- Mapping vertical edges commutes with evaluating a path. -/
theorem vMap_composePath (F : StrictDoubleFunctor D₁ D₂) {a b : O₁}
    (p : Edge (pathCategory O₁ V₁.toQuiver) a b) :
    F.vMap (@composePath O₁ V₁ _ _ p) = @composePath O₂ V₂ _ _
      (@Prefunctor.mapPath O₁ V₁.toQuiver O₂ V₂.toQuiver
        (@Prefunctor.mk O₁ V₁.toQuiver O₂ V₂.toQuiver F.obj
          (fun {_ _} f ↦ F.vMap f)) _ _ p) :=
  (eq_of_heq (@Functor.hcongr_hom O₁ (pathCategory O₁ V₁.toQuiver) O₂ V₂ _ _
    (@Quiv.pathComposition_naturality O₁ O₂ V₁ V₂ F.vFunctor) _ _ p)).symm

/-- Apply a strict double functor to every generator of the path expansions. Its cell map
is the original map with boundary transports supplied by naturality of path evaluation.
The body is exposed so that the object endpoints of the path and cell maps compute. -/
@[expose]
def expand (F : StrictDoubleFunctor D₁ D₂) : ImplicitDoubleFunctor D₁.expand D₂.expand where
  obj := F.obj
  hMap := @Prefunctor.mapPath O₁ H₁.toQuiver O₂ H₂.toQuiver
    (@Prefunctor.mk O₁ H₁.toQuiver O₂ H₂.toQuiver F.obj (fun {_ _} f ↦ F.hMap f))
  hMap_id _ := rfl
  hMap_comp p q := @Prefunctor.mapPath_comp O₁ H₁.toQuiver O₂ H₂.toQuiver
    (@Prefunctor.mk O₁ H₁.toQuiver O₂ H₂.toQuiver F.obj
      (fun {_ _} f ↦ F.hMap f)) _ _ p _ q
  vMap := @Prefunctor.mapPath O₁ V₁.toQuiver O₂ V₂.toQuiver
    (@Prefunctor.mk O₁ V₁.toQuiver O₂ V₂.toQuiver F.obj (fun {_ _} f ↦ F.vMap f))
  vMap_id _ := rfl
  vMap_comp p q := @Prefunctor.mapPath_comp O₁ V₁.toQuiver O₂ V₂.toQuiver
    (@Prefunctor.mk O₁ V₁.toQuiver O₂ V₂.toQuiver F.obj
      (fun {_ _} f ↦ F.vMap f)) _ _ p _ q
  map {a b c d p q l r} α :=
    Cell.cast (D := D₂.toDoubleCategoryStruct) (F.hMap_composePath p) (F.hMap_composePath q)
      (F.vMap_composePath l) (F.vMap_composePath r) (F.map α)
  -- Path evaluation and the explicit edge categories are semireducible.
  -- `erw` matches the original operations inside their expanded cell families;
  -- unfolding the expansion then lets the existing transport laws normalize the casts.
  map_hId f := by
    erw [D₂.expand_cast, F.map_hId]
    erw [Cell.cast_cast, cast_hId]
    rfl
  map_vId f := by
    erw [D₂.expand_cast, F.map_vId]
    erw [Cell.cast_cast, cast_vId]
    rfl
  map_hComp α β := by
    erw [D₂.expand_cast, D₁.expand_hComp, F.map_cast, F.map_hComp,
      D₂.expand_hComp, hComp_cast_cast]
    dsimp only [StrictDoubleCategory.expand, DoubleCategoryStruct.expand]
    simp only [Cell.cast_cast]
  map_vComp α β := by
    erw [D₂.expand_cast, D₁.expand_vComp, F.map_cast, F.map_vComp,
      D₂.expand_vComp, vComp_cast_cast]
    dsimp only [StrictDoubleCategory.expand, DoubleCategoryStruct.expand]
    simp only [Cell.cast_cast]
  hGenerator := F.hMap
  vGenerator := F.vMap
  hMap_toPath _ := rfl
  vMap_toPath _ := rfl

@[simp]
theorem expand_obj (F : StrictDoubleFunctor D₁ D₂) (a : O₁) : F.expand.obj a = F.obj a :=
  rfl

@[simp]
theorem expand_hGenerator (F : StrictDoubleFunctor D₁ D₂) {a b : O₁} (f : Edge H₁ a b) :
    F.expand.hGenerator f = F.hMap f := rfl

@[simp]
theorem expand_vGenerator (F : StrictDoubleFunctor D₁ D₂) {a b : O₁} (f : Edge V₁ a b) :
    F.expand.vGenerator f = F.vMap f := rfl

@[simp]
theorem expand_hPrefunctor (F : StrictDoubleFunctor D₁ D₂) :
    F.expand.hPrefunctor = F.hFunctor.toPrefunctor := rfl

@[simp]
theorem expand_vPrefunctor (F : StrictDoubleFunctor D₁ D₂) :
    F.expand.vPrefunctor = F.vFunctor.toPrefunctor := rfl

/-- The expanded cell map is the original cell map transported on evaluated boundaries. -/
@[simp]
theorem expand_map (F : StrictDoubleFunctor D₁ D₂) {a b c d : O₁}
    {p : Edge (pathCategory O₁ H₁.toQuiver) a b}
    {q : Edge (pathCategory O₁ H₁.toQuiver) c d}
    {l : Edge (pathCategory O₁ V₁.toQuiver) a c}
    {r : Edge (pathCategory O₁ V₁.toQuiver) b d} (α : D₁.expand.Cell p q l r) :
    F.expand.map α = Cell.cast (D := D₂.toDoubleCategoryStruct)
      (F.hMap_composePath p) (F.hMap_composePath q)
      (F.vMap_composePath l) (F.vMap_composePath r) (F.map α) :=
  (rfl)

/-- Expanding the identity gives the identity generator-preserving functor. -/
@[simp]
theorem expand_id : (id D₁).expand = ImplicitDoubleFunctor.id D₁.expand := by
  apply ImplicitDoubleFunctor.ext
  apply hext
  · intro a; rfl
  · intro a b p
    exact heq_of_eq (@Prefunctor.mapPath_id O₁ H₁.toQuiver _ _ p)
  · intro a b p
    exact heq_of_eq (@Prefunctor.mapPath_id O₁ V₁.toQuiver _ _ p)
  · intro a b c d p q l r α
    dsimp only [expand, id, ImplicitDoubleFunctor.id]
    exact Cell.cast_heq (D := D₁.toDoubleCategoryStruct) _ _ _ _ α

/-- Expansion preserves composition as equality of generator-preserving double functors. -/
@[simp]
theorem expand_comp (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) :
    (F.comp G).expand = F.expand.comp G.expand := by
  apply ImplicitDoubleFunctor.ext
  apply hext
  · intro a; rfl
  · intro a b p
    exact heq_of_eq (@Prefunctor.mapPath_comp_apply O₁ H₁.toQuiver O₂ H₂.toQuiver
      F.hFunctor.toPrefunctor O₃ H₃.toQuiver G.hFunctor.toPrefunctor _ _ p)
  · intro a b p
    exact heq_of_eq (@Prefunctor.mapPath_comp_apply O₁ V₁.toQuiver O₂ V₂.toQuiver
      F.vFunctor.toPrefunctor O₃ V₃.toQuiver G.vFunctor.toPrefunctor _ _ p)
  · intro a b c d p q l r α
    dsimp only [expand, comp, ImplicitDoubleFunctor.comp]
    erw [G.map_cast]
    exact (Cell.cast_heq _ _ _ _ _).trans
      ((Cell.cast_heq _ _ _ _ _).trans (Cell.cast_heq _ _ _ _ _)).symm

end StrictDoubleFunctor

namespace StrictDoubleIso

/-- Expanding both directions of a double isomorphism gives a double isomorphism on paths. -/
def expand (e : StrictDoubleIso D₁ D₂) : StrictDoubleIso D₁.expand D₂.expand where
  hom := e.hom.expand.toStrictDoubleFunctor
  inv := e.inv.expand.toStrictDoubleFunctor
  hom_inv_id := by
    rw [← ImplicitDoubleFunctor.comp_toStrictDoubleFunctor,
      ← StrictDoubleFunctor.expand_comp, e.hom_inv_id, StrictDoubleFunctor.expand_id]
    rfl
  inv_hom_id := by
    rw [← ImplicitDoubleFunctor.comp_toStrictDoubleFunctor,
      ← StrictDoubleFunctor.expand_comp, e.inv_hom_id, StrictDoubleFunctor.expand_id]
    rfl

@[simp]
theorem expand_hom (e : StrictDoubleIso D₁ D₂) :
    e.expand.hom = e.hom.expand.toStrictDoubleFunctor := (rfl)

@[simp]
theorem expand_inv (e : StrictDoubleIso D₁ D₂) :
    e.expand.inv = e.inv.expand.toStrictDoubleFunctor := (rfl)

@[simp]
theorem expand_refl : (refl D₁).expand = refl D₁.expand := by
  apply ext
  simp

@[simp]
theorem expand_symm (e : StrictDoubleIso D₁ D₂) : e.symm.expand = e.expand.symm := by
  apply ext
  rfl

/-- Expansion preserves composition of double isomorphisms. -/
@[simp]
theorem expand_trans (e : StrictDoubleIso D₁ D₂) (e' : StrictDoubleIso D₂ D₃) :
    (e.trans e').expand = e.expand.trans e'.expand := by
  apply ext
  simp

end StrictDoubleIso

end TauCeti
