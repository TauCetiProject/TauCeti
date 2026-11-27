/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DoubleCategory.Implicit.Basic
public import TauCeti.CategoryTheory.DoubleCategory.Functor

/-!
# Generator-preserving implicit double functors

An implicit double functor is a strict double functor between implicit double categories
together with horizontal and vertical generator maps over its common object map. Its edge
maps send singleton paths to the specified singleton paths. Functoriality then forces the
action on every path to be Mathlib's `Prefunctor.mapPath` of the generator map.

`ImplicitDoubleFunctor` reuses the cell map and preservation laws of `StrictDoubleFunctor`.
Its generator maps are determined by the underlying strict double functor, as expressed by
`ImplicitDoubleFunctor.ext`. Identity and composition preserve generators and satisfy the
category laws as equalities of implicit double functors. No representation choices are needed.

The implicit presentation follows A. D. Fairbanks and M. Shulman, *Doubly weak double
categories*, Applied Categorical Structures **34** (2026), article 26, Definitions 3.1–3.3.
-/

public section

universe s₁ s₂ s₃ s₄ u₁ u₂ u₃ u₄ h₁ h₂ h₃ h₄ v₁ v₂ v₃ v₄

namespace TauCeti

open CategoryTheory StrictDoubleCategory DoubleCategoryStruct

variable {O₁ : Type u₁} {H₁ : Quiver.{h₁} O₁} {V₁ : Quiver.{v₁} O₁}
  {O₂ : Type u₂} {H₂ : Quiver.{h₂} O₂} {V₂ : Quiver.{v₂} O₂}
  {O₃ : Type u₃} {H₃ : Quiver.{h₃} O₃} {V₃ : Quiver.{v₃} O₃}

/-- A generator-preserving implicit double functor: a strict double functor with maps of
horizontal and vertical generators whose singleton paths are their images under the edge maps.
The underlying strict double functor supplies preservation of both identities and pastings. -/
structure ImplicitDoubleFunctor (D₁ : ImplicitDoubleCategory.{s₁} O₁ H₁ V₁)
    (D₂ : ImplicitDoubleCategory.{s₂} O₂ H₂ V₂) extends StrictDoubleFunctor D₁ D₂ where
  /-- The horizontal generator map. -/
  hGenerator {a b : O₁} : @Quiver.Hom O₁ H₁ a b → @Quiver.Hom O₂ H₂ (obj a) (obj b)
  /-- The vertical generator map. -/
  vGenerator {a b : O₁} : @Quiver.Hom O₁ V₁ a b → @Quiver.Hom O₂ V₂ (obj a) (obj b)
  /-- The horizontal edge map extends the generator map on singleton paths. -/
  hMap_toPath {a b : O₁} (f : @Quiver.Hom O₁ H₁ a b) :
    hMap (@Quiver.Hom.toPath O₁ H₁ a b f) = @Quiver.Hom.toPath O₂ H₂ _ _ (hGenerator f)
  /-- The vertical edge map extends the generator map on singleton paths. -/
  vMap_toPath {a b : O₁} (f : @Quiver.Hom O₁ V₁ a b) :
    vMap (@Quiver.Hom.toPath O₁ V₁ a b f) = @Quiver.Hom.toPath O₂ V₂ _ _ (vGenerator f)

namespace ImplicitDoubleFunctor

variable {D₁ : ImplicitDoubleCategory.{s₁} O₁ H₁ V₁}
  {D₂ : ImplicitDoubleCategory.{s₂} O₂ H₂ V₂}
  {D₃ : ImplicitDoubleCategory.{s₃} O₃ H₃ V₃}

/-- The prefunctor on horizontal generating quivers. -/
abbrev hPrefunctor (F : ImplicitDoubleFunctor D₁ D₂) : @Prefunctor O₁ H₁ O₂ H₂ :=
  @Prefunctor.mk O₁ H₁ O₂ H₂ F.obj (fun {_ _} f ↦ F.hGenerator f)

/-- The prefunctor on vertical generating quivers. -/
abbrev vPrefunctor (F : ImplicitDoubleFunctor D₁ D₂) : @Prefunctor O₁ V₁ O₂ V₂ :=
  @Prefunctor.mk O₁ V₁ O₂ V₂ F.obj (fun {_ _} f ↦ F.vGenerator f)

@[simp]
theorem hPrefunctor_obj (F : ImplicitDoubleFunctor D₁ D₂) (a : O₁) :
    @Prefunctor.obj O₁ H₁ O₂ H₂ F.hPrefunctor a = F.obj a := rfl

@[simp]
theorem hPrefunctor_map (F : ImplicitDoubleFunctor D₁ D₂) {a b : O₁}
    (f : @Quiver.Hom O₁ H₁ a b) :
    @Prefunctor.map O₁ H₁ O₂ H₂ F.hPrefunctor a b f = F.hGenerator f := rfl

@[simp]
theorem vPrefunctor_obj (F : ImplicitDoubleFunctor D₁ D₂) (a : O₁) :
    @Prefunctor.obj O₁ V₁ O₂ V₂ F.vPrefunctor a = F.obj a := rfl

@[simp]
theorem vPrefunctor_map (F : ImplicitDoubleFunctor D₁ D₂) {a b : O₁}
    (f : @Quiver.Hom O₁ V₁ a b) :
    @Prefunctor.map O₁ V₁ O₂ V₂ F.vPrefunctor a b f = F.vGenerator f := rfl

/-- The horizontal path map is the extension of the horizontal generator map. -/
@[simp]
theorem hMap_eq_mapPath (F : ImplicitDoubleFunctor D₁ D₂) {a b : O₁}
    (p : @Quiver.Path O₁ H₁ a b) :
    F.hMap p = @Prefunctor.mapPath O₁ H₁ O₂ H₂ F.hPrefunctor a b p := by
  let := H₁
  let := H₂
  induction p with
  | nil => exact F.hMap_id _
  | cons p f ih =>
    simpa only [edgeComp, Quiver.pathCategory_comp, Quiver.Path.comp_toPath_eq_cons,
      Prefunctor.mapPath_cons, hPrefunctor_map] using
      F.hMap_comp p (@Quiver.Hom.toPath O₁ H₁ _ _ f) |>.trans
        (congrArg₂ (edgeComp (pathCategory O₂ H₂)) ih (F.hMap_toPath f))

/-- The vertical path map is the extension of the vertical generator map. -/
@[simp]
theorem vMap_eq_mapPath (F : ImplicitDoubleFunctor D₁ D₂) {a b : O₁}
    (p : @Quiver.Path O₁ V₁ a b) :
    F.vMap p = @Prefunctor.mapPath O₁ V₁ O₂ V₂ F.vPrefunctor a b p := by
  let := V₁
  let := V₂
  induction p with
  | nil => exact F.vMap_id _
  | cons p f ih =>
    simpa only [edgeComp, Quiver.pathCategory_comp, Quiver.Path.comp_toPath_eq_cons,
      Prefunctor.mapPath_cons, vPrefunctor_map] using
      F.vMap_comp p (@Quiver.Hom.toPath O₁ V₁ _ _ f) |>.trans
        (congrArg₂ (edgeComp (pathCategory O₂ V₂)) ih (F.vMap_toPath f))

/-- An implicit double functor has no extra choice of generator maps once its underlying
strict double functor is fixed. -/
@[ext]
theorem ext {F G : ImplicitDoubleFunctor D₁ D₂}
    (h : F.toStrictDoubleFunctor = G.toStrictDoubleFunctor) : F = G := by
  rcases F with ⟨F, Fh, Fv, hFh, hFv⟩
  rcases G with ⟨G, Gh, Gv, hGh, hGv⟩
  cases h
  have hh : @Fh = @Gh := by
    let := H₂
    funext a b f
    exact eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons ((hFh f).symm.trans (hGh f)))
  have hv : @Fv = @Gv := by
    let := V₂
    funext a b f
    exact eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons ((hFv f).symm.trans (hGv f)))
  cases hh
  cases hv
  rfl

variable (D₁) in
/-- The identity implicit double functor. Its body is exposed so that the object endpoints
of its generator and cell maps compute. -/
@[expose]
def id : ImplicitDoubleFunctor D₁ D₁ where
  toStrictDoubleFunctor := StrictDoubleFunctor.id D₁
  hGenerator f := f
  vGenerator f := f
  hMap_toPath _ := rfl
  vMap_toPath _ := rfl

@[simp]
theorem id_toStrictDoubleFunctor : (id D₁).toStrictDoubleFunctor = StrictDoubleFunctor.id D₁ :=
  rfl

@[simp]
theorem id_hGenerator {a b : O₁} (f : @Quiver.Hom O₁ H₁ a b) :
    (id D₁).hGenerator f = f := rfl

@[simp]
theorem id_vGenerator {a b : O₁} (f : @Quiver.Hom O₁ V₁ a b) :
    (id D₁).vGenerator f = f := rfl

/-- Composition of implicit double functors, in diagrammatic order. Its body is exposed so
that the object endpoints of its generator and cell maps compute. -/
@[expose]
def comp (F : ImplicitDoubleFunctor D₁ D₂) (G : ImplicitDoubleFunctor D₂ D₃) :
    ImplicitDoubleFunctor D₁ D₃ where
  toStrictDoubleFunctor := F.toStrictDoubleFunctor.comp G.toStrictDoubleFunctor
  hGenerator f := G.hGenerator (F.hGenerator f)
  vGenerator f := G.vGenerator (F.vGenerator f)
  hMap_toPath f := by simp
  vMap_toPath f := by simp

@[simp]
theorem comp_toStrictDoubleFunctor (F : ImplicitDoubleFunctor D₁ D₂)
    (G : ImplicitDoubleFunctor D₂ D₃) :
    (F.comp G).toStrictDoubleFunctor = F.toStrictDoubleFunctor.comp G.toStrictDoubleFunctor :=
  rfl

@[simp]
theorem comp_hGenerator (F : ImplicitDoubleFunctor D₁ D₂) (G : ImplicitDoubleFunctor D₂ D₃)
    {a b : O₁} (f : @Quiver.Hom O₁ H₁ a b) :
    (F.comp G).hGenerator f = G.hGenerator (F.hGenerator f) := rfl

@[simp]
theorem comp_vGenerator (F : ImplicitDoubleFunctor D₁ D₂) (G : ImplicitDoubleFunctor D₂ D₃)
    {a b : O₁} (f : @Quiver.Hom O₁ V₁ a b) :
    (F.comp G).vGenerator f = G.vGenerator (F.vGenerator f) := rfl

@[simp]
theorem id_comp (F : ImplicitDoubleFunctor D₁ D₂) : (id D₁).comp F = F :=
  ext (StrictDoubleFunctor.id_comp _)

@[simp]
theorem comp_id (F : ImplicitDoubleFunctor D₁ D₂) : F.comp (id D₂) = F :=
  ext (StrictDoubleFunctor.comp_id _)

/-- Composition of implicit double functors is associative. -/
theorem comp_assoc {O₄ : Type u₄} {H₄ : Quiver.{h₄} O₄} {V₄ : Quiver.{v₄} O₄}
    {D₄ : ImplicitDoubleCategory.{s₄} O₄ H₄ V₄} (F : ImplicitDoubleFunctor D₁ D₂)
    (G : ImplicitDoubleFunctor D₂ D₃) (K : ImplicitDoubleFunctor D₃ D₄) :
    (F.comp G).comp K = F.comp (G.comp K) :=
  ext (StrictDoubleFunctor.comp_assoc _ _ _)

end ImplicitDoubleFunctor

end TauCeti
