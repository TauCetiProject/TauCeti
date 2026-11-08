/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import TauCeti.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Sections and their coefficient limits

A section of a Grothendieck construction chooses an object over each base object
and compatible transport arrows. Its morphisms are natural transformations over
the identity of the base. If the fibers are groupoids, these section morphisms
are invertible, even when the base is not a groupoid.

A represented action on the total category restricts to a coefficient diagram
along each section. Taking its limit makes completed labels act by isomorphisms
on completed coefficient objects. Apply `Functor.mapIso` to a label isomorphism
or `Functor.mapAut` to the automorphism group of a section. Mathlib's `limMap_π`
computes the action at every base object; functoriality supplies identity and composition.

Construct sections with `Functor.Fiber.mk` from a functor whose composite with the
projection is the identity. `Section.homMk` constructs a completed label from a
natural transformation satisfying the corresponding base identity.

The section category uses Mathlib's `Functor.Fiber` of the postcomposition
functor, rather than a separate encoding of transport coherence. Coefficient
maps and their limits use `whiskeringRight`, `limMap` and `Functor.mapAut`.
No faithfulness of the represented action is required.

Adapted from `Mei/CategoryTheory/Grothendieck/Section.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `68536122a97fed8e87bc6870b9427151971b9ab2` (Apache 2.0).
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Grothendieck

universe v u w z v' u'

namespace TauCeti.CategoryTheory.Grothendieck

variable {D : Type u} [Category.{v} D] (C : D ⥤ Cat.{w, z})

/-- Sections of the projection to the base, with natural transformations over its identity. -/
abbrev Section : Type _ :=
  Functor.Fiber ((whiskeringRight D (Grothendieck C) D).obj (forget C)) (𝟭 D)

namespace Section

variable {C}

/-- The underlying functor of a section. -/
abbrev toFunctor (s : Section C) : D ⥤ Grothendieck C :=
  Functor.Fiber.fiberInclusion.obj s

/-- A section is a right inverse to the projection. -/
@[simp]
theorem toFunctor_comp_forget (s : Section C) : s.toFunctor ⋙ forget C = 𝟭 D :=
  s.property

/-- The underlying natural transformation of a morphism of sections. -/
abbrev hom {s t : Section C} (α : s ⟶ t) : s.toFunctor ⟶ t.toFunctor :=
  Functor.Fiber.fiberInclusion.map α

/-- The underlying transformation of an identity section morphism is the identity. -/
@[simp↓]
theorem hom_id (s : Section C) : hom (𝟙 s) = 𝟙 s.toFunctor := (rfl)

/-- The underlying transformation preserves composition of section morphisms. -/
@[simp↓, reassoc]
theorem hom_comp {s t r : Section C} (α : s ⟶ t) (β : t ⟶ r) :
    hom (α ≫ β) = hom α ≫ hom β := (rfl)

/-- A morphism of sections lies over the identity transformation of the base. -/
theorem hom_over {s t : Section C} (α : s ⟶ t) :
    whiskerRight (hom α) (forget C) =
      eqToHom s.toFunctor_comp_forget ≫ eqToHom t.toFunctor_comp_forget.symm := by
  have := α.property
  simpa using IsHomLift.fac'
    ((whiskeringRight D (Grothendieck C) D).obj (forget C)) (𝟙 (𝟭 D)) (hom α)

/-- Every component of a section morphism projects to an isomorphism of the base. -/
instance hom_app_base_isIso {s t : Section C} (α : s ⟶ t) (d : D) :
    IsIso ((hom α).app d).base := by
  have h := hom_over α
  have : IsIso (whiskerRight (hom α) (forget C)) := by
    rw [h]
    infer_instance
  -- The projection formula also identifies the dependent endpoints of the component.
  convert (inferInstance : IsIso ((whiskerRight (hom α) (forget C)).app d)) using 1 <;>
    simp only [Functor.comp_obj, forget_obj, whiskerRight_app, forget_map]
  rfl

/-- Morphisms of sections are determined by their components. -/
@[ext]
theorem hom_ext {s t : Section C} {α β : s ⟶ t}
    (h : ∀ d, (hom α).app d = (hom β).app d) : α = β := by
  apply Functor.Fiber.hom_ext
  exact NatTrans.ext (funext h)

/-- A natural transformation satisfying the base identity gives a morphism of sections. -/
def homMk {s t : Section C} (α : s.toFunctor ⟶ t.toFunctor)
    (hα : whiskerRight α (forget C) =
      eqToHom s.toFunctor_comp_forget ≫ eqToHom t.toFunctor_comp_forget.symm) : s ⟶ t :=
  ⟨α, IsHomLift.of_fac'
    ((whiskeringRight D (Grothendieck C) D).obj (forget C)) (𝟙 (𝟭 D)) α
    s.toFunctor_comp_forget t.toFunctor_comp_forget (by simpa using hα)⟩

@[simp]
theorem hom_homMk {s t : Section C} (α : s.toFunctor ⟶ t.toFunctor) (hα) :
    hom (homMk α hα) = α := (rfl)

/-- Sections of a groupoid-valued diagram form a groupoid. -/
instance [∀ d, IsGroupoid (C.obj d)] : IsGroupoid (Section C) where
  all_isIso {s t} α := by
    have (d : D) : IsIso ((hom α).app d) :=
      (Grothendieck.isoMk (asIso ((hom α).app d).base)
        (asIso ((hom α).app d).fiber)).isIso_hom
    have : IsIso (hom α) := NatIso.isIso_of_isIso_app _
    exact isIso_of_reflects_iso α Functor.Fiber.fiberInclusion

variable {V : Type u'} [Category.{v'} V] (A : Grothendieck C ⥤ V)

/-- The coefficient diagrams obtained by restricting a represented action to sections. -/
abbrev coefficientDiagram : Section C ⥤ (D ⥤ V) :=
  Functor.Fiber.fiberInclusion ⋙ (whiskeringRight D (Grothendieck C) V).obj A

@[simp]
theorem coefficientDiagram_obj (s : Section C) :
    (coefficientDiagram A).obj s = s.toFunctor ⋙ A := (rfl)

@[simp]
theorem coefficientDiagram_map {s t : Section C} (α : s ⟶ t) :
    (coefficientDiagram A).map α = whiskerRight (hom α) A := (rfl)

variable [∀ s : Section C, HasLimit (s.toFunctor ⋙ A)]

/-- The completed coefficient objects and their maps under completed labels. Only limits
along the specified sections are required. -/
noncomputable abbrev coefficientLimit : Section C ⥤ V where
  obj s := limit (s.toFunctor ⋙ A)
  map α := limMap ((coefficientDiagram A).map α)
  map_id s := by
    apply limit.hom_ext
    intro d
    simp
  map_comp α β := by
    apply limit.hom_ext
    intro d
    simp [Category.assoc]

@[simp]
theorem coefficientLimit_obj (s : Section C) :
    (coefficientLimit A).obj s = limit (s.toFunctor ⋙ A) := (rfl)

/-- The action of a completed label is computed componentwise at every base object. -/
@[reassoc]
theorem coefficientLimit_map_π {s t : Section C} (α : s ⟶ t) (d : D) :
    (coefficientLimit A).map α ≫ limit.π (t.toFunctor ⋙ A) d =
      limit.π (s.toFunctor ⋙ A) d ≫ A.map ((hom α).app d) := by
  simp [coefficientLimit]

end Section
end TauCeti.CategoryTheory.Grothendieck
