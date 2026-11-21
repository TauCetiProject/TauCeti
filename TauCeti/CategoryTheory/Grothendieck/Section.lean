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

/-!
# Sections and their coefficient limits

A section of a Grothendieck construction chooses an object over each base object
and compatible transport arrows. Its morphisms are natural transformations over
the identity of the base. If the fibers are groupoids, these section morphisms
are invertible, even when the base is not a groupoid.

A functor from the total category to a category `V` restricts to a diagram
along each section. Taking limits of these diagrams gives a functor from sections
to `V`. Section isomorphisms induce isomorphisms of the limits via `Functor.mapIso`;
when every fiber is a groupoid, every section morphism induces an isomorphism.
After importing `Mathlib.CategoryTheory.Endomorphism`, apply `Functor.mapAut`
to obtain an action of the automorphism group of a section.
The projection formula computes the induced maps at every base object;
functoriality supplies identity and composition.

Construct sections with `Functor.Fiber.mk` from a functor whose composite with the
projection is the identity. `Section.homMk` constructs a section morphism from a
natural transformation satisfying the corresponding base identity.

The section category uses Mathlib's `Functor.Fiber` of the postcomposition
functor, rather than a separate encoding of transport coherence. Coefficient
maps and their limits use `whiskeringRight`, `limMap` and `Functor.mapAut`.
No faithfulness of the functor from the total category is required.

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

/-- A section chooses an object over each specified base object. -/
@[simp]
theorem toFunctor_obj_base (s : Section C) (d : D) : (s.toFunctor.obj d).base = d :=
  Functor.congr_obj s.toFunctor_comp_forget d

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
theorem whiskerRight_hom_forget {s t : Section C} (α : s ⟶ t) :
    whiskerRight (hom α) (forget C) =
      eqToHom s.toFunctor_comp_forget ≫ eqToHom t.toFunctor_comp_forget.symm := by
  have := α.property
  simpa using IsHomLift.fac'
    ((whiskeringRight D (Grothendieck C) D).obj (forget C)) (𝟙 (𝟭 D)) (hom α)

/-- Every component of a section morphism projects to an isomorphism of the base. -/
instance isIso_hom_app_base {s t : Section C} (α : s ⟶ t) (d : D) :
    IsIso ((hom α).app d).base := by
  have h := whiskerRight_hom_forget α
  have : IsIso (whiskerRight (hom α) (forget C)) := by
    rw [h]
    infer_instance
  rw [← forget_map, ← whiskerRight_app]
  exact NatIso.isIso_app_of_isIso _ d

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

/-- Restriction of a functor from the total category along each section. -/
abbrev coefficientDiagram : Section C ⥤ (D ⥤ V) :=
  Functor.Fiber.fiberInclusion ⋙ (whiskeringRight D (Grothendieck C) V).obj A

@[simp]
theorem coefficientDiagram_obj (s : Section C) :
    (coefficientDiagram A).obj s = s.toFunctor ⋙ A := (rfl)

@[simp]
theorem coefficientDiagram_map {s t : Section C} (α : s ⟶ t) :
    (coefficientDiagram A).map α = whiskerRight (hom α) A := (rfl)

variable [∀ s : Section C, HasLimit (s.toFunctor ⋙ A)]

/-- Limits of the diagrams restricted along sections, with maps induced by section morphisms.
Only limits along the specified sections are required. -/
-- The object types must compute so that the maps compose with limit projections.
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

@[simp]
theorem coefficientLimit_map {s t : Section C} (α : s ⟶ t) :
    (coefficientLimit A).map α = limMap (whiskerRight (hom α) A) := (rfl)

/-- The induced map on limits is computed componentwise at every base object. -/
@[reassoc]
theorem coefficientLimit_map_π {s t : Section C} (α : s ⟶ t) (d : D) :
    (coefficientLimit A).map α ≫ limit.π (t.toFunctor ⋙ A) d =
      limit.π (s.toFunctor ⋙ A) d ≫ A.map ((hom α).app d) := by
  simp

end Section
end TauCeti.CategoryTheory.Grothendieck
