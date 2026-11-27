/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import TauCeti.Algebra.Category.Grp.Limits

/-!
# Homomorphisms on compatible sections

A natural transformation of group-valued functors induces a homomorphism of their groups
of compatible sections. This bundles the map of Mathlib's `Functor.sectionsFunctor` with
its pointwise group laws, so kernels and translations can be used on global sections.
-/

public section

open CategoryTheory

universe w v u

namespace GrpCat

variable {C : Type u} [Category.{v} C] {F G H : C ⥤ GrpCat.{w}}

/-- The homomorphism on compatible sections induced by a natural transformation. -/
def sectionsMap (α : F ⟶ G) : (F ⋙ forget GrpCat).sections →* (G ⋙ forget GrpCat).sections where
  toFun := (Functor.sectionsFunctor C).map (Functor.whiskerRight α (forget GrpCat))
  map_one' := by ext U; exact map_one (α.app U).hom
  map_mul' s t := by ext U; exact map_mul (α.app U).hom (s.val U) (t.val U)

@[simp]
lemma sectionsMap_apply (α : F ⟶ G) (s : (F ⋙ forget GrpCat).sections) (U : C) :
    (sectionsMap α s).val U = α.app U (s.val U) := (rfl)

@[simp]
lemma sectionsMap_id : sectionsMap (𝟙 F) = MonoidHom.id _ := by ext s U; rfl

@[simp]
lemma sectionsMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    sectionsMap (α ≫ β) = (sectionsMap β).comp (sectionsMap α) := by ext s U; rfl

end GrpCat
