/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Colimit stability of morphism properties

Stability under colimits of a fixed shape is preserved by intersections and by
inverse image along a functor preserving those colimits. Intersections also preserve
stability under filtered colimits. These rules allow closure
properties of quasi-isomorphisms to be deduced from those of isomorphisms.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

universe w w'

variable {C D : Type*} [Category* C] [Category* D] {J : Type*} [Category* J]

/-- The intersection of two properties stable under colimits of shape `J` is stable
under those colimits. -/
instance IsStableUnderColimitsOfShape.inf {P Q : MorphismProperty C}
    [P.IsStableUnderColimitsOfShape J] [Q.IsStableUnderColimitsOfShape J] :
    (P ⊓ Q).IsStableUnderColimitsOfShape J where
  condition F G s t hs ht f hf φ hφ :=
    ⟨IsStableUnderColimitsOfShape.condition F G s t hs ht f (fun j ↦ (hf j).1) φ hφ,
      IsStableUnderColimitsOfShape.condition F G s t hs ht f (fun j ↦ (hf j).2) φ hφ⟩

/-- The intersection of two properties stable under filtered colimits is stable
under filtered colimits. -/
instance IsStableUnderFilteredColimits.inf {P Q : MorphismProperty C}
    [P.IsStableUnderFilteredColimits.{w, w'}] [Q.IsStableUnderFilteredColimits.{w, w'}] :
    (P ⊓ Q).IsStableUnderFilteredColimits.{w, w'} where
  isStableUnderColimitsOfShape J _ _ := by infer_instance

/-- Inverse image along a colimit-preserving functor preserves stability under
colimits of the same shape. -/
instance IsStableUnderColimitsOfShape.inverseImage (P : MorphismProperty D) (H : C ⥤ D)
    [PreservesColimitsOfShape J H] [P.IsStableUnderColimitsOfShape J] :
    (P.inverseImage H).IsStableUnderColimitsOfShape J where
  condition F G s t hs ht f hf φ hφ :=
    IsStableUnderColimitsOfShape.condition
      (W := P) (F ⋙ H) (G ⋙ H) (H.mapCocone s) (H.mapCocone t)
      (isColimitOfPreserves H hs) (isColimitOfPreserves H ht)
      (Functor.whiskerRight f H) hf (H.map φ)
      (fun j ↦ by simpa using congrArg H.map (hφ j))

end CategoryTheory.MorphismProperty
