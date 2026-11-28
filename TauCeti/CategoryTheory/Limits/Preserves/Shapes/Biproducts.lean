/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic

/-!
# Preservation of binary biproducts

This module provides binary biproduct preservation instances for composition and functors
preserving biproducts of shape `WalkingPair`. The latter instance also supplies preservation for
identities and equivalences.
-/

public section

namespace CategoryTheory.Limits

attribute [instance 50] preservesBinaryBiproducts_of_preservesBiproducts

universe u₁ u₂ u₃ v₁ v₂ v₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]

/-- The composite of functors preserving binary biproducts preserves binary biproducts. -/
instance (priority := 100) preservesBinaryBiproducts_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [PreservesBinaryBiproducts F] [PreservesBinaryBiproducts G] :
    PreservesBinaryBiproducts (F ⋙ G) where
  preserves := { preserves := fun hb =>
    ⟨isBinaryBilimitOfPreserves G (isBinaryBilimitOfPreserves F hb)⟩ }

end CategoryTheory.Limits
