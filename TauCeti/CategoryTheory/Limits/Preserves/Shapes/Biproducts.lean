/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Adjunction.Limits
import TauCeti.CategoryTheory.Limits.Shapes.Biproduct.Basic

/-!
# Preservation of binary biproducts

Composition and equivalences preserve binary biproducts. These instances supply the
preservation hypotheses for the functoriality of the Bass group.
-/

public section

namespace CategoryTheory.Limits

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

/-- An equivalence of categories preserves binary biproducts. -/
instance (priority := 100) preservesBinaryBiproducts_of_isEquivalence (F : C ⥤ D)
    [F.IsEquivalence] : PreservesBinaryBiproducts F :=
  preservesBinaryBiproducts_of_preservesBiproducts F

end CategoryTheory.Limits
