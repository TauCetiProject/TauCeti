/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.DifferentialModule.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Zero objects and binary biproducts of differential modules

The equivalence between differential modules and one-periodic complexes transports zero objects
and binary biproducts from the ambient additive category. These structures are needed to put the
componentwise split exact structure on differential modules.
-/

public section

universe v u

namespace TauCeti.DifferentialModule

open CategoryTheory CategoryTheory.Limits ZeroObject

variable (C : Type u) [Category.{v} C]

/-- The zero differential module. -/
noncomputable def zero [HasZeroMorphisms C] [HasZeroObject C] : DifferentialModule C where
  X := 0
  d := 0
  d_comp_d := by simp

/-- The zero differential module is a zero object. -/
theorem isZero_zero [HasZeroMorphisms C] [HasZeroObject C] : IsZero (zero C) := by
  constructor <;> intro M
  · exact ⟨⟨⟨0⟩, fun f ↦ by ext; exact (CategoryTheory.Limits.isZero_zero C).eq_of_src _ _⟩⟩
  · exact ⟨⟨⟨0⟩, fun f ↦ by ext; exact (CategoryTheory.Limits.isZero_zero C).eq_of_tgt _ _⟩⟩

/-- Differential modules have a zero object when the ambient category does. -/
noncomputable instance [HasZeroMorphisms C] [HasZeroObject C] :
    HasZeroObject (DifferentialModule C) :=
  ⟨⟨zero C, isZero_zero C⟩⟩

/-- Differential modules have binary biproducts when the ambient additive category does. -/
noncomputable instance [Preadditive C] [HasBinaryBiproducts C] :
    HasBinaryBiproducts (DifferentialModule C) := by
  let _ : HasBinaryProducts (DifferentialModule C) :=
    Adjunction.hasLimitsOfShape_of_equivalence (onePeriodicComplexEquivalence C).functor
  exact HasBinaryBiproducts.of_hasBinaryProducts

end TauCeti.DifferentialModule
