/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.CategoryTheory.VonNeumannRegular.Basic

/-!
# The Jacobson radical of a von Neumann regular preadditive category

A von Neumann regular preadditive category has zero Jacobson radical.
-/

public section

namespace TauCeti

open CategoryTheory

namespace IsVonNeumannRegularCategory

variable {C : Type*} [Category* C] [Preadditive C]

/-- A von Neumann regular category has zero Jacobson radical. -/
@[simp]
theorem jacobsonRadicalIdeal_eq_bot [IsVonNeumannRegularCategory C] :
    jacobsonRadicalIdeal C = ⊥ := by
  refine eq_bot_iff.mpr (MorphismIdeal.le_def.mpr fun X Y f hf ↦ MorphismIdeal.mem_bot.mpr ?_)
  rw [jacobsonRadicalIdeal_hom] at hf
  obtain ⟨g, hg⟩ := exists_comp_comp_eq_self f
  have := mem_jacobsonRadical_iff_isIso_id_sub_comp_right.mp hf g
  have hzero : (𝟙 X - f ≫ g) ≫ f = 0 := by
    simp [Preadditive.sub_comp, hg]
  exact (cancel_epi (𝟙 X - f ≫ g)).mp (by simpa using hzero)

end IsVonNeumannRegularCategory

end TauCeti
