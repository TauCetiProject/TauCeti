/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.Completion
public import TauCeti.RingTheory.Valuation.ValuativeRel.ValueGroup

/-!
# Value groups of completions

Completion does not add values to a valued field. Consequently a discrete valuation remains
discrete on completion, and rank at most one is preserved. These facts allow the same
uniformizer to be used before and after completing an unramified extension.

The proof uses Mathlib's `Valuation.exists_extension_eq_map`, which says that the extended
valuation takes every value already on the dense subfield.
-/

public section

open ValuativeRel UniformSpace

namespace UniformSpace.Completion

variable {K : Type*} [Field K] [ValuativeRel K] [UniformSpace K]
  [IsValuativeTopology K] [IsUniformAddGroup K]

/-- Every value in the completion is attained on the original field. -/
theorem exists_coe_veq (x : Completion K) : ∃ r : K, (r : Completion K) =ᵥ x := by
  obtain ⟨r, hr⟩ := (valuation K).exists_extension_eq_map x
  refine ⟨r, ((valuation K).extension.veq_iff_eq).2 ?_⟩
  simpa using hr.symm

/-- The canonical map on value groups from a valued field to its completion is surjective. -/
theorem mapValueGroupWithZero_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero K (Completion K)) := by
  intro γ
  obtain ⟨x, rfl⟩ := valuation_surjective γ
  obtain ⟨r, hr⟩ := exists_coe_veq x
  exact ⟨valuation K r, by
    rw [ValuativeExtension.mapValueGroupWithZero_valuation]
    exact (valuation (Completion K)).veq_iff_eq.mp hr⟩

/-- Completion preserves discreteness of a valued field, with no rank hypothesis. -/
instance isDiscrete [IsDiscrete K] : IsDiscrete (Completion K) :=
  .of_surjective_mapValueGroupWithZero mapValueGroupWithZero_surjective

/-- Completion preserves rank at most one. -/
instance isRankLeOne [IsRankLeOne K] : IsRankLeOne (Completion K) :=
  .of_surjective_mapValueGroupWithZero mapValueGroupWithZero_surjective

end UniformSpace.Completion
