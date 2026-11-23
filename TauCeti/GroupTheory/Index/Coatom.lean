/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Order.Atoms

/-!
# Maximal subgroups above a subgroup of finite index

Every proper subgroup of finite index lies in a maximal subgroup. Finite index cannot be dropped:
the additive group `ℚ` has no maximal subgroup at all.

This is the algebraic input for maximal open subgroups of a topological group: a maximal subgroup
above an open subgroup is open.

## Main results

* `Subgroup.exists_isCoatom_le_of_finiteIndex`: a proper subgroup of finite index lies in a
  maximal subgroup, with additive form `AddSubgroup.exists_isCoatom_le_of_finiteIndex`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- **A proper subgroup of finite index lies in a maximal subgroup.** -/
@[to_additive /-- **A proper additive subgroup of finite index lies in a maximal additive
subgroup.** -/]
theorem exists_isCoatom_le_of_finiteIndex {K : Subgroup G} [K.FiniteIndex] (hK : K ≠ ⊤) :
    ∃ M : Subgroup G, IsCoatom M ∧ K ≤ M := by
  -- A proper subgroup above `K` of least index is maximal, because a strictly larger subgroup
  -- has strictly smaller index (Mathlib's `Subgroup.index_strictAnti`).
  obtain ⟨M, hM⟩ := exists_minimalFor_of_wellFoundedLT
    (fun M : Subgroup G ↦ K ≤ M ∧ M ≠ ⊤) index ⟨K, le_rfl, hK⟩
  have : M.FiniteIndex := finiteIndex_of_le hM.1.1
  refine ⟨M, ⟨hM.1.2, fun N hMN ↦ by_contra fun hN ↦ ?_⟩, hM.1.1⟩
  exact hM.not_lt ⟨hM.1.1.trans hMN.le, hN⟩ (index_strictAnti hMN)

end Subgroup
