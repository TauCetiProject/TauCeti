/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Basic.Countable.Defs
import Mathlib.Basic.Denumerable
import Mathlib.Logic.Equiv.Basic

/-!
# Injections into infinite sets of countable indices

An infinite subset of a countable type admits a self-injection that fixes any prescribed member.
This lets us reindex a countable sequence or an array axis into an infinite coordinate subset
while leaving a distinguished coordinate unchanged.
-/

public section

noncomputable section

namespace Set.Infinite

/-- An injection of a countable type into an infinite set `S` of indices may be chosen to fix a
prescribed element `i ∈ S`. -/
theorem exists_injective_into_apply_eq_of_mem {ι : Type*} [Countable ι] [Infinite ι]
    {S : Set ι} (hS : S.Infinite) {i : ι} (hi : i ∈ S) :
    ∃ a : ι → ι, Function.Injective a ∧ a i = i ∧ ∀ k, a k ∈ S := by
  classical
  have := hS.to_subtype
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ι) (β := S)
  refine ⟨fun k ↦ e (Equiv.swap i (e.symm ⟨i, hi⟩) k), ?_, by simp, fun k ↦ (e _).2⟩
  exact Subtype.val_injective.comp (e.injective.comp (Equiv.injective _))

end Set.Infinite
