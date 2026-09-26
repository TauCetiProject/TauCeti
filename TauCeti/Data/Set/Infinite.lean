/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Basic.Denumerable
import Mathlib.Logic.Equiv.Basic

/-!
# Injections into infinite sets of natural numbers

An infinite subset of `ℕ` admits an injection from `ℕ` that fixes any prescribed member.
This lets us reindex a countable sequence or an array axis into an infinite coordinate subset
while leaving a distinguished coordinate unchanged.
-/

public section

noncomputable section

namespace Set.Infinite

/-- An injection of `ℕ` into an infinite set `S` of indices may be chosen to fix a prescribed
element `i ∈ S`. -/
theorem exists_injective_nat_apply_eq_of_mem {S : Set ℕ} (hS : S.Infinite) {i : ℕ}
    (hi : i ∈ S) : ∃ a : ℕ → ℕ, Function.Injective a ∧ a i = i ∧ ∀ k, a k ∈ S := by
  have := hS.to_subtype
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := ℕ) (β := S)
  refine ⟨fun k ↦ e (Equiv.swap i (e.symm ⟨i, hi⟩) k), ?_, by simp, fun k ↦ (e _).2⟩
  exact Subtype.val_injective.comp (e.injective.comp (Equiv.injective _))

end Set.Infinite
