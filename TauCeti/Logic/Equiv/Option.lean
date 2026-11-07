/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Option

/-!
# Extending a matching of the complements of two points

A relation between two index types that holds along an equivalence of the complements of two
points, and also holds at those two points, is realised by an equivalence of the whole types
(`Equiv.exists_equiv_forall_of_equiv_subtype_ne`).
-/

public section

namespace Equiv

/-- A relation `R` between two types that holds along an equivalence of the complements of `i₀`
and `j₀` and also holds at `i₀, j₀` is realised by an equivalence of the whole types. -/
theorem exists_equiv_forall_of_equiv_subtype_ne {ι κ : Type*}
    {R : ι → κ → Prop} {i₀ : ι} {j₀ : κ} (e : {i // i ≠ i₀} ≃ {j // j ≠ j₀}) (h₀ : R i₀ j₀)
    (h : ∀ i : {i // i ≠ i₀}, R i (e i)) : ∃ e' : ι ≃ κ, ∀ i, R i (e' i) := by
  classical
  refine ⟨(Equiv.optionSubtypeNe i₀).symm.trans
    ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe j₀)), fun i ↦ ?_⟩
  rcases eq_or_ne i i₀ with rfl | hi
  · have hnone : ((Equiv.optionSubtypeNe i).symm.trans
        ((Equiv.optionCongr e).trans (Equiv.optionSubtypeNe j₀))) i = j₀ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self]
      rfl
    rwa [hnone]
  · rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hi,
      Equiv.optionCongr_apply, Option.map_some, Equiv.optionSubtypeNe_some]
    exact h ⟨i, hi⟩

end Equiv
