/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Free ultrafilters via the cofinite filter

An ultrafilter on a type `α` is finer than `Filter.cofinite` if and only if it is free (not equal to
`pure a` for any `a : α`). On `ℕ`, where `Filter.cofinite = Filter.atTop`, this characterizes free
ultrafilters as those finer than `Filter.atTop`.
-/

public section

namespace Ultrafilter

/-- An ultrafilter on `α` is finer than `Filter.cofinite` if and only if it is not principal at any
point of `α`. -/
theorem le_cofinite_iff_forall_ne_pure {α : Type*} {ω : Ultrafilter α} :
    (ω : Filter α) ≤ Filter.cofinite ↔ ∀ a, ω ≠ pure a := by
  refine ⟨fun h a ha ↦ ?_,
    fun h ↦ ω.le_cofinite_or_eq_pure.resolve_right fun ⟨a, ha⟩ ↦ h a ha⟩
  have hmem : ({a}ᶜ : Set α) ∈ (ω : Filter α) := h (Filter.mem_cofinite.2 (by simp))
  simp [ha] at hmem

/-- An ultrafilter on `ℕ` is finer than `Filter.atTop` if and only if it is not principal at any
natural number. -/
theorem le_atTop_iff_forall_ne_pure {ω : Ultrafilter ℕ} :
    (ω : Filter ℕ) ≤ Filter.atTop ↔ ∀ n, ω ≠ pure n := by
  rw [← Nat.cofinite_eq_atTop, le_cofinite_iff_forall_ne_pure]

end Ultrafilter
