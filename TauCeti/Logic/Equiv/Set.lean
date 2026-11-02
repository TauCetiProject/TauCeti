/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Set

/-!
# Bijections between sets from equivalences of subtypes

A map `g : α → β` that agrees on `s` with an equivalence `s ≃ t` is a bijection from `s` onto `t`
(`Set.BijOn.of_equiv_coe`). This is a converse to `Set.BijOn.equiv`, which turns a bijection
between sets into an equivalence of the subtypes.
-/

public section

namespace Set

/-- A map that agrees on `s` with an equivalence `s ≃ t` is a bijection from `s` onto `t`. -/
theorem BijOn.of_equiv_coe {α β : Type*} {s : Set α} {t : Set β} {g : α → β}
    (e : s ≃ t) (he : ∀ z : s, (e z : β) = g z) : BijOn g s t := by
  refine ⟨fun z hz => he ⟨z, hz⟩ ▸ (e ⟨z, hz⟩).2, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · have := e.injective (Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm)))
    exact congrArg Subtype.val this
  · exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).2, by rw [← he, e.apply_symm_apply]⟩

end Set
