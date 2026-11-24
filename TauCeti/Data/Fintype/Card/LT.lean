/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Card

/-!
# A family smaller than a finite type misses a value

A family indexed by a finite type with fewer members than a finite type `X` cannot be surjective
onto `X`, so it misses some value (`Fintype.exists_forall_ne_of_card_lt`). The same holds for an
initial segment `{i | i < t}` of the natural numbers with `t < card X`
(`Fintype.exists_forall_lt_ne_of_lt_card`).
-/

public section

namespace Fintype

/-- A finite family which has fewer members than a finite type `X` misses a value of `X`. -/
theorem exists_forall_ne_of_card_lt {I X : Type*} [Fintype I] [Fintype X] (e : I → X)
    (hcard : card I < card X) : ∃ m, ∀ i, e i ≠ m := by
  by_contra! h
  exact absurd (card_le_of_surjective e h) (not_le.mpr hcard)

/-- An initial segment of the natural numbers with fewer members than a finite type `X` misses a
value of `X` under any map `ℕ → X`. -/
theorem exists_forall_lt_ne_of_lt_card {X : Type*} [Fintype X] {t : ℕ} (c : ℕ → X)
    (hcard : t < card X) : ∃ m, ∀ i < t, c i ≠ m := by
  obtain ⟨m, hm⟩ := exists_forall_ne_of_card_lt (fun i : Fin t ↦ c i) (by simpa using hcard)
  exact ⟨m, fun i hi ↦ hm ⟨i, hi⟩⟩

end Fintype
