/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.OfFn

/-!
# Lists related entrywise to `List.ofFn`

The list `f 0, …, f (n - 1)` is related entrywise by `R` to a list `l` exactly when `l` is the list
`g 0, …, g (n - 1)` of a function `g` with `R (f i) (g i)` for every `i`
(`List.forall₂_ofFn_left_iff`). This turns an entrywise condition on lists into a family of
conditions indexed by `Fin n`, one for each entry.
-/

public section

namespace List

variable {α β : Type*} {R : α → β → Prop}

/-- `List.ofFn f` is related entrywise by `R` to a list exactly when that list is `List.ofFn g` for
a function `g` with `R (f i) (g i)` for every `i`. -/
theorem forall₂_ofFn_left_iff {n : ℕ} {f : Fin n → α} {l : List β} :
    Forall₂ R (ofFn f) l ↔ ∃ g : Fin n → β, (∀ i, R (f i) (g i)) ∧ l = ofFn g := by
  refine ⟨fun h => ?_, ?_⟩
  · induction n generalizing l with
    | zero => exact ⟨Fin.elim0, fun i => i.elim0, forall₂_nil_left_iff.1 h⟩
    | succ n ih =>
      rw [ofFn_succ, forall₂_cons_left_iff] at h
      obtain ⟨b, l, hb, h, rfl⟩ := h
      obtain ⟨g, hg, rfl⟩ := ih h
      exact ⟨Fin.cons b g, Fin.cases hb hg, (ofFn_cons ..).symm⟩
  · rintro ⟨g, h, rfl⟩
    exact forall₂_iff_get.2 ⟨by simp, fun i h₁ _ => by simpa using h ⟨i, by simpa using h₁⟩⟩

end List
