/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Option.Basic
public import Mathlib.Data.Set.CoeSort

/-!
# Restricting partial maps to subsets

A partial map `g : α → Option β` that sends the elements of `s : Set α` on which it is defined into
`t : Set β` restricts to a partial map `s → Option t`, `Set.optionRestrict`. It is the partial-map
analogue of `Set.MapsTo.restrict`, and is defined and undefined exactly where `g` is.
-/

public section

namespace Set

variable {α β : Type*} (s : Set α) (t : Set β)

/-- A partial map sending `s` into `t`, as a partial map from `s` to `t`. -/
def optionRestrict (g : α → Option β) (hg : ∀ ⦃x y⦄, g x = some y → x ∈ s → y ∈ t) (x : s) :
    Option t :=
  (g x).pmap (fun y hy => ⟨y, hg hy x.2⟩) fun _ h => h

variable {s t} {g : α → Option β} {hg : ∀ ⦃x y⦄, g x = some y → x ∈ s → y ∈ t}

@[simp]
theorem optionRestrict_eq_some_iff {x : s} {y : t} :
    s.optionRestrict t g hg x = some y ↔ g x = some y.1 := by
  simp [optionRestrict, Subtype.ext_iff, eq_comm (a := y.1)]

@[simp]
theorem optionRestrict_eq_none_iff {x : s} : s.optionRestrict t g hg x = none ↔ g x = none := by
  simp [optionRestrict]

/-- Forgetting the membership proofs recovers the original partial map. -/
@[simp]
theorem unattach_optionRestrict (x : s) : (s.optionRestrict t g hg x).unattach = g x := by
  cases h : g x with
  | none => rw [optionRestrict_eq_none_iff.2 h, Option.unattach_none]
  | some y => rw [(optionRestrict_eq_some_iff (y := ⟨y, hg h x.2⟩)).2 h, Option.unattach_some]

end Set
