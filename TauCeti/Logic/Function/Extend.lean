/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Init
public import Mathlib.Data.Set.Inclusion
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Coe

/-!
# Extending functions along injections

A function `a` on `ℕ` extends to `ℤ` along the cast `ℕ → ℤ` by `Function.extend`, with a
fallback function `e` supplying the values off the range of the cast. This file records that the
negative integers lie off that range, so the extension agrees with the fallback there.

A function `g` on a subset `t` extends to the whole type along `Subtype.val`, for instance by
zero. Restricting `g` to a smaller subset `s` before extending does not change the extension at
the points which lie in `s` as soon as they lie in `t`.

## Main results

* `Function.extend_natCast_of_neg`: the extension of `a` along `ℕ → ℤ` with fallback `e` takes
  the value `e n` at every negative integer `n`.
* `Function.extend_subtypeVal_comp_inclusion`: extending a function on `t` and extending its
  restriction to `s ⊆ t` agree at every point of `s` and every point outside `t`.
-/

public section

namespace Function

/-- The extension of a function on `ℕ` along the cast to `ℤ` agrees with the fallback at
negative integers. -/
theorem extend_natCast_of_neg {α : Sort*} (a : ℕ → α) (e : ℤ → α) {n : ℤ} (hn : n < 0) :
    extend ((↑) : ℕ → ℤ) a e n = e n :=
  extend_apply' _ _ _ fun ⟨m, hm⟩ => by omega

/-- Extending a function on `t` along `Subtype.val`, or first restricting it to a subset `s ⊆ t`,
gives the same value at a point `a` that lies in `s` whenever it lies in `t`: both are `g a` if
`a ∈ s`, and both are the fallback `e a` if `a ∉ t`. -/
theorem extend_subtypeVal_comp_inclusion {α β : Type*} {s t : Set α} (h : s ⊆ t) (g : t → β)
    (e : α → β) {a : α} (ha : a ∈ t → a ∈ s) :
    extend Subtype.val (g ∘ Set.inclusion h) e a = extend Subtype.val g e a := by
  by_cases hat : a ∈ t
  · exact (Subtype.val_injective.extend_apply _ e ⟨a, ha hat⟩).trans
      (Subtype.val_injective.extend_apply g e ⟨a, hat⟩).symm
  · have has : a ∉ s := fun has ↦ hat (h has)
    rw [extend_apply' _ _ _ fun ⟨b, hb⟩ ↦ has (hb ▸ b.2),
      extend_apply' _ _ _ fun ⟨b, hb⟩ ↦ hat (hb ▸ b.2)]

end Function
