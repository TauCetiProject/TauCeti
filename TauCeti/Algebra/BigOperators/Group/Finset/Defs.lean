/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Finite sums of singleton multisets

Summing `{g a}` in `Multiset β` over `a ∈ s` recovers the mapped underlying multiset `s.val.map g`
(`Finset.sum_multiset_map_singleton`), complementing Mathlib's `Finset.sum_multiset_singleton`.
-/

public section

namespace Finset

/-- Summing singleton multisets `{g a}` over `a ∈ s` produces `s.val.map g`. -/
theorem sum_multiset_map_singleton {ι β : Type*} (s : Finset ι) (g : ι → β) :
    ∑ a ∈ s, ({g a} : Multiset β) = s.val.map g := by
  rw [sum_eq_multiset_sum,
    show (fun a ↦ ({g a} : Multiset β)) = (fun b ↦ ({b} : Multiset β)) ∘ g from
      funext fun _ ↦ (Function.comp_apply).symm,
    ← Multiset.map_map, Multiset.sum_map_singleton]

end Finset
