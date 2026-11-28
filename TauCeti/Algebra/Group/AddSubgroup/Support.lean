/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Notation.Support

/-!
# Subgroup invariance on the support of a function

If a function to a type with zero is invariant under translation by an additive subgroup `H` at
every point of its support, then it is invariant under `H` everywhere: if `x` is outside the
support but `x + u` is inside it, translating back by `-u ∈ H` would put `x` in the support.

## Main results

* `AddSubgroup.add_eq_of_add_eq_on_support`: invariance on the support implies invariance
  everywhere.
-/

public section

open Function

namespace AddSubgroup

variable {V M : Type*} [AddGroup V] [Zero M]

/-- Invariance under a subgroup on the support of a function implies invariance everywhere. -/
theorem add_eq_of_add_eq_on_support (H : AddSubgroup V) {f : V → M}
    (hf : ∀ x ∈ support f, ∀ u ∈ H, f (x + u) = f x) (x : V) {u : V} (hu : u ∈ H) :
    f (x + u) = f x := by
  by_cases hx : f x = 0
  · by_cases hxu : f (x + u) = 0
    · simp [hx, hxu]
    · have h := hf (x + u) hxu (-u) (H.neg_mem hu)
      simp only [add_neg_cancel_right, hx] at h
      exact (hxu h.symm).elim
  · exact hf x hx u hu

end AddSubgroup
