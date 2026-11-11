/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Sums over a choice of representatives

Given a map `π : α → β` onto a finite type, a right inverse `r` of `π` chooses a representative
`r b` of each fibre, and `∑ b, T (r b)` sums a function `T : α → A` over these representatives.
Such sums typically come with a proof that they do not depend on the choice, for instance when
`π` is the projection onto a quotient such as the double cosets `H \ G / K`.

If they do not, and `A` is cancellative, then `T` itself is constant on the fibres of `π`:
comparing a fixed choice with the one that replaces the representative of a single fibre leaves
only the two terms at that fibre.

## Main statements

* `Function.RightInverse.eq_of_sum_eq`: a function whose sums over the representatives chosen by
  the right inverses of `π` all agree is constant on the fibres of `π`.
-/

public section

namespace Function.RightInverse

open Finset

/-- **A function is constant on fibres if its sums over representatives are**: if the sum over
a finite type `β` of the values of `T` at the representatives `r b` chosen by a right inverse `r`
of `π : α → β` does not depend on `r`, then `T a = T a'` whenever `π a = π a'`. -/
theorem eq_of_sum_eq {α β A : Type*} [Fintype β] [AddCancelCommMonoid A]
    {π : α → β} {r₀ : β → α} (hr₀ : Function.RightInverse r₀ π) (T : α → A)
    (hT : ∀ r : β → α, Function.RightInverse r π → ∑ b, T (r b) = ∑ b, T (r₀ b))
    {a a' : α} (h : π a = π a') : T a = T a' := by
  classical
  -- Replacing the representative `r₀ (π a)` by any `t` in the same fibre leaves the sum unchanged,
  -- and the two sums differ only in their terms at `π a`.
  have key (t : α) (ht : π t = π a) : T t = T (r₀ (π a)) := by
    have hr : Function.RightInverse (Function.update r₀ (π a) t) π := fun b => by
      rcases eq_or_ne b (π a) with rfl | hb
      · rw [Function.update_self, ht]
      · rw [Function.update_of_ne hb, hr₀ b]
    have := (sum_eq_sum_iff_single (mem_univ (π a)) fun b _ hb => by
      rw [Function.update_of_ne hb]).mp (hT _ hr)
    rwa [Function.update_self] at this
  exact (key a rfl).trans (key a' h.symm).symm

end Function.RightInverse
