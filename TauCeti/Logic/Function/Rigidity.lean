/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Init

/-!
# Function rigidity from rank

An endofunction preserving a binary relation fixes every point determined by its relation
values at lower-rank points, provided seed points are fixed separately. The rank bound allows
partial rigidity as well as a proof that an endofunction is the identity.
-/

public section

namespace Function

/-- A relation-preserving endofunction fixes all points below a rank bound if it fixes the
seed points there and each non-seed point below the bound is uniquely determined by its
relation values at lower-rank points. -/
theorem apply_eq_self_of_rank {α β : Sort*} (g : α → α)
    {rel : α → α → β} {rank : α → ℕ} {seed : α → Prop}
    (hg : ∀ x y, rel (g x) (g y) = rel x y) (n : ℕ)
    (hseed : ∀ x, rank x < n → seed x → g x = x)
    (huniq : ∀ x, rank x < n → ¬ seed x → ∀ y,
      (∀ z, rank z < rank x → rel z y = rel z x) → y = x) :
    ∀ x, rank x < n → g x = x := by
  have h : ∀ m, ∀ x, rank x = m → m < n → g x = x := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro x hxm hmn
      by_cases hx : seed x
      · exact hseed x (hxm ▸ hmn) hx
      · apply huniq x (hxm ▸ hmn) hx
        intro z hlt
        rw [hxm] at hlt
        simpa only [ih _ hlt z rfl (Nat.lt_trans hlt hmn)] using hg z x
  exact fun x hx ↦ h _ x rfl hx

end Function
