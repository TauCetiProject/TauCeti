/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Init

/-!
# Function rigidity from ranked anchors

An endofunction preserving a binary relation fixes every point determined by its relation
values at already fixed anchors. A natural-number rank makes this determination inductive:
anchors have lower rank, and seed points are fixed separately. The rank bound allows partial
rigidity as well as a proof that an endofunction is the identity.
-/

public section

namespace Function

/-- A relation-preserving endofunction fixes all points below a rank bound if it fixes the
seed points there and each non-seed point is uniquely determined by its lower-rank anchors. -/
theorem apply_eq_self_of_rank {α β : Type*} (g : α → α)
    {rel : α → α → β} {rank : α → ℕ} {anchors : α → List α} {seed : α → Prop}
    (hrank : ∀ x, ∀ z ∈ anchors x, rank z < rank x)
    (huniq : ∀ x, ¬ seed x → ∀ y,
      (anchors x).map (rel · y) = (anchors x).map (rel · x) → y = x)
    (hg : ∀ x y, rel (g x) (g y) = rel x y) (n : ℕ)
    (hseed : ∀ x, rank x < n → seed x → g x = x) : ∀ x, rank x < n → g x = x := by
  have h : ∀ m, ∀ x, rank x = m → m < n → g x = x := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro x hxm hmn
      by_cases hx : seed x
      · exact hseed x (hxm ▸ hmn) hx
      · apply huniq x hx
        apply List.map_congr_left
        intro z hz
        have hlt := hrank x z hz
        rw [hxm] at hlt
        simpa only [ih _ hlt z rfl (Nat.lt_trans hlt hmn)] using hg z x
  exact fun x hx ↦ h _ x rfl hx

end Function
