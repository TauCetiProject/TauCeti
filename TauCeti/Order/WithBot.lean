/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Claude
-/
module

public import Mathlib.Order.Directed
public import Mathlib.Order.WithBot

/-!
# Lower bounds by coercions and truncation monotonicity in `WithTop`

In a downward directed order `α`, every element of `WithTop α` lies above the coercion of some
element of `α` below any given bound. This brings finitely many elements of `WithTop α` down to a
common coercion that is itself bounded, for instance a common exponent `m ≤ -1` below the orders
of several meromorphic functions. In a nonempty linear order, truncating a `WithTop α` element at
`(s : WithTop α)` and unwrapping via `WithTop.untopA` is monotone in `s`.

## Main results

* `WithTop.exists_le_and_coe_le`: for `x : WithTop α` and `a : α` there is `b ≤ a` with `↑b ≤ x`.
* `WithTop.monotone_untopA_min_coe`: `s ↦ (min (s : WithTop α) τ).untopA` is monotone.
* `WithTop.untopA_coe_min_le`: `(min (t : WithTop α) x).untopA ≤ t`.
* `WithTop.untopA_bot`: `(⊥ : WithTop α).untopA = ⊥`.
* `WithTop.untopA_map`: `(x.map f).untopA = f x.untopA` for `x ≠ ⊤`.
* `WithTop.map_untopA_min_coe`:
  `f (min (t : WithTop α) x).untopA = (min (f t : WithTop β) (x.map f)).untopA`
  for monotone `f`.
-/

public section

namespace WithTop

variable {α : Type*}

/-- In a downward directed order, every `x : WithTop α` lies above the coercion of some element
below any given `a : α`. -/
theorem exists_le_and_coe_le [Preorder α] [IsCodirectedOrder α] (x : WithTop α) (a : α) :
    ∃ b : α, b ≤ a ∧ (b : WithTop α) ≤ x := by
  induction x with
  | top => exact ⟨a, le_rfl, le_top⟩
  | coe k =>
    obtain ⟨b, hbk, hba⟩ := exists_le_le k a
    exact ⟨b, hba, coe_le_coe.2 hbk⟩

/-- Unwrapping the truncation `min (s : WithTop α) τ` via `WithTop.untopA` is monotone in `s`. -/
theorem monotone_untopA_min_coe [LinearOrder α] [Nonempty α] (τ : WithTop α) :
    Monotone fun s : α ↦ (min (s : WithTop α) τ).untopA :=
  fun _ _ hst ↦ WithTop.untopA_mono (ne_top_of_le_ne_top WithTop.coe_ne_top inf_le_left)
    (inf_le_inf_right τ (WithTop.coe_le_coe.mpr hst))

/-- Truncating `t` at `x : WithTop α` is bounded above by `t`. -/
theorem untopA_coe_min_le [LinearOrder α] [Nonempty α] (t : α) (x : WithTop α) :
    (min (t : WithTop α) x).untopA ≤ t :=
  WithTop.untopA_le (min_le_left _ _)

/-- Unwrapping `⊥ : WithTop α` yields `⊥ : α`. -/
@[simp]
theorem untopA_bot [Bot α] [Nonempty α] : (⊥ : WithTop α).untopA = (⊥ : α) := by
  rw [← WithTop.coe_bot, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

/-- Unwrapping a non-top element after `WithTop.map` commutes with `WithTop.untopA`. -/
theorem untopA_map {β : Type*} [Nonempty α] [Nonempty β] (f : α → β) {x : WithTop α}
    (hx : x ≠ ⊤) : (x.map f).untopA = f x.untopA := by
  lift x to α using hx
  rw [map_coe, untopA_eq_untop coe_ne_top, untopA_eq_untop coe_ne_top, untop_coe, untop_coe]

/-- Applying a monotone map `f : α → β` after truncating `t` at `x : WithTop α` commutes with
mapping `f` inside the truncation. -/
theorem map_untopA_min_coe {β : Type*} [LinearOrder α] [Nonempty α]
    [LinearOrder β] [Nonempty β] {f : α → β} (hf : Monotone f) (t : α) (x : WithTop α) :
    f (min (t : WithTop α) x).untopA = (min (f t : WithTop β) (x.map f)).untopA := by
  have hne : min (t : WithTop α) x ≠ ⊤ := ne_top_of_le_ne_top coe_ne_top (min_le_left _ _)
  have hmap_min : (min (t : WithTop α) x).map f = min (f t : WithTop β) (x.map f) := by
    rw [← WithTop.map_coe (f := f)]
    rcases le_total (t : WithTop α) x with h | h
    · rw [min_eq_left h, min_eq_left (hf.withTop_map h)]
    · rw [min_eq_right h, min_eq_right (hf.withTop_map h)]
  rw [← hmap_min, untopA_map f hne]

end WithTop
