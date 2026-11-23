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

end WithTop
