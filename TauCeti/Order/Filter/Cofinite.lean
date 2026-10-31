/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Cofinite

/-!
# Functions tending to infinity along the cofinite filter

If a function tending to `atTop` along the cofinite filter takes all its values strictly above `b`,
then they are bounded below by a single `c > b` (`Filter.Tendsto.exists_gt_forall_le`); for
instance, positive periods tending to infinity are bounded below by a positive constant. This
complements Mathlib's `Filter.Tendsto.exists_forall_le`, which needs a nonempty domain. That such a
function takes only finitely many values below each bound is Mathlib's Northcott property
(`northcott_iff_tendsto`, `Northcott.finite_le`).
-/

public section

open Filter

namespace Filter.Tendsto

variable {α β : Type*} {f : α → β}

/-- If a function tending to `atTop` along the cofinite filter takes all its values above `b`, it
is bounded below by some `c > b`. -/
theorem exists_gt_forall_le [LinearOrder β] [NoMaxOrder β] (hf : Tendsto f cofinite atTop)
    {b : β} (hb : ∀ a, b < f a) : ∃ c, b < c ∧ ∀ a, c ≤ f a := by
  cases isEmpty_or_nonempty α
  · obtain ⟨c, hc⟩ := exists_gt b
    exact ⟨c, hc, isEmptyElim⟩
  · obtain ⟨a₀, ha₀⟩ := hf.exists_forall_le
    exact ⟨f a₀, hb a₀, ha₀⟩

end Filter.Tendsto
