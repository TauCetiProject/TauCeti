/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Cofinite

/-!
# Functions tending to infinity along the cofinite filter

A function `f` tending to `atTop` along the cofinite filter takes only finitely many values below
each bound (`Filter.Tendsto.finite_setOf_lt`). If moreover all its values lie strictly above `b`,
then they are bounded below by a single `c > b` (`Filter.Tendsto.exists_gt_forall_le`); for
instance, positive periods tending to infinity are bounded below by a positive constant. These
complement Mathlib's `Filter.Tendsto.exists_forall_le`, which needs a nonempty domain.
-/

public section

open Filter

namespace Filter.Tendsto

variable {α β : Type*} {f : α → β}

/-- A function tending to `atTop` along the cofinite filter takes only finitely many values below
any bound. -/
theorem finite_setOf_lt [Preorder β] (hf : Tendsto f cofinite atTop) (b : β) :
    {a | f a < b}.Finite :=
  (eventually_cofinite.1 (hf.eventually_ge_atTop b)).subset fun _ h => h.not_ge

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
