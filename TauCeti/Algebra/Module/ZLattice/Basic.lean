/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Fundamental domains of integer spans

This file records geometric properties of the standard fundamental domain associated to a basis.

## Main results

* `ZSpan.convex_fundamentalDomain`: the fundamental domain of a real basis is convex.
-/

public section

open Module Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The fundamental domain of a basis is convex: it is cut out by the conditions
`b.repr x i ∈ [0, 1)`, one convex condition per coordinate. -/
theorem _root_.ZSpan.convex_fundamentalDomain (β : Basis ι ℝ E) :
    Convex ℝ (ZSpan.fundamentalDomain β) := by
  intro x hx y hy a t ha ht hat
  rw [ZSpan.mem_fundamentalDomain] at hx hy ⊢
  intro i
  simpa using convex_Ico (0 : ℝ) 1 (hx i) (hy i) ha ht hat

end TauCeti
