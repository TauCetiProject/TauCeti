/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet

/-!
# Complements on factor sets

This file complements `Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean` with the count
in the top factor set (`Associates.count_top`).
-/

public section

namespace Associates

variable {α : Type*} [CommMonoidWithZero α] [DecidableEq (Associates α)]
  [∀ p : Associates α, Decidable (Irreducible p)]

/-- Counting in the factor set `⊤`, the factor set of `0`, gives `0`: by definition, the count is
natural-valued and `⊤` is sent to `0`. -/
@[simp]
theorem count_top (p : Associates α) : p.count (⊤ : FactorSet α) = 0 := by
  unfold Associates.count
  split_ifs <;> rfl

end Associates
