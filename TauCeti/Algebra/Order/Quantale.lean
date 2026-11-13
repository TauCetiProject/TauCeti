/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Quantale

/-!
# Residuation in quantales at the extreme elements

In a quantale the right residual `x ⇨ᵣ y` is the largest `z` with `x * z ≤ y`. It is `⊤` in the
two cases where that constraint is vacuous: when the bound `y` is `⊤`, and when the factor `x`
is the absorbing element `⊥`.
-/

public section

namespace Quantale

variable {α : Type*} [Semigroup α] [CompleteLattice α] [IsQuantale α]

/-- The bound `⊤` imposes no constraint, so the right residual by it is `⊤`. -/
@[to_additive (attr := simp)
/-- The bound `⊤` imposes no constraint, so the right residual by it is `⊤`. -/]
theorem rightMulResiduation_top (x : α) : x ⇨ᵣ (⊤ : α) = ⊤ :=
  top_unique <| rightMulResiduation_le_iff_mul_le.mpr le_top

/-- The absorbing element `⊥` imposes no constraint, so its right residual is `⊤`. -/
@[to_additive (attr := simp)
/-- The absorbing element `⊥` imposes no constraint, so its right residual is `⊤`. -/]
theorem bot_rightMulResiduation (y : α) : (⊥ : α) ⇨ᵣ y = ⊤ :=
  top_unique <| rightMulResiduation_le_iff_mul_le.mpr <| by simp

end Quantale
