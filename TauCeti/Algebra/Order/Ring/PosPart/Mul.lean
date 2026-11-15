/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NoncommRing

/-!
# A positive-part product identity

For a lattice-ordered additive group with ring multiplication,
`b⁺ * c + (-b) * (c ⊓ 0) = b⁺ * c⁺ - b⁻ * c⁻`.
Multiplication need not be commutative or compatible with the order. In the integer case this
rewrites tropical coefficient mutation contributions as exchange-matrix corrections.
-/

public section

namespace TauCeti

/-- Rewrites `b⁺ * c + (-b) * (c ⊓ 0)` as `b⁺ * c⁺ - b⁻ * c⁻` in terms of positive and
negative parts. Here `c ⊓ 0` is the infimum with zero, namely `-c⁻`. -/
theorem posPart_mul_add_neg_mul_inf_zero {R : Type*} [Ring R] [Lattice R]
    [AddLeftMono R] (b c : R) :
    b⁺ * c + (-b) * (c ⊓ 0) = b⁺ * c⁺ - b⁻ * c⁻ := by
  have hc : c ⊓ 0 = -c⁻ := by rw [negPart_eq_neg_inf_zero, neg_neg]
  calc
    b⁺ * c + (-b) * (c ⊓ 0) =
        b⁺ * (c⁺ - c⁻) + (b⁺ - b⁻) * c⁻ := by
      rw [posPart_sub_negPart, posPart_sub_negPart, hc, neg_mul_neg]
    _ = b⁺ * c⁺ - b⁻ * c⁻ := by noncomm_ring

end TauCeti
