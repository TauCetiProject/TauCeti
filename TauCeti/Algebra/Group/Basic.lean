/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic

/-!
# Basic identities in groups

## Main results

* `TauCeti.inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv`: in a group, `b⁻¹ * a = d⁻¹ * c` if and only
  if `a * c⁻¹ = b * d⁻¹`. In a commutative group, Mathlib's
  `inv_mul_eq_inv_mul_iff_mul_eq_mul` gives the equivalent `a * d = c * b`.
* `TauCeti.eq_of_eq_neg_of_ne_of_eq_one_or_neg_one`: if `a` and `c` are distinct elements of
  `{1, -1}` and `b = -a`, then `b = c`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {a b c d : G}

/-- Two left quotients `b⁻¹ * a` and `d⁻¹ * c` are equal exactly when the right quotients
`a * c⁻¹` and `b * d⁻¹` are. -/
@[to_additive /-- Two left differences `-b + a` and `-d + c` are equal exactly when the right
differences `a + -c` and `b + -d` are. -/]
theorem inv_mul_eq_inv_mul_iff_mul_inv_eq_mul_inv : b⁻¹ * a = d⁻¹ * c ↔ a * c⁻¹ = b * d⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, mul_assoc]

/-- If `a` and `c` are distinct elements of `{1, -1}` and `b = -a`, then `b = c`. -/
theorem eq_of_eq_neg_of_ne_of_eq_one_or_neg_one {α : Type*} [One α] [InvolutiveNeg α]
    {a b c : α} (ha : a = 1 ∨ a = -1) (hc : c = 1 ∨ c = -1) (hba : b = -a) (hac : a ≠ c) :
    b = c := by
  rcases ha with rfl | rfl <;> rcases hc with rfl | rfl
  · exact absurd rfl hac
  · exact hba
  · exact hba.trans (neg_neg 1)
  · exact absurd rfl hac

end TauCeti
