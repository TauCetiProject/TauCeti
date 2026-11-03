/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum.Basic

/-!
# Rational combinations of `1` and an irrational element

Let `K` be a division ring of characteristic zero and let `β ∈ K` be irrational, that is, not the
image of a rational number. Then the rational combinations `a + b β` are pairwise distinct
(`TauCeti.ratCast_add_ratCast_mul_injective`): the map `(a, b) ↦ a + b β` from `ℚ × ℚ` to `K` is
injective. For example, the integer grid points `u + v β` used in transcendence proofs are
distinct.
-/

public section

namespace TauCeti

/-- **Rational combinations of `1` and an irrational element are distinct**: if `β` in a division
ring of characteristic zero is not the image of a rational number, then `(a, b) ↦ a + b β` is
injective on `ℚ × ℚ`. -/
theorem ratCast_add_ratCast_mul_injective {K : Type*} [DivisionRing K] [CharZero K] {β : K}
    (hβ : ∀ q : ℚ, (q : K) ≠ β) :
    Function.Injective fun p : ℚ × ℚ ↦ (p.1 : K) + p.2 * β := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only at h
  obtain rfl | hb := eq_or_ne b b'
  · simpa using h
  refine absurd ?_ (hβ ((b' - b)⁻¹ * (a - a')))
  have hb' : ((b' - b : ℚ) : K) ≠ 0 := by exact_mod_cast sub_ne_zero.2 hb.symm
  rw [Rat.cast_mul, Rat.cast_inv, inv_mul_eq_iff_eq_mul₀ hb']
  push_cast
  rw [sub_mul, sub_eq_sub_iff_add_eq_add, add_comm (_ * β), h, add_comm]

end TauCeti
