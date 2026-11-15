/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.Ring

/-!
# Vanishing cross terms over subfields

If `x²`, `a`, and `b` lie in a subfield but `x` does not, the square of `a + b * x` lies in
that subfield exactly when `a * b = 0`, provided the ambient field has characteristic different
from two.
This criterion is used in square-class descent through quadratic extensions.
-/

public section

namespace TauCeti

variable {L : Type*} [Field L]

/-- **Vanishing cross term in a quadratic step.** If `x² ∈ F` but `x ∉ F`, then for `a, b ∈ F`
the square `(a + b * x) ^ 2` lies in `F` exactly when its cross term vanishes: `a * b = 0`.
Characteristic not two enters through `2 ≠ 0` in `L`. It holds for an arbitrary subfield `F` of
`L`; no ambient base field or algebra tower is needed. -/
theorem add_mul_sq_mem_iff_mul_eq_zero {S : Type*} [SetLike S L] [SubfieldClass S L] {F : S}
    {x : L} (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) [NeZero (2 : L)] {a b : L} (ha : a ∈ F)
    (hb : b ∈ F) : (a + b * x) ^ 2 ∈ F ↔ a * b = 0 := by
  refine ⟨fun hab_mem => ?_, fun hab => ?_⟩
  · by_contra hab
    have h2ab : 2 * a * b ≠ 0 := by
      rw [mul_assoc]
      exact mul_ne_zero two_ne_zero hab
    -- Otherwise `x` is the cross term `(a + b * x) ^ 2 - a ^ 2 - b ^ 2 * x ^ 2` divided by its
    -- nonzero coefficient `2 * a * b`, and so lies in `F`.
    refine hxF ?_
    rw [← inv_mul_cancel_left₀ h2ab x,
      show 2 * a * b * x = (a + b * x) ^ 2 - a ^ 2 - b ^ 2 * x ^ 2 by ring]
    exact mul_mem (inv_mem (mul_mem (mul_mem (ofNat_mem F 2) ha) hb))
      (sub_mem (sub_mem hab_mem (pow_mem ha 2)) (mul_mem (pow_mem hb 2) hx2))
  · rcases mul_eq_zero.mp hab with rfl | rfl
    · simpa [mul_pow] using mul_mem (pow_mem hb 2) hx2
    · simpa using pow_mem ha 2

end TauCeti
