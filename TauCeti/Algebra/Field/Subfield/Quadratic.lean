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

If `x²` lies in a subfield but `x` does not, squaring `a + b * x` can land in that subfield
only when `a * b = 0`, provided the ambient field has characteristic different from two.
This criterion is used in square-class descent through quadratic extensions.
-/

public section

namespace TauCeti

variable {L : Type*} [Field L]

/-- **Vanishing cross term in a quadratic step.** If `x² ∈ F` but `x ∉ F`, then a square
`(a + b * x) ^ 2` of a normal-form element that lands back in `F` has no cross term: `a * b = 0`.
This is where characteristic not two enters, through `2 ≠ 0` in `L`. It holds for an arbitrary
subfield `F` of `L`; no ambient base field or algebra tower is needed. -/
theorem mul_eq_zero_of_add_mul_sq_mem {S : Type*} [SetLike S L] [SubfieldClass S L] {F : S} {x : L}
    (hx2 : x ^ 2 ∈ F) (hxF : x ∉ F) [NeZero (2 : L)] {a b : L}
    (ha : a ∈ F) (hb : b ∈ F) (hab_mem : (a + b * x) ^ 2 ∈ F) :
    a * b = 0 := by
  by_contra hab
  refine hxF ?_
  -- Expanding `(a + b * x) ^ 2` and using `x² ∈ F`, the cross term `2 * a * b * x` lies in `F`.
  have hcross_mem : 2 * a * b * x ∈ F := by
    have hEq : 2 * a * b * x = (a + b * x) ^ 2 - a ^ 2 - b ^ 2 * x ^ 2 := by ring
    rw [hEq]
    exact sub_mem (sub_mem hab_mem (pow_mem ha 2)) (mul_mem (pow_mem hb 2) hx2)
  -- The coefficient `2 * a * b` lies in `F` and is nonzero, so `x` is recovered by dividing it out.
  have hcoef_mem : 2 * a * b ∈ F := mul_mem (mul_mem (natCast_mem (s := F) 2) ha) hb
  have hcoef_ne : 2 * a * b ≠ 0 := by
    have h2ab : (2 : L) * (a * b) ≠ 0 := mul_ne_zero (NeZero.ne (2 : L)) hab
    simpa [mul_assoc] using h2ab
  have hxeq : (2 * a * b)⁻¹ * (2 * a * b * x) = x := by
    rw [← mul_assoc, inv_mul_cancel₀ hcoef_ne, one_mul]
  rw [← hxeq]
  exact mul_mem (inv_mem hcoef_mem) hcross_mem

end TauCeti
