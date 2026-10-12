/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# A square root of five from a fifth root of unity

For a primitive fifth root of unity `ζ`, the element `1 + 2 * (ζ + ζ⁻¹)` squares to `5`.
This gives an explicit generator of the quadratic subfield of the fifth cyclotomic field.
The identity itself holds in arbitrary characteristic.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 1.
-/

public section

namespace IsPrimitiveRoot

/-- A primitive fifth root of unity gives a square root of five. -/
@[simp] theorem one_add_two_mul_add_inv_sq_of_five {K : Type*} [Field K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) : (1 + 2 * (ζ + ζ⁻¹)) ^ 2 = 5 := by
  have hsum := hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
  norm_num [Finset.sum_range_succ] at hsum
  have hne := hζ.ne_zero (by norm_num : 5 ≠ 0)
  field_simp
  linear_combination 4 * hsum

end IsPrimitiveRoot
