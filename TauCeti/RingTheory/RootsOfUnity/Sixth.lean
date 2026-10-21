/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Sixth roots of unity and square roots of `-3`

When `6` is nonzero in a domain, the primitive sixth roots of unity are exactly the roots of the
sixth cyclotomic polynomial `X² - X + 1`. Completing the square, `ζ` is a primitive sixth root of
unity exactly when `2ζ - 1` is a square root of `-3`; in particular `(1 + √-3) / 2` is one.

## Main results

* `TauCeti.isPrimitiveRoot_six_iff`: `ζ` is a primitive sixth root of unity iff
  `ζ ^ 2 - ζ + 1 = 0`.
* `TauCeti.isPrimitiveRoot_one_add_div_two`: if `x ^ 2 = -3`, then `(1 + x) / 2` is a primitive
  sixth root of unity.
-/

public section

open Polynomial

namespace TauCeti

/-- **The primitive sixth roots of unity.** In a domain in which `6 ≠ 0`, `ζ` is a primitive sixth
root of unity exactly when it is a root of `X² - X + 1`. -/
theorem isPrimitiveRoot_six_iff {R : Type*} [CommRing R] [IsDomain R] [NeZero ((6 : ℕ) : R)]
    {ζ : R} : IsPrimitiveRoot ζ 6 ↔ ζ ^ 2 - ζ + 1 = 0 := by
  rw [← isRoot_cyclotomic_iff, cyclotomic_six]
  simp only [IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_one]

/-- **A primitive sixth root of unity from a square root of `-3`.** In a field in which `6 ≠ 0`, if
`x ^ 2 = -3` then `(1 + x) / 2` is a primitive sixth root of unity. -/
theorem isPrimitiveRoot_one_add_div_two {F : Type*} [Field F] [NeZero ((6 : ℕ) : F)] {x : F}
    (hx : x ^ 2 = -3) : IsPrimitiveRoot ((1 + x) / 2) 6 := by
  have h2 : (2 : F) ≠ 0 := fun h => NeZero.ne ((6 : ℕ) : F) (by push_cast; linear_combination 3 * h)
  rw [isPrimitiveRoot_six_iff]
  field_simp
  linear_combination hx

end TauCeti
