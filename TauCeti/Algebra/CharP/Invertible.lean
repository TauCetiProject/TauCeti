/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Invertible.Defs
public import Mathlib.Algebra.Module.Defs

/-!
# Elements equal to their own negative when `2` is invertible

If `2` is invertible in the scalar semiring `R`, then an element `x` of an `R`-module with
`x = -x` is zero: `x = ⅟2 • (x + x) = ⅟2 • (x + -x) = 0`. Mathlib's `self_eq_neg` asks instead
for the module to be additively torsion-free, which fails for instance over `ZMod 3`.

## Main results

* `TauCeti.eq_zero_of_eq_neg_of_invertible_two`: `x = -x` forces `x = 0`.
-/

public section

namespace TauCeti

/-- If `2` is invertible in the scalars, an element of a module equal to its own negative is
zero. -/
theorem eq_zero_of_eq_neg_of_invertible_two {R M : Type*} [Semiring R] [Invertible (2 : R)]
    [AddCommGroup M] [Module R M] {x : M} (h : x = -x) : x = 0 := by
  have h2 : x + x = 0 := (congrArg (x + ·) h).trans (add_neg_cancel x)
  calc x = (⅟2 * 2 : R) • x := by rw [invOf_mul_self, one_smul]
    _ = 0 := by rw [mul_smul, two_smul, h2, smul_zero]

end TauCeti
