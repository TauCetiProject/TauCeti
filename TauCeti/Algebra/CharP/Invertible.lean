/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Module.Defs

/-!
# Elements equal to their own negative when `2` is invertible

If `2` is invertible in the scalar semiring `R`, then an element `x` of an `R`-module with
`x = -x` is zero: `x = ⅟2 • (x + x) = ⅟2 • (x + -x) = 0`. Mathlib's `self_eq_neg` asks instead
for the module to be additively torsion-free, which fails for instance over `ZMod 3`.

The same cancellation gives a scalar parity criterion: if `(-1) ^ n` fixes a nonzero vector,
then `n` is even. It applies when `2` is given as a unit, without a chosen inverse.

## Main results

* `TauCeti.eq_zero_of_eq_neg_of_invertible_two`: `x = -x` forces `x = 0`.
* `TauCeti.even_of_neg_one_pow_smul_eq_self`: `(-1) ^ n • v = v` for nonzero `v`
  forces `n` to be even when `2` is a unit.
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

/-- If `(-1) ^ n • v = v` for nonzero `v` and a unit scalar `2`, then `n` is even. -/
theorem even_of_neg_one_pow_smul_eq_self {R N : Type*} [Ring R] [AddCommGroup N] [Module R N]
    {n : ℕ} {v : N} (h2 : IsUnit (2 : R)) (hv : v ≠ 0)
    (h : (-1 : R) ^ n • v = v) : Even n := by
  rcases Nat.even_or_odd n with hn | hn
  · exact hn
  · exfalso
    obtain ⟨hinv⟩ := h2.nonempty_invertible
    let := hinv
    exact hv (eq_zero_of_eq_neg_of_invertible_two (R := R)
      (by simpa [hn.neg_one_pow] using h.symm))

end TauCeti
