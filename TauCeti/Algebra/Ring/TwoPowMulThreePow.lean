/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.Defs

/-!
# Numerals of the form `2 ^ m * 3 ^ n`

A numeral whose only prime factors are `2` and `3` — `6`, `12`, `48`, `864`, `1728` — is a unit as
soon as `2` and `3` are, and in a nontrivial ring it is nonzero. Such numerals are the denominators
of the classical invariants of a Weierstrass equation, so the two statements below are the side
conditions that a computation over a ring where `2` and `3` are invertible keeps presenting,
`field_simp` included.

Both are phrased with the numeral as a *hypothesis*, `x = 2 ^ m * 3 ^ n`, rather than with
`2 ^ m * 3 ^ n` in the conclusion: `x` is then a numeral literal at the use site and the exponents
are supplied by `norm_num`, which is what makes the lemmas usable on `48` or `1728` without a
preparatory rewrite.

## Main results

* `TauCeti.isUnit_of_eq_two_pow_mul_three_pow`: in a semiring where `2` and `3` are units, so is
  `2 ^ m * 3 ^ n`.
* `TauCeti.ne_zero_of_eq_two_pow_mul_three_pow`: the same conclusion as nonvanishing, stated for
  `Invertible` instances, which is how a field of characteristic other than `2` and `3` carries
  the hypothesis (Mathlib's Weierstrass normal-form API asks for it in that form too).
-/

public section

namespace TauCeti

variable {R : Type*} [Semiring R] {x : R} {m n : ℕ}

/-- **A numeral built from `2` and `3` is a unit once `2` and `3` are.** -/
theorem isUnit_of_eq_two_pow_mul_three_pow (h2 : IsUnit (2 : R)) (h3 : IsUnit (3 : R))
    (hx : x = 2 ^ m * 3 ^ n) : IsUnit x :=
  hx ▸ (h2.pow m).mul (h3.pow n)

/-- **A numeral built from `2` and `3` is nonzero where `2` and `3` are invertible.** For a
hypothesis in `IsUnit` form, use `TauCeti.isUnit_of_eq_two_pow_mul_three_pow` and
`IsUnit.ne_zero`. -/
theorem ne_zero_of_eq_two_pow_mul_three_pow [Nontrivial R] [Invertible (2 : R)]
    [Invertible (3 : R)] (hx : x = 2 ^ m * 3 ^ n) : x ≠ 0 :=
  (isUnit_of_eq_two_pow_mul_three_pow (isUnit_of_invertible 2) (isUnit_of_invertible 3) hx).ne_zero

end TauCeti
