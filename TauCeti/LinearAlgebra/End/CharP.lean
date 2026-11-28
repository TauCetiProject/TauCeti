/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Endomorphisms of modules over a ring of prime characteristic

Over a commutative ring `k` of prime characteristic `p`, the identity
`X ^ p ^ a - 1 = (X - 1) ^ p ^ a` of polynomials over `k` shows that `y ^ p ^ a - 1` is the
`p ^ a`-th power of `y - 1` for every endomorphism `y` of a `k`-module. The module itself need not
have characteristic `p` as a ring of endomorphisms: it may be zero.

## Main results

* `Module.End.injective_pow_char_pow_sub_one`: if `y - 1` is injective, so is `y ^ p ^ a - 1`.
-/

public section

namespace Module.End

variable {k : Type*} [CommRing k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {N : Type*} [AddCommGroup N] [Module k N]

/-- In characteristic `p`, if `y - 1` is injective then so is `y ^ p ^ a - 1`, because
`y ^ p ^ a - 1 = (y - 1) ^ p ^ a`. -/
theorem injective_pow_char_pow_sub_one {y : Module.End k N} (hy : Function.Injective ⇑(y - 1))
    (a : ℕ) : Function.Injective ⇑(y ^ p ^ a - 1) := by
  have h := congrArg (Polynomial.aeval y)
    (sub_pow_char_pow (p := p) (n := a) (Polynomial.X : Polynomial k) 1)
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one, one_pow] at h
  rw [← h, FunLike.coe_pow_eq_iterate]
  exact hy.iterate _

end Module.End
