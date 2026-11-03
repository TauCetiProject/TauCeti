/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.AddChar

/-!
# Additive characters on rings of positive characteristic

## Main results

* `AddChar.pow_char_eq_one`: every additive character on a ring of characteristic `p`, such as
  `ZMod p`, takes values in the `p`-th roots of unity.
-/

public section

/-- An additive character on a ring of characteristic `p` takes values in the `p`-th roots of
unity; for instance every additive character on `ZMod p` does. -/
@[simp]
theorem AddChar.pow_char_eq_one {R M : Type*} [NonAssocSemiring R] (p : ℕ) [CharP R p]
    [Monoid M] (ψ : AddChar R M) (x : R) : ψ x ^ p = 1 := by
  simp [← AddChar.map_nsmul_eq_pow]
