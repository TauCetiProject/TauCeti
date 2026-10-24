/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Nat.Find

/-!
# Strings of powers acting on a vector

For a monoid `M` acting on a type `V` with a zero, an element `x : M` and a vector `w : V`, the
`x`-string of `w` is the sequence `w, x • w, x² • w, …`. This file shows that if the string
reaches `0` and `w ≠ 0`, then it has a last nonzero vector, which `x` sends to `0`. Raising and
lowering operators of representations, such as `E` and `F` for `U_q(sl₂)`, use this to produce
highest- and lowest-weight vectors.

## Main results

* `TauCeti.exists_pow_smul_ne_zero_and_smul_eq_zero`: if `xⁿ • w = 0` for some `n` and `w ≠ 0`,
  then `xⁿ • w ≠ 0` and `x • xⁿ • w = 0` for some `n`.
-/

public section

namespace TauCeti

variable {M V : Type*} [Monoid M] [MulAction M V] [Zero V]

/-- If some power of `x` kills a nonzero vector `w`, then the string `w, x • w, x² • w, …` ends
in a nonzero vector `xⁿ • w` killed by `x`. -/
theorem exists_pow_smul_ne_zero_and_smul_eq_zero {x : M} {w : V} (hw0 : w ≠ 0)
    (h : ∃ n : ℕ, x ^ n • w = 0) : ∃ n : ℕ, x ^ n • w ≠ 0 ∧ x • x ^ n • w = 0 := by
  classical
  have hn : 0 < Nat.find h :=
    Nat.pos_of_ne_zero fun hn ↦ hw0 (by simpa [hn] using Nat.find_spec h)
  refine ⟨Nat.find h - 1, Nat.find_min h (by omega), ?_⟩
  rw [← mul_smul, ← pow_succ', Nat.sub_add_cancel hn]
  exact Nat.find_spec h

end TauCeti
