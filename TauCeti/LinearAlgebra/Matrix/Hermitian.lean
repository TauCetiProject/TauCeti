/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Nilpotent Hermitian matrices

Over a star-ordered ring whose star is proper, such as `ℝ` or `ℂ`, a Hermitian matrix `H`
with `H * H = Hᴴ * H = 0` is zero (`Matrix.conjTranspose_mul_self_eq_zero`). Since the powers of a
Hermitian matrix are Hermitian, peeling off squares shows that a nilpotent Hermitian matrix is
zero. This is what rules out nonzero nilpotent ideals in an algebra of matrices closed under
conjugate transposition.

## Main results

* `Matrix.IsHermitian.eq_zero_of_isNilpotent`: a nilpotent Hermitian matrix is zero.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [Ring R] [PartialOrder R] [StarRing R]
  [StarOrderedRing R] [IsProperStar R]

/-- **A nilpotent Hermitian matrix is zero** over a star-ordered ring with a proper star. Some
such hypothesis is needed: over `ZMod 2` the symmetric matrix `!![1, 1; 1, 1]` squares to zero. -/
theorem IsHermitian.eq_zero_of_isNilpotent {H : Matrix n n R} (hH : H.IsHermitian)
    (hnil : IsNilpotent H) : H = 0 := by
  obtain ⟨m, hm⟩ := hnil
  -- `H ^ 2 ^ (j + 1) = (H ^ 2 ^ j)ᴴ * H ^ 2 ^ j`, so each vanishing power of the form `2 ^ j`
  -- forces the previous one to vanish
  have key (j : ℕ) (hj : H ^ 2 ^ j = 0) : H = 0 := by
    induction j with
    | zero => simpa using hj
    | succ j ih =>
      refine ih (conjTranspose_mul_self_eq_zero.mp ?_)
      rw [(hH.pow (2 ^ j)).eq, ← pow_add, ← two_mul, ← pow_succ']
      exact hj
  exact key m (pow_eq_zero_of_le m.lt_two_pow_self.le hm)

end Matrix
