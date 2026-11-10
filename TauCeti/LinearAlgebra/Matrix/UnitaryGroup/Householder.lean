/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.Module

/-!
# Householder reflections over a star ring

Let `α` be a star ring that is an algebra over a commutative ring `R` with trivial star, such as
the quaternions over `ℝ`. For a vector `v` with Hermitian square `vᴴ v = s ∈ R` and a scalar `c`
with `c² s = 2 c`, the matrix `H = 1 - c v vᴴ` is Hermitian and squares to the identity, hence
is unitary. For `s` invertible and `c = 2 / s` this is the Householder reflection in `v`. No
commutativity of `α` is assumed.

## Main results

* `Matrix.one_sub_smul_vecMulVec_mem_unitary`: the matrix `1 - c v vᴴ` is unitary when
  `vᴴ v = s` and `c² s = 2 c`.
-/

public section

open scoped Matrix

namespace Matrix

variable {R α n : Type*} [CommRing R] [StarRing R] [TrivialStar R] [Ring α] [StarRing α]
  [Algebra R α] [StarModule R α] [Fintype n] [DecidableEq n]

/-- **A Householder reflection is unitary.** If `vᴴ v = s` and `c² s = 2 c`, then
`H = 1 - c v vᴴ` is a Hermitian involution, hence unitary. -/
theorem one_sub_smul_vecMulVec_mem_unitary {v : n → α} {s c : R}
    (hvv : star v ⬝ᵥ v = algebraMap R α s) (hc : c * c * s = 2 * c) :
    1 - c • vecMulVec v (star v) ∈ unitary (Matrix n n α) := by
  set P := vecMulVec v (star v)
  have hPP : P * P = s • P := by
    rw [vecMulVec_mul_vecMulVec, hvv, algebraMap_smul, vecMulVec_smul]
  have hH : star (1 - c • P) = 1 - c • P := by
    rw [star_sub, star_one, star_smul, star_trivial, star_eq_conjTranspose,
      conjTranspose_vecMulVec, star_star]
  have hHH : (1 - c • P) * (1 - c • P) = 1 := by
    calc (1 - c • P) * (1 - c • P) = 1 - (2 * c - c * c * s) • P := by
          simp only [sub_mul, mul_sub, mul_one, one_mul, smul_mul_smul_comm, hPP, smul_smul]
          module
      _ = 1 := by rw [hc, sub_self, zero_smul, sub_zero]
  exact ⟨by rw [hH, hHH], by rw [hH, hHH]⟩

end Matrix
