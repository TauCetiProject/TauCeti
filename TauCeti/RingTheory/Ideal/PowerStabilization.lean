/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import TauCeti.Algebra.Algebra.Operations

/-!
# Stabilization of the powers of an ideal

A criterion for the powers of an ideal `I` to become constant: if some `i ∈ I` is such that
`1 + i` annihilates `I ^ n`, then `I ^ (n + 1) = I ^ n`, and hence, by
`Submodule.pow_eq_pow_of_pow_succ_eq_pow`, the powers are constant from `n` on. The ring need not
be commutative.

In Wedhorn's proof of Proposition 7.49(2) such an `i` is produced from a finitely generated `I` by
localizing at `1 + I`; that step is not part of this file.

## Main results

* `Ideal.pow_succ_eq_pow_of_forall_mul_eq_zero`: an `i ∈ I` whose `1 + i` annihilates `I ^ n`
  gives `I ^ (n + 1) = I ^ n`.
* `Ideal.pow_eq_pow_of_forall_mul_eq_zero`: hence `I ^ k = I ^ n` for all `k ≥ n`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], proof of Proposition 7.49(2), where this criterion is
  the closing step.
-/

public section

namespace Ideal

variable {R : Type*} [Ring R] {I : Ideal R} {i : R} {n : ℕ}

/-- If some `i ∈ I` is such that `1 + i` annihilates `I ^ n`, then `I ^ (n + 1) = I ^ n`. -/
theorem pow_succ_eq_pow_of_forall_mul_eq_zero (hi : i ∈ I) (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) :
    I ^ (n + 1) = I ^ n := by
  -- For `n ≠ 0`, `x = -(i * x)` lies in `I * I ^ n = I ^ (n + 1)`. At `n = 0` that identity fails
  -- for a left ideal; instead `1 + i` annihilating `1` puts `1 = -i` in `I`.
  refine le_antisymm (Ideal.pow_le_pow_right n.le_succ) fun x hx ↦ ?_
  obtain rfl | hn := eq_or_ne n 0
  · have hone : (1 : R) = -i := eq_neg_of_add_eq_zero_left <| by
      simpa using h 1 (by simp [Submodule.pow_zero, one_eq_top])
    simp [(eq_top_iff_one I).mpr (hone ▸ neg_mem hi), Submodule.pow_one]
  · rw [eq_neg_of_add_eq_zero_left (by rw [← one_add_mul, h x hx] : x + i * x = 0),
      I.pow_succ' hn]
    exact neg_mem (mul_mem_mul hi hx)

/-- If some `i ∈ I` is such that `1 + i` annihilates `I ^ n`, then the powers of `I` are constant
from `n` on. -/
theorem pow_eq_pow_of_forall_mul_eq_zero (hi : i ∈ I) (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) {k : ℕ}
    (hk : n ≤ k) : I ^ k = I ^ n :=
  Submodule.pow_eq_pow_of_pow_succ_eq_pow (pow_succ_eq_pow_of_forall_mul_eq_zero hi h) hk

end Ideal
