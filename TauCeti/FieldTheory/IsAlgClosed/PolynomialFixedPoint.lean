/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Nonzero fixed points of polynomials over algebraically closed fields

Over an algebraically closed field, a nonzero polynomial `g` divisible by `X ^ 2` has a nonzero
fixed point: writing `g = X ^ 2 * h`, any root `t` of `X * h - 1` satisfies `g t = t`.

This is used to find nonzero fixed vectors of Frobenius-semilinear maps, where the fixed-point
condition reduces to an equation `∑ cᵢ t ^ (qⁱ) = t` with every exponent `qⁱ ≥ 2`.

## Main results

* `IsAlgClosed.exists_ne_zero_eval_eq_self`: a nonzero `g` with `X ^ 2 ∣ g` has a nonzero `t`
  with `g.eval t = t`.
-/

public section

open Polynomial

namespace IsAlgClosed

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, a nonzero polynomial divisible by `X ^ 2` has a nonzero
fixed point. -/
theorem exists_ne_zero_eval_eq_self {g : k[X]} (hg : g ≠ 0) (h2 : X ^ 2 ∣ g) :
    ∃ t ≠ 0, g.eval t = t := by
  obtain ⟨h, rfl⟩ := h2
  have hh : h ≠ 0 := right_ne_zero_of_mul hg
  have hdeg : (X * h - 1).natDegree = h.natDegree + 1 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hh]
  obtain ⟨t, ht⟩ := exists_root (X * h - 1)
    (degree_ne_of_natDegree_ne (by rw [hdeg]; exact Nat.succ_ne_zero _))
  have ht' : t * h.eval t = 1 := by simpa [sub_eq_zero] using ht
  refine ⟨t, fun h0 ↦ by simp [h0] at ht', ?_⟩
  rw [eval_mul, eval_pow, eval_X, sq, mul_assoc, ht', mul_one]

end IsAlgClosed
