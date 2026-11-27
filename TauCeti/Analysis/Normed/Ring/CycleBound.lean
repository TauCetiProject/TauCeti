/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Integrality along a cycle in an ultrametric ring

Let `R` be an ultrametric seminormed ring with multiplicative seminorm. If two elements `x`, `y`
have `‖x + y‖ ≤ 1` and `‖x y‖ > 1`, then `‖x‖ = ‖y‖`, so `‖x‖² = ‖x y‖`
(`IsUltrametricDist.norm_sq_eq_norm_mul_of_norm_add_le_one`): a norm above one is replaced by its
square root. Iterating this along the orbits of a permutation of a finite set, which return to
their starting point, shows that numbers `s(c)` satisfying suitable relations between `c` and
`σ c` are integral (`IsUltrametricDist.norm_le_one_of_perm`).

This is the ultrametric step of the proof that the discriminant of a lattice with complex
multiplication, normalised at a point of order two, is a unit at every prime: there `σ` moves
along a chain of isogenies of degree two.

## References

* The statement follows `New.norm_le_one_of_cycle` in `Lib/CM/GoodReduction` of the folder `grh`
  of https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207
  (Apache 2.0, Copyright 2026 Anthropic PBC), stated there for a finite group acting on itself.
-/

public section

namespace IsUltrametricDist

variable {R : Type*} [SeminormedRing R] [NormMulClass R] [IsUltrametricDist R]

/-- In an ultrametric ring with multiplicative seminorm, if `‖x + y‖ ≤ 1` and `1 < ‖x y‖`, then
`‖x‖ = ‖y‖`, so `‖x‖² = ‖x y‖`. -/
theorem norm_sq_eq_norm_mul_of_norm_add_le_one {x y : R} (h_add : ‖x + y‖ ≤ 1)
    (h_mul : 1 < ‖x * y‖) : ‖x‖ ^ 2 = ‖x * y‖ := by
  -- one of the two norms exceeds `1`, so the sum is shorter than the longer side
  have h_max : ‖x + y‖ < max ‖x‖ ‖y‖ := by
    refine h_add.trans_lt (lt_max_iff.mpr ?_)
    by_contra! h
    rw [norm_mul] at h_mul
    nlinarith [norm_nonneg x, norm_nonneg y]
  have h_eq := norm_eq_of_add_norm_lt_max h_max
  rw [norm_mul, ← h_eq, sq]

/-- **Integrality along a cycle.** Let `σ` be a permutation of a finite set and `s`, `s'`, `s₀`
functions with values in an ultrametric ring with multiplicative seminorm such that, for every
`c`, the sum `s c + s' c + s₀ c` and the product `s c * s' (σ c)` are integral, and
`‖s (σ c) * s₀ (σ c)‖ = ‖s c‖`. Then every `s c` is integral: a norm `‖s c‖ > 1` would be replaced
by its square root at each step `c ↦ σ c`, and the steps return to `c`. -/
theorem norm_le_one_of_perm {X : Type*} [Finite X] (σ : Equiv.Perm X) {s s' s₀ : X → R}
    (h_sum : ∀ c, ‖s c + s' c + s₀ c‖ ≤ 1) (h_dual : ∀ c, ‖s c * s' (σ c)‖ ≤ 1)
    (h_step : ∀ c, ‖s (σ c) * s₀ (σ c)‖ = ‖s c‖) (c : X) : ‖s c‖ ≤ 1 := by
  have halve (c : X) (hc : 1 < ‖s c‖) : ‖s (σ c)‖ ^ 2 = ‖s c‖ := by
    have hs' : ‖s' (σ c)‖ ≤ 1 := by
      have := h_dual c
      rw [norm_mul] at this
      nlinarith [norm_nonneg (s' (σ c))]
    have h_add : ‖s (σ c) + s₀ (σ c)‖ ≤ 1 := by
      have h := (norm_add_le_max (s (σ c) + s' (σ c) + s₀ (σ c)) (-s' (σ c))).trans
        (max_le (h_sum (σ c)) (by rwa [norm_neg]))
      rwa [add_right_comm, add_neg_cancel_right] at h
    rw [norm_sq_eq_norm_mul_of_norm_add_le_one h_add (by rwa [h_step]), h_step]
  by_contra! hc
  -- along the orbit, `‖s ((σ ^ i) c)‖ ^ 2 ^ i = ‖s c‖ > 1`
  have iterate (i : ℕ) : ‖s ((σ ^ i) c)‖ ^ 2 ^ i = ‖s c‖ := by
    induction i with
    | zero => simp
    | succ i ih =>
      have h_gt : 1 < ‖s ((σ ^ i) c)‖ :=
        lt_of_pow_lt_pow_left₀ (2 ^ i) (norm_nonneg _) (by rwa [one_pow, ih])
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ, pow_mul', halve _ h_gt, ih]
  -- at `i = orderOf σ` this says `‖s c‖ ^ 2 ^ i = ‖s c‖`
  have h := iterate (orderOf σ)
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at h
  exact (lt_self_pow₀ hc (Nat.one_lt_two_pow (orderOf_pos σ).ne')).ne' h

end IsUltrametricDist
