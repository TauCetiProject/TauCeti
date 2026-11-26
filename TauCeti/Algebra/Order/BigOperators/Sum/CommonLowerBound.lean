/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Contraction of combinations of rows with a common lower bound

Let `β τ`, for `τ ∈ s`, be rows of total mass one on `t`, all dominating one vector `δ` of total
mass `c` on `t`, and let `a` be weights on `s` with sum zero. In the combination
`∑ τ, a τ * β τ` the common part `δ` cancels, so its `ℓ¹` norm on `t` is at most `1 - c` times
the `ℓ¹` norm of `a` (`TauCeti.sum_abs_sum_mul_le`). This is the contraction estimate for
stochastic matrices satisfying Doeblin's condition.
-/

public section

namespace TauCeti

open Finset

variable {A B R : Type*} [CommRing R] [LinearOrder R] [IsOrderedRing R]

/-- **The contraction estimate under a common lower bound (Doeblin's condition).** Let `a` be
weights on `s` with sum zero, and let every row `β τ`, `τ ∈ s`, have total mass one on `t` and
dominate a common vector `δ` of total mass `c` on `t`. Then the `ℓ¹` norm on `t` of
`∑ τ, a τ β τ` is at most `1 - c` times the `ℓ¹` norm of `a`: the common part `δ` cancels. -/
theorem sum_abs_sum_mul_le {s : Finset A} {t : Finset B} {a : A → R} {β : A → B → R}
    {δ : B → R} {c : R} (ha : ∑ τ ∈ s, a τ = 0) (hβδ : ∀ τ ∈ s, ∀ v, 0 ≤ β τ v - δ v)
    (hβ : ∀ τ ∈ s, ∑ v ∈ t, β τ v = 1) (hδ : ∑ v ∈ t, δ v = c) :
    ∑ v ∈ t, |∑ τ ∈ s, a τ * β τ v| ≤ (1 - c) * ∑ τ ∈ s, |a τ| := by
  have hpt (v : B) : |∑ τ ∈ s, a τ * β τ v| ≤ ∑ τ ∈ s, |a τ| * (β τ v - δ v) := by
    have heq : ∑ τ ∈ s, a τ * β τ v = ∑ τ ∈ s, a τ * (β τ v - δ v) := by
      rw [sum_congr rfl fun τ _ => mul_sub _ _ _, sum_sub_distrib, ← sum_mul, ha, zero_mul,
        sub_zero]
    rw [heq]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun τ hτ => ?_)
    rw [abs_mul, abs_of_nonneg (hβδ τ hτ v)]
  calc ∑ v ∈ t, |∑ τ ∈ s, a τ * β τ v|
      ≤ ∑ v ∈ t, ∑ τ ∈ s, |a τ| * (β τ v - δ v) := sum_le_sum fun v _ => hpt v
    _ = (1 - c) * ∑ τ ∈ s, |a τ| := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun τ hτ => ?_
        rw [← mul_sum, sum_sub_distrib, hβ τ hτ, hδ, mul_comm]

end TauCeti
