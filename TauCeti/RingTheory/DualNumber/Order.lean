/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DualNumber.Basic
public import TauCeti.RingTheory.Ideal.Order.Basic
import TauCeti.Algebra.DualNumber.Basic

/-!
# Ideal order on the dual numbers

Over a field `k`, the maximal ideal `𝔪` of the dual numbers `k[ε]` has local order `1`
(`DualNumber.localOrder_maximalIdeal`), while its square `𝔪² = ⊥` has local order `∞`.
-/

public section

namespace DualNumber

open IsLocalRing

/-- On the dual numbers `k[ε] / (ε²)` over a field `k`, the maximal ideal has local order `1`. -/
@[simp]
theorem localOrder_maximalIdeal {k : Type*} [Field k] :
    (maximalIdeal (DualNumber k)).localOrder = 1 := by
  refine le_antisymm (le_of_not_gt fun hlt ↦ ?_) ?_
  · have h2 : ((2 : ℕ) : ℕ∞) ≤ (maximalIdeal (DualNumber k)).localOrder := by
      have : ((1 : ℕ) : ℕ∞) + 1 ≤ (maximalIdeal (DualNumber k)).localOrder :=
        ENat.natCast_add_one_le_iff.mpr (by simpa using hlt)
      exact_mod_cast this
    rw [Ideal.natCast_le_localOrder_iff, maximalIdeal_sq_eq_bot,
      maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at h2
    exact eps_ne_zero h2
  · rw [← Nat.cast_one, Ideal.natCast_le_localOrder_iff, _root_.pow_one]

end DualNumber
