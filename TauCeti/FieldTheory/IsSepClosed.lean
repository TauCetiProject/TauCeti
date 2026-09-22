/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
-- Proof-only: the quadratic formula, which solves the equation once the discriminant is a square.
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Quadratics over a separably closed field

A separably closed field solves every quadratic **except** the inseparable ones. A quadratic
`a X² + b X + c` with `a ≠ 0` is inseparable exactly when its derivative `2a X + b` vanishes, that
is when `2 = 0` and `b = 0`; away from that case the equation has a root in the field itself.

Both halves are already available. Where `2 ≠ 0` the quadratic formula applies as soon as the
discriminant is a square, and a separably closed field supplies square roots
(`IsSepClosed.exists_eq_mul_self`). Where `2 = 0` the polynomial `a X² + b X + c` with `b ≠ 0` is
separable, and `IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C` is exactly that case.

The excluded case is genuinely excluded: over an imperfect separably closed field of
characteristic `2`, such as the separable closure of `𝔽₂(t)`, the equation `X² = t` has no
solution.

## Main results

* `TauCeti.exists_quadratic_eq_zero_of_isSepClosed`
-/

public section

namespace TauCeti

/-- **A quadratic with a nonvanishing derivative has a root in a separably closed field.** The
derivative of `a X² + b X + c` is `2a X + b`, so the hypothesis `2 ≠ 0 ∨ b ≠ 0` says exactly that
the quadratic is separable; without it the equation can be `X² = t` for a non-square `t`, which has
no solution over an imperfect separably closed field of characteristic `2`. -/
theorem exists_quadratic_eq_zero_of_isSepClosed {K : Type*} [Field K] [IsSepClosed K] {a : K}
    (ha : a ≠ 0) (b c : K) (h : (2 : K) ≠ 0 ∨ b ≠ 0) :
    ∃ x : K, a * (x * x) + b * x + c = 0 := by
  by_cases h2 : (2 : K) = 0
  · obtain ⟨x, hx⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C (n := 2) a b c
      (by exact_mod_cast h2) le_rfl (h.resolve_left (not_not_intro h2))
    exact ⟨x, by linear_combination hx⟩
  · have : NeZero (2 : K) := ⟨h2⟩
    exact exists_quadratic_eq_zero ha (IsSepClosed.exists_eq_mul_self (discrim a b c))

end TauCeti

end
