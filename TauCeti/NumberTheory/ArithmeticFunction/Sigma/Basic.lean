/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Ring.GeomSum

/-!
# The divisor power sums at prime powers

* `ArithmeticFunction.sigma_prime_pow_succ`: the recurrence `σ_j(p^{m+1}) = p^j σ_j(p^m) + 1`.
-/

public section

open Finset
open scoped ArithmeticFunction.sigma

namespace ArithmeticFunction

/-- The prime-power recurrence for the divisor power sum: `σ_j(p^{m+1}) = p^j σ_j(p^m) + 1`. -/
theorem sigma_prime_pow_succ {j p : ℕ} (hp : p.Prime) (m : ℕ) :
    σ j (p ^ (m + 1)) = p ^ j * σ j (p ^ m) + 1 := by
  have hsum (n : ℕ) : σ j (p ^ n) = ∑ i ∈ range (n + 1), (p ^ j) ^ i := by
    rw [sigma_apply_prime_pow hp]
    exact sum_congr rfl fun i _ ↦ by rw [← pow_mul, mul_comm]
  rw [hsum, hsum]
  exact geom_sum_succ

end ArithmeticFunction
