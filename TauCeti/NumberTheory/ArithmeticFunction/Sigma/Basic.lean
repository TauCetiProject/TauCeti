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
# The divisor power sums and `ζ * ζ = σ 0`

* `ArithmeticFunction.zeta_mul_zeta`, `ArithmeticFunction.coe_zeta_mul_coe_zeta`: the Dirichlet
  square of `ζ` is the divisor-count function `σ 0`.
* `ArithmeticFunction.sigma_prime_pow_succ`: the recurrence `σ_j(p^{m+1}) = p^j σ_j(p^m) + 1`.
-/

public section

open Finset
open scoped ArithmeticFunction.sigma ArithmeticFunction.zeta

namespace ArithmeticFunction

/-- The Dirichlet square of `ζ` is the divisor-count function `σ 0`. -/
theorem zeta_mul_zeta : (ζ * ζ : ArithmeticFunction ℕ) = σ 0 :=
  pow_zero_eq_zeta ▸ zeta_mul_pow_eq_sigma

/-- The Dirichlet square of `ζ` in `ArithmeticFunction R` is `σ 0`. -/
theorem coe_zeta_mul_coe_zeta {R : Type*} [Semiring R] : (ζ * ζ : ArithmeticFunction R) = σ 0 := by
  rw [← natCoe_mul, zeta_mul_zeta]

/-- The prime-power recurrence for the divisor power sum: `σ_j(p^{m+1}) = p^j σ_j(p^m) + 1`. -/
theorem sigma_prime_pow_succ {j p : ℕ} (hp : p.Prime) (m : ℕ) :
    σ j (p ^ (m + 1)) = p ^ j * σ j (p ^ m) + 1 := by
  have hsum (n : ℕ) : σ j (p ^ n) = ∑ i ∈ range (n + 1), (p ^ j) ^ i := by
    rw [sigma_apply_prime_pow hp]
    exact sum_congr rfl fun i _ ↦ by rw [← pow_mul, mul_comm]
  rw [hsum, hsum]
  exact geom_sum_succ

end ArithmeticFunction
