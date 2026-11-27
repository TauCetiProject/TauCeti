/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import TauCeti.Data.Nat.Interval

/-!
# The divisor power sums and `ζ * ζ = σ 0`

* `ArithmeticFunction.zeta_mul_zeta`, `ArithmeticFunction.coe_zeta_mul_coe_zeta`: the Dirichlet
  square of `ζ` is the divisor-count function `σ 0`.
* `ArithmeticFunction.sigma_prime_pow_succ`: the recurrence `σ_j(p^{m+1}) = p^j σ_j(p^m) + 1`.
* `TauCeti.sum_Ioc_sigma_zero_add_sqrt_sq`: Dirichlet's hyperbola identity
  `∑_{n ≤ N} σ₀(n) + ⌊√N⌋² = 2 ∑_{a ≤ ⌊√N⌋} ⌊N / a⌋`.
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

namespace TauCeti

/-- **Dirichlet's hyperbola identity** for the divisor function:
`∑_{n ≤ N} τ(n) + M² = 2 ∑_{a ≤ M} ⌊N / a⌋`, where `M = ⌊√N⌋`. Both sides count the pairs
`(a, b)` of positive integers with `a * b ≤ N`, the pairs with `a ≤ M` and `b ≤ M` twice. -/
theorem sum_Ioc_sigma_zero_add_sqrt_sq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, σ 0 n + N.sqrt ^ 2 = 2 * ∑ a ∈ Ioc 0 N.sqrt, N / a := by
  have hN : N < (N.sqrt + 1) * (N.sqrt + 1) := Nat.sqrt_lt.1 (Nat.lt_add_one N.sqrt)
  -- The pairs with `a > M` have `b ≤ M`; count them by `b` instead of by `a`.
  have hswap : ∑ a ∈ Ioc N.sqrt N, N / a = ∑ b ∈ Ioc 0 N.sqrt, (N / b - N.sqrt) :=
    calc ∑ a ∈ Ioc N.sqrt N, N / a
        = ∑ a ∈ Ioc N.sqrt N, ∑ b ∈ Ioc 0 N.sqrt, if a * b ≤ N then 1 else 0 :=
          sum_congr rfl fun a ha ↦ by
            have ha' := (mem_Ioc.1 ha).1
            have hle : N / a ≤ N.sqrt :=
              Nat.le_of_lt_add_one ((Nat.div_lt_iff_lt_mul (by omega)).2 (by nlinarith))
            rw [← card_filter, Nat.card_filter_Ioc_mul_le (by omega), min_eq_right hle,
              Nat.sub_zero]
      _ = ∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc N.sqrt N, if b * a ≤ N then 1 else 0 := by
          rw [sum_comm]
          simp only [mul_comm]
      _ = ∑ b ∈ Ioc 0 N.sqrt, (N / b - N.sqrt) :=
          sum_congr rfl fun b hb ↦ by
            rw [← card_filter, Nat.card_filter_Ioc_mul_le (mem_Ioc.1 hb).1,
              min_eq_right (Nat.div_le_self N b)]
  have hge : ∀ b ∈ Ioc 0 N.sqrt, N.sqrt ≤ N / b := fun b hb ↦ by
    rw [Nat.le_div_iff_mul_le (mem_Ioc.1 hb).1]
    exact (Nat.mul_le_mul_left _ (mem_Ioc.1 hb).2).trans (Nat.sqrt_le N)
  have hsq : N.sqrt ^ 2 = ∑ _b ∈ Ioc 0 N.sqrt, N.sqrt := by simp [sq]
  calc ∑ n ∈ Ioc 0 N, σ 0 n + N.sqrt ^ 2
      = ∑ a ∈ Ioc 0 N, N / a + N.sqrt ^ 2 := by
        rw [ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div]
    _ = ∑ a ∈ Ioc 0 N.sqrt, N / a + ∑ a ∈ Ioc N.sqrt N, N / a + N.sqrt ^ 2 := by
        rw [sum_Ioc_consecutive (fun a ↦ N / a) (Nat.zero_le _) (Nat.sqrt_le_self N)]
    _ = ∑ a ∈ Ioc 0 N.sqrt, N / a +
          ∑ b ∈ Ioc 0 N.sqrt, (N / b - N.sqrt + N.sqrt) := by
        rw [hswap, hsq, add_assoc, ← sum_add_distrib]
    _ = ∑ a ∈ Ioc 0 N.sqrt, N / a + ∑ b ∈ Ioc 0 N.sqrt, N / b :=
        congrArg _ (sum_congr rfl fun b hb ↦ Nat.sub_add_cancel (hge b hb))
    _ = 2 * ∑ a ∈ Ioc 0 N.sqrt, N / a := (two_mul _).symm

end TauCeti
