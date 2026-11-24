/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Weighted hyperbola sums of Dirichlet convolutions

Mathlib's `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum` rewrites `∑_{0<n≤N} (f * g)(n)` as a sum
over the hyperbola `mℓ ≤ N`. This file adds the weighted form, where each term carries a weight
`w(n)` with values in a module; the weight stays attached to the product `mℓ`, so it need not be
multiplicative (for instance `w(n) = e(nα)`). The proof follows the plan of Mathlib's
`ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`, through
`Nat.divisorsAntidiagonal_eq_prod_filter_of_le`.

## Main results

* `ArithmeticFunction.sum_Ioc_mul_smul_eq_sum_sum`:
  `∑_{0<n≤N} (f * g)(n) • w(n) = ∑_{0<m≤N} f(m) • ∑_{0<ℓ≤N/m} g(ℓ) • w(mℓ)`.
-/

public section

open Finset

namespace ArithmeticFunction

variable {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]

/-- Summing a Dirichlet convolution `f * g` against an arbitrary weight `w` over `0 < n ≤ N` is
the sum of `f(m) g(ℓ) w(mℓ)` over the hyperbola `mℓ ≤ N`. The weight stays attached to the
product `mℓ`; it need not be multiplicative. -/
theorem sum_Ioc_mul_smul_eq_sum_sum (f g : ArithmeticFunction R) (w : ℕ → A) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (f * g) n • w n =
      ∑ m ∈ Ioc 0 N, f m • ∑ ℓ ∈ Ioc 0 (N / m), g ℓ • w (m * ℓ) := by
  calc ∑ n ∈ Ioc 0 N, (f * g) n • w n
      = ∑ n ∈ Ioc 0 N, ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 = n,
          (f x.1 * g x.2) • w (x.1 * x.2) := by
        refine sum_congr rfl fun n hn ↦ ?_
        rw [mem_Ioc] at hn
        rw [ArithmeticFunction.mul_apply, sum_smul,
          Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
        exact sum_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2]
    _ = ∑ x ∈ Ioc 0 N ×ˢ Ioc 0 N with x.1 * x.2 ∈ Ioc 0 N, (f x.1 * g x.2) • w (x.1 * x.2) :=
        sum_fiberwise_eq_sum_filter _ _ _ _
    _ = ∑ m ∈ Ioc 0 N, ∑ ℓ ∈ Ioc 0 N with m * ℓ ≤ N, (f m * g ℓ) • w (m * ℓ) := by
        rw [sum_filter, sum_product]
        refine sum_congr rfl fun m hm ↦ ?_
        rw [sum_filter]
        refine sum_congr rfl fun ℓ hℓ ↦ ?_
        simp only [mem_Ioc] at hm hℓ
        have : 0 < m * ℓ := Nat.mul_pos hm.1 hℓ.1
        simp [this]
    _ = ∑ m ∈ Ioc 0 N, f m • ∑ ℓ ∈ Ioc 0 (N / m), g ℓ • w (m * ℓ) := by
        refine sum_congr rfl fun m hm ↦ ?_
        rw [smul_sum]
        have hm : 0 < m := (mem_Ioc.1 hm).1
        have : {ℓ ∈ Ioc 0 N | m * ℓ ≤ N} = Ioc 0 (N / m) := by
          ext ℓ
          simp only [mem_filter, mem_Ioc, Nat.le_div_iff_mul_le hm, mul_comm ℓ m]
          constructor
          · exact fun h ↦ ⟨h.1.1, h.2⟩
          · exact fun h ↦ ⟨⟨h.1, h.2.trans' (Nat.le_mul_of_pos_left ℓ hm)⟩, h.2⟩
        rw [this]
        exact sum_congr rfl fun ℓ _ ↦ (smul_smul _ _ _).symm

end ArithmeticFunction
