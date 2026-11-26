/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.Periodic

import Mathlib.Data.Nat.Periodic
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Products and sums of periodic families over ranges and intervals

A product of an `l`-periodic family `f : ℕ → M` over `range (n₁ * l + n₀)` is the `n₁`-th power
of the product over one period times the product over `range n₀`. For instance, the generating
polynomials `∏_{j < n} (1 + q^(2j) X)` of the quantum binomial coefficients factor this way when
`q²` is a root of unity of order `l`, which proves the quantum Lucas theorem.

Sequences arising from arithmetic functions regrouped by norm or extended by identity at `0`
satisfy `a (k + N) = a k` only for `1 ≤ k`, since `a 0` need not agree with `a N`. Because only
indices `j ≥ 1` enter `Icc (m + 1) (m + N)` and `Icc 1 n`, shifting `j ↦ 1 + i` reduces products
and sums over positive intervals to genuinely `N`-periodic families on `ℕ`. When the period
product `∏ j ∈ Icc 1 N, a j` is `1` (additively, when `∑ j ∈ Icc 1 N, a j = 0`), the partial
products `m ↦ ∏ j ∈ Icc 1 m, a j` are `N`-periodic on all of `ℕ` and depend only on `m % N`.

For an endomorphism `τ` of a commutative monoid (or additive monoid), the product (or sum) over a
full period `range p` of a `τ`-orbit `a (i + 1) = τ (a i)` with `a p = a 0` is fixed by `τ`; in
particular, norms `∏ i ∈ range p, τ^[i] x` of periodic points and ring-endomorphism orbit products
`∏ i ∈ range p, (σ ^ i) x` (for `σ ^ p = 1`) are fixed by the endomorphism.

## Main results

* `Finset.prod_range_mul_add_of_periodic`, `Finset.sum_range_mul_add_of_periodic`: a product or
  sum of an `l`-periodic family over `range (n₁ * l + n₀)` in terms of one period and a remainder.
* `Finset.prod_Ico_add_of_periodic`, `Finset.sum_Ico_add_of_periodic`: a product or sum of an
  `l`-periodic family over `Ico m (m + l)` equals that over `range l`.
* `Finset.prod_Icc_shift_eq_of_periodic`, `Finset.sum_Icc_shift_eq_of_periodic`: if
  `a (k + N) = a k` for all `1 ≤ k`, every block `Icc (m + 1) (m + N)` has the same product or sum
  as `Icc 1 N`.
* `Finset.prod_Icc_add_right_of_periodic`, `Finset.sum_Icc_add_right_of_periodic` and
  `Finset.prod_Icc_mul_eq_pow_of_periodic`, `Finset.sum_Icc_mul_eq_nsmul_of_periodic`: extending
  `Icc 1 m` by one period or taking `m` full periods `Icc 1 (m * N)`.
* `Finset.periodic_prod_Icc_of_prod_eq_one`, `Finset.periodic_sum_Icc_of_sum_eq_zero` and
  `Finset.prod_Icc_eq_prod_Icc_mod_of_prod_eq_one`,
  `Finset.sum_Icc_eq_sum_Icc_mod_of_sum_eq_zero`: when the period product is `1` (or period sum is
  `0`), `m ↦ ∏ j ∈ Icc 1 m, a j` is `N`-periodic on all of `ℕ` and agrees with its value at
  `m % N`.
* `Finset.map_prod_range_eq_self_of_periodic`, `Finset.map_sum_range_eq_self_of_periodic`,
  `Finset.isFixedPt_prod_range_iterate_of_isPeriodicPt`,
  `Finset.isFixedPt_sum_range_iterate_of_isPeriodicPt`, and
  `Finset.isFixedPt_prod_range_pow_apply`: an endomorphism fixes the product or sum over `range p`
  of any `p`-periodic orbit.
-/

public section

namespace Finset

section CommMonoid

variable {M : Type*} [CommMonoid M]

/-- A product over `range (n₁ * l + n₀)` of an `l`-periodic family is the `n₁`-th power of the
product over one period times the product over `range n₀`. -/
@[to_additive sum_range_mul_add_of_periodic
  /-- A sum over `range (n₁ * l + n₀)` of an `l`-periodic family is `n₁` times the sum over one
  period plus the sum over `range n₀`. -/]
theorem prod_range_mul_add_of_periodic {f : ℕ → M} {l : ℕ}
    (hf : Function.Periodic f l) (n₁ n₀ : ℕ) :
    ∏ j ∈ range (n₁ * l + n₀), f j = (∏ j ∈ range l, f j) ^ n₁ * ∏ j ∈ range n₀, f j := by
  have h (j i : ℕ) : f (l * j + i) = f i := by simpa [mul_comm l, add_comm] using hf.nat_mul j i
  rw [prod_range_add, mul_comm n₁, prod_range_mul_eq_prod_prod]
  simp only [h, prod_const, card_range]

/-- A product over `Ico m (m + l)` of an `l`-periodic family equals its product over `range l`. -/
@[to_additive
  /-- A sum over `Ico m (m + l)` of an `l`-periodic family equals its sum over `range l`. -/]
theorem prod_Ico_add_of_periodic {f : ℕ → M} {l : ℕ} (hf : Function.Periodic f l) (m : ℕ) :
    ∏ j ∈ Ico m (m + l), f j = ∏ j ∈ range l, f j := by
  rw [← Nat.image_Ico_mod m l, prod_image (Nat.mod_injOn_Ico m l)]
  exact prod_congr rfl fun j _ ↦ (hf.map_mod_nat j).symm

section PositivePeriodic

variable {a : ℕ → M} {N : ℕ}

/-- **Periodicity of block products.** If `a (k + N) = a k` for every `k ≥ 1`, every block of `N`
consecutive positive indices has the same product as `Icc 1 N`. -/
@[to_additive
  /-- **Periodicity of block sums.** If `a (k + N) = a k` for every `k ≥ 1`, every block of `N`
  consecutive positive indices has the same sum as `Icc 1 N`. -/]
theorem prod_Icc_shift_eq_of_periodic (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (m : ℕ) :
    ∏ j ∈ Icc (m + 1) (m + N), a j = ∏ j ∈ Icc 1 N, a j := by
  let b : ℕ → M := fun i ↦ a (1 + i)
  have hb : Function.Periodic b N := fun i ↦ by
    simpa [b, add_assoc] using hper (1 + i) (Nat.le_add_right 1 i)
  have hlhs : ∏ j ∈ Icc (m + 1) (m + N), a j = ∏ i ∈ Ico m (m + N), b i := by
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range, prod_Ico_eq_prod_range]
    simp [b, add_assoc, add_left_comm, add_comm]
  have hrhs : ∏ j ∈ Icc 1 N, a j = ∏ i ∈ range N, b i := by
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
    simp [b]
  rw [hlhs, hrhs, prod_Ico_add_of_periodic hb m]

/-- Extending `Icc 1 m` by one period `N` multiplies by `∏ j ∈ Icc 1 N, a j`. -/
@[to_additive
  /-- Extending `Icc 1 m` by one period `N` adds `∑ j ∈ Icc 1 N, a j`. -/]
theorem prod_Icc_add_right_of_periodic (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (m : ℕ) :
    ∏ j ∈ Icc 1 (m + N), a j = (∏ j ∈ Icc 1 m, a j) * ∏ j ∈ Icc 1 N, a j := by
  let b : ℕ → M := fun i ↦ a (1 + i)
  have hb : Function.Periodic b N := fun i ↦ by
    simpa [b, add_assoc] using hper (1 + i) (Nat.le_add_right 1 i)
  have hIcc (k : ℕ) : ∏ j ∈ Icc 1 k, a j = ∏ i ∈ range k, b i := by
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
    simp [b]
  rw [hIcc (m + N), hIcc m, hIcc N, show m + N = 1 * N + m by omega,
    prod_range_mul_add_of_periodic hb 1 m, pow_one, mul_comm]

/-- Taking the product over `m` full periods `Icc 1 (m * N)` gives the `m`-th power of the period
product `∏ j ∈ Icc 1 N, a j`. -/
@[to_additive sum_Icc_mul_eq_nsmul_of_periodic
  /-- Summing `m` full periods `Icc 1 (m * N)` gives `m` times the period sum
  `∑ j ∈ Icc 1 N, a j`. -/]
theorem prod_Icc_mul_eq_pow_of_periodic (hper : ∀ k, 1 ≤ k → a (k + N) = a k) (m : ℕ) :
    ∏ j ∈ Icc 1 (m * N), a j = (∏ j ∈ Icc 1 N, a j) ^ m := by
  let b : ℕ → M := fun i ↦ a (1 + i)
  have hb : Function.Periodic b N := fun i ↦ by
    simpa [b, add_assoc] using hper (1 + i) (Nat.le_add_right 1 i)
  have hIcc (k : ℕ) : ∏ j ∈ Icc 1 k, a j = ∏ i ∈ range k, b i := by
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
    simp [b]
  simpa using (hIcc (m * N)).trans
    ((prod_range_mul_add_of_periodic hb m 0).trans (by simp [hIcc N]))

/-- **Partial products of a unit-period sequence are periodic on all of `ℕ`.** Even when
`a (k + N) = a k` holds only for `1 ≤ k`, triviality of the period product `∏ j ∈ Icc 1 N, a j = 1`
makes `m ↦ ∏ j ∈ Icc 1 m, a j` periodic of period `N` for every `m ≥ 0`. -/
@[to_additive
  /-- **Partial sums of a zero-mean periodic sequence are periodic on all of `ℕ`.** Even when
  `a (k + N) = a k` holds only for `1 ≤ k`, vanishing of the period sum `∑ j ∈ Icc 1 N, a j = 0`
  makes `m ↦ ∑ j ∈ Icc 1 m, a j` periodic of period `N` for every `m ≥ 0`. -/]
theorem periodic_prod_Icc_of_prod_eq_one (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hprod : ∏ j ∈ Icc 1 N, a j = 1) :
    Function.Periodic (fun m ↦ ∏ j ∈ Icc 1 m, a j) N := fun m ↦ by
  simp only [prod_Icc_add_right_of_periodic hper m, hprod, mul_one]

/-- If `a` is `N`-periodic on `k ≥ 1` with period product `1`, the partial product up to `m`
depends only on `m % N`. -/
@[to_additive
  /-- If `a` is `N`-periodic on `k ≥ 1` with vanishing period sum, the partial sum up to `m`
  depends only on `m % N`. -/]
theorem prod_Icc_eq_prod_Icc_mod_of_prod_eq_one (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hprod : ∏ j ∈ Icc 1 N, a j = 1) (m : ℕ) :
    ∏ j ∈ Icc 1 m, a j = ∏ j ∈ Icc 1 (m % N), a j :=
  ((periodic_prod_Icc_of_prod_eq_one hper hprod).map_mod_nat m).symm

end PositivePeriodic

/-- If a monoid endomorphism `τ` shifts a periodic sequence `a` by `a (i + 1) = τ (a i)` with
`a p = a 0`, then `τ` fixes the product `∏ i ∈ range p, a i`. -/
@[to_additive
  /-- If an additive monoid endomorphism `τ` shifts a periodic sequence `a` by
  `a (i + 1) = τ (a i)` with `a p = a 0`, then `τ` fixes the sum `∑ i ∈ range p, a i`. -/]
theorem map_prod_range_eq_self_of_periodic {p : ℕ} (τ : M →* M) (a : ℕ → M)
    (h_period : a p = a 0) (h_succ : ∀ i : ℕ, a (i + 1) = τ (a i)) :
    τ (∏ i ∈ range p, a i) = ∏ i ∈ range p, a i := by
  cases p with
  | zero => simp
  | succ p =>
    calc
      τ (∏ i ∈ range (p + 1), a i) = ∏ i ∈ range (p + 1), a (i + 1) := by
        simp only [map_prod, h_succ]
      _ = (∏ i ∈ range p, a (i + 1)) * a (p + 1) := prod_range_succ _ p
      _ = ∏ i ∈ range (p + 1), a i := by rw [h_period, prod_range_succ']

/-- If `x` is `p`-periodic under a monoid endomorphism `τ`, then `τ` fixes the orbit product
`∏ i ∈ range p, τ^[i] x`. -/
@[to_additive
  /-- If `x` is `p`-periodic under an additive monoid endomorphism `τ`, then `τ` fixes the orbit
  sum `∑ i ∈ range p, τ^[i] x`. -/]
theorem isFixedPt_prod_range_iterate_of_isPeriodicPt {p : ℕ} {τ : M →* M} {x : M}
    (hx : Function.IsPeriodicPt τ p x) :
    Function.IsFixedPt τ (∏ i ∈ range p, τ^[i] x) :=
  map_prod_range_eq_self_of_periodic τ (fun i ↦ τ^[i] x) hx fun i ↦
    Function.iterate_succ_apply' τ i x

end CommMonoid

/-- If a ring endomorphism `σ` satisfies `σ ^ p = 1`, then `σ` fixes the norm product
`∏ i ∈ range p, (σ ^ i) x` for every `x`. -/
theorem isFixedPt_prod_range_pow_apply {R : Type*} [CommSemiring R] {σ : R →+* R} {p : ℕ}
    (hσ : σ ^ p = 1) (x : R) :
    Function.IsFixedPt σ (∏ i ∈ range p, (σ ^ i) x) :=
  map_prod_range_eq_self_of_periodic (σ : R →* R) (fun i ↦ (σ ^ i) x)
    (by rw [hσ, pow_zero]) fun i ↦ by simp [pow_succ']

end Finset
