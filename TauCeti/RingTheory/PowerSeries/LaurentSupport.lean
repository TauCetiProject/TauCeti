/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Ring

/-!
# Laurent-coefficient support bounds in `(R⸨X⸩)⟦X⟧`

This file records slope-`m` and uniform lower support bounds on the inner Laurent coefficients of
power series in `(R⸨X⸩)⟦X⟧` under multiplication and powers, for use in the integrality proof of
the plethystic exponential (`PowerSeries.exists_map_eq_plethysticExp`):

* **Slope-`m` lower vanishing**: vanishing below `q`-degree `a * m` in `t`-degree `a` is
  satisfied by `1` and preserved under multiplication and powers.
* **Uniform lower vanishing under positive powers**: for `0 ≤ N`, vanishing of all positive
  `t`-coefficients below `q`-degree `N` when `constantCoeff = 0` is preserved under all positive
  powers (`PowerSeries.coeff_coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero`).
* **Product comparison**: if `G₁` satisfies the slope-`m` lower bound (`m ≤ 0`) and `G₂` has
  constant term `1` with positive `t`-coefficients vanishing below `q`-degree `N`, then
  `[q ^ r t ^ k] (G₁ * G₂) = [q ^ r t ^ k] G₁` whenever `r < k * m + N`
  (`PowerSeries.coeff_coeff_mul_eq_left_of_lt_mul`).

## Main results

* `PowerSeries.coeff_coeff_one_eq_zero_of_lt_mul`: `[q ^ s t ^ a] 1 = 0` for `s < a * m`.
* `PowerSeries.coeff_coeff_mul_eq_zero_of_lt_mul`: slope-`m` lower vanishing is preserved by
  multiplication.
* `PowerSeries.coeff_coeff_pow_eq_zero_of_lt_mul`: slope-`m` lower vanishing is preserved by
  powers.
* `PowerSeries.coeff_coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero`: uniform lower vanishing
  below `q`-degree `N` (`0 ≤ N`) on positive `t`-coefficients, when `constantCoeff = 0`, is
  preserved by positive powers.
* `PowerSeries.coeff_coeff_mul_eq_left_of_lt_mul`: multiplying a slope-`m` bounded series `G₁` by a
  series `G₂` with constant term `1` and positive `t`-coefficients vanishing below `N`
  preserves `[q ^ r t ^ k] G₁` whenever `r < k * m + N` and `m ≤ 0`.
-/

public section

namespace PowerSeries

open scoped LaurentSeries PowerSeries

/-- Every `a`-th `t`-coefficient of `1 : (R⸨X⸩)⟦X⟧` vanishes below `q`-degree `a * m`. -/
theorem coeff_coeff_one_eq_zero_of_lt_mul {R : Type*} [Semiring R] {m : ℤ} :
    ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (1 : (R⸨X⸩)⟦X⟧)).coeff s = 0 := by
  rintro (_ | a) s hs
  · simp [HahnSeries.coeff_one, ne_of_lt (by simpa using hs)]
  · simp

/-- If every `a`-th `t`-coefficient of `G₁` and `G₂` vanishes below `q`-degree `a * m`, then the
same holds for `G₁ * G₂`. -/
theorem coeff_coeff_mul_eq_zero_of_lt_mul {R : Type*} [Semiring R] {m : ℤ} {G₁ G₂ : (R⸨X⸩)⟦X⟧}
    (h₁ : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G₁).coeff s = 0)
    (h₂ : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G₂).coeff s = 0) :
    ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (G₁ * G₂)).coeff s = 0 := by
  intro a s hs
  rw [coeff_mul, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun x hx ↦ ?_
  have hab : (x.1 : ℤ) * m + (x.2 : ℤ) * m = (a : ℤ) * m := by
    have : x.1 + x.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    push_cast [← this]; ring
  exact HahnSeries.le_orderTop_iff_forall.mp
    ((add_le_add
      (HahnSeries.le_orderTop_iff_forall.mpr fun _ hi ↦ h₁ x.1 _ (WithTop.coe_lt_coe.mp hi))
      (HahnSeries.le_orderTop_iff_forall.mpr fun _ hi ↦ h₂ x.2 _ (WithTop.coe_lt_coe.mp hi))).trans
      HahnSeries.orderTop_add_le_mul)
    s (by rw [← WithTop.coe_add, WithTop.coe_lt_coe, hab]; exact hs)

/-- If every `a`-th `t`-coefficient of `G` vanishes below `q`-degree `a * m`, then the same holds
for `G ^ n`. -/
theorem coeff_coeff_pow_eq_zero_of_lt_mul {R : Type*} [Semiring R] {m : ℤ} {G : (R⸨X⸩)⟦X⟧}
    (hG : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G).coeff s = 0) (n : ℕ) :
    ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (G ^ n)).coeff s = 0 := by
  induction n with
  | zero => simpa using coeff_coeff_one_eq_zero_of_lt_mul (R := R) (m := m)
  | succ n ih => rw [pow_succ]; exact coeff_coeff_mul_eq_zero_of_lt_mul ih hG

/-- If `G : (R⸨X⸩)⟦X⟧` has zero `t`-constant coefficient and every positive `t`-coefficient
vanishes below `q`-degree `N ≥ 0`, then every positive `t`-coefficient of `G ^ d` (`1 ≤ d`)
vanishes below `q`-degree `N`. -/
theorem coeff_coeff_pow_eq_zero_of_lt_of_constantCoeff_eq_zero {R : Type*} [Semiring R]
    {G : (R⸨X⸩)⟦X⟧} {N : ℤ} (hN : 0 ≤ N) (hG0 : constantCoeff G = 0)
    (hG : ∀ a, 1 ≤ a → ∀ s < N, (coeff a G).coeff s = 0) :
    ∀ d, 1 ≤ d → ∀ a, 1 ≤ a → ∀ s < N, (coeff a (G ^ d)).coeff s = 0 := by
  intro d hd
  induction d with
  | zero => omega
  | succ d ih =>
    rcases d with _ | d
    · simpa using hG
    · intro a _ s hs
      rw [pow_succ, coeff_mul, HahnSeries.coeff_sum]
      refine Finset.sum_eq_zero fun x _ ↦ ?_
      rcases eq_or_ne x.1 0 with h1 | h1
      · rw [h1, coeff_zero_eq_constantCoeff_apply, map_pow, hG0,
          zero_pow (Nat.succ_ne_zero d), zero_mul, HahnSeries.coeff_zero]
      · rcases eq_or_ne x.2 0 with h2 | h2
        · rw [h2, coeff_zero_eq_constantCoeff_apply, hG0, mul_zero, HahnSeries.coeff_zero]
        · exact HahnSeries.le_orderTop_iff_forall.mp
            ((add_le_add
              (HahnSeries.le_orderTop_iff_forall.mpr fun _ hi ↦
                ih (Nat.succ_pos d) x.1 (Nat.pos_of_ne_zero h1) _ (WithTop.coe_lt_coe.mp hi))
              (HahnSeries.le_orderTop_iff_forall.mpr fun _ hi ↦
                hG x.2 (Nat.pos_of_ne_zero h2) _ (WithTop.coe_lt_coe.mp hi))).trans
              HahnSeries.orderTop_add_le_mul)
            s (by rw [← WithTop.coe_add, WithTop.coe_lt_coe]; omega)

/-- Multiplying a slope-`m` bounded series `G₁` by a series `G₂` with constant term `1` and
positive `t`-coefficients vanishing below `N` preserves `[q ^ r t ^ k]` whenever
`r < k * m + N` and `m ≤ 0`. -/
theorem coeff_coeff_mul_eq_left_of_lt_mul {R : Type*} [Semiring R] {G₁ G₂ : (R⸨X⸩)⟦X⟧}
    {k : ℕ} {m N r : ℤ} (hm : m ≤ 0) (hr : r < (k : ℤ) * m + N)
    (h₁ : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G₁).coeff s = 0)
    (h₂0 : constantCoeff G₂ = 1)
    (h₂ : ∀ a, 1 ≤ a → ∀ s < N, (coeff a G₂).coeff s = 0) :
    (coeff k (G₁ * G₂)).coeff r = (coeff k G₁).coeff r := by
  classical
  rw [coeff_mul, HahnSeries.coeff_sum,
    Finset.sum_eq_single_of_mem (k, 0) (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero k))]
  · rw [coeff_zero_eq_constantCoeff_apply, h₂0, mul_one]
  · intro x hx hne
    have hsum := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    have hx2 : 1 ≤ x.2 := Nat.pos_of_ne_zero fun h0 ↦ hne (Prod.ext (by omega) h0)
    have hxm : (k : ℤ) * m ≤ (x.1 : ℤ) * m :=
      mul_le_mul_of_nonpos_right (by exact_mod_cast (by omega : x.1 ≤ k)) hm
    exact HahnSeries.le_orderTop_iff_forall.mp
      ((add_le_add
        (HahnSeries.le_orderTop_iff_forall.mpr fun _ hi ↦
          h₁ x.1 _ (WithTop.coe_lt_coe.mp hi))
        (HahnSeries.le_orderTop_iff_forall.mpr fun _ hi ↦
          h₂ x.2 hx2 _ (WithTop.coe_lt_coe.mp hi))).trans
        HahnSeries.orderTop_add_le_mul)
      r (by rw [← WithTop.coe_add, WithTop.coe_lt_coe]; omega)

end PowerSeries
