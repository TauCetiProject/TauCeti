/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.Ring
import TauCeti.RingTheory.LaurentSeries.Multiplication

/-!
# Laurent-coefficient support bounds in `(R⸨X⸩)⟦X⟧`

This file records slope-`m` and uniform lower support bounds on the inner Laurent coefficients of
power series in `(R⸨X⸩)⟦X⟧` under multiplication and powers.

## Main results

* `PowerSeries.coeff_coeff_one_eq_zero_of_lt_mul`: `[q ^ s t ^ a] 1 = 0` for `s < a * m`.
* `PowerSeries.coeff_coeff_mul_eq_zero_of_lt_mul`: slope-`m` lower vanishing is preserved by
  multiplication.
* `PowerSeries.coeff_coeff_pow_eq_zero_of_lt_mul`: slope-`m` lower vanishing is preserved by
  powers.
* `PowerSeries.coeff_coeff_mul_eq_left_of_lt_mul`: multiplying a slope-`m` bounded series `G₁` by a
  series `G₂` with constant term `1` and positive `t`-coefficients vanishing below `q`-degree `N`
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
  exact LaurentSeries.coeff_mul_eq_zero_of_lt (h₁ x.1) (h₂ x.2) (hab ▸ hs)

/-- If every `a`-th `t`-coefficient of `G` vanishes below `q`-degree `a * m`, then the same holds
for `G ^ n`. -/
theorem coeff_coeff_pow_eq_zero_of_lt_mul {R : Type*} [Semiring R] {m : ℤ} {G : (R⸨X⸩)⟦X⟧}
    (hG : ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a G).coeff s = 0) (n : ℕ) :
    ∀ a : ℕ, ∀ s < (a : ℤ) * m, (coeff a (G ^ n)).coeff s = 0 := by
  induction n with
  | zero => simpa using coeff_coeff_one_eq_zero_of_lt_mul (R := R) (m := m)
  | succ n ih => rw [pow_succ]; exact coeff_coeff_mul_eq_zero_of_lt_mul ih hG

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
    exact LaurentSeries.coeff_mul_eq_zero_of_lt (h₁ x.1) (h₂ x.2 hx2) (by omega)

end PowerSeries
