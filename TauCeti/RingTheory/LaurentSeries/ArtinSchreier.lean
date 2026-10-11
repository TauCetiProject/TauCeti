/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.HahnSeries.Valuation
public import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# An obstruction to reducing an Artin–Schreier pole

If `a` is not an `n`-th power in `k` and `n > 1`, the pole `a T⁻ⁿ` cannot be improved by
subtracting `wⁿ - w` in `k((T))`. Every such representative still has a negative order divisible
by `n`. In characteristic `p`, with `n = p`, this shows why the existence of a reduced
Artin–Schreier representative requires a perfect residue field: neither an integral
representative nor a prime-to-`p` pole need exist.

The argument uses the leading coefficient, and does not require a characteristic hypothesis.
It complements the perfect-residue-field reduction in Stichtenoth, *Algebraic Function Fields
and Codes*, second edition, Proposition 3.7.8.
-/

public section

open scoped LaurentSeries

namespace TauCeti

open HahnSeries

variable {k : Type*} [Field k] {n : ℕ} {a : k}

/-- If the coefficient of `a T⁻ⁿ` is not an `n`-th power, subtracting `wⁿ - w` never
cancels its pole. A pole of `w` of order greater than one only makes the pole worse. -/
theorem _root_.LaurentSeries.orderTop_single_sub_pow_sub_self
    (hn : 1 < n) (ha : ∀ b : k, b ^ n ≠ a) (w : k⸨X⸩) :
    (single (-(n : ℤ)) a - (w ^ n - w)).orderTop =
      ((if w.order < -1 then (n : ℤ) * w.order else -(n : ℤ)) : ℤ) := by
  have hn0 : n ≠ 0 := by omega
  have hnZ : (1 : ℤ) < n := by exact_mod_cast hn
  have ha0 : a ≠ 0 := by simpa [hn0] using (ha 0).symm
  have hu : (single (-(n : ℤ)) a : k⸨X⸩).orderTop = (-(n : ℤ) : ℤ) :=
    orderTop_single ha0
  rcases eq_or_ne w 0 with rfl | hw
  · simpa [hn0] using hu
  have hwtop : w.orderTop = (w.order : WithTop ℤ) :=
    (order_eq_orderTop_of_ne_zero hw).symm
  have hpow : (w ^ n).orderTop = ((n : ℤ) * w.order : ℤ) := by
    rw [← addVal_apply, AddValuation.map_pow, addVal_apply, hwtop,
      ← WithTop.coe_nsmul, nsmul_eq_mul]
  by_cases hneg : w.order < 0
  · have hlt : (n : ℤ) * w.order < w.order := by nlinarith
    have hv : (w ^ n - w).orderTop = ((n : ℤ) * w.order : ℤ) := by
      rw [orderTop_sub (by rw [hpow, hwtop]; exact_mod_cast hlt), hpow]
    split_ifs with hlow
    · have hlow' : (n : ℤ) * w.order < -(n : ℤ) := by nlinarith
      rw [← neg_sub (w ^ n - w), orderTop_neg, orderTop_sub (by
        rw [hv, hu]; exact_mod_cast hlow'), hv]
    · have hw1 : w.order = -1 := by omega
      have hv' : (w ^ n - w).orderTop = (-(n : ℤ) : ℤ) := by
        simpa [hw1] using hv
      have hlead : (w ^ n - w).leadingCoeff = w.leadingCoeff ^ n := by
        rw [leadingCoeff_sub (by rw [hpow, hwtop]; exact_mod_cast hlt), leadingCoeff_pow]
      have hcoeff : (single (-(n : ℤ)) a - (w ^ n - w)).coeff (-(n : ℤ)) ≠ 0 := by
        have hv0 : w ^ n - w ≠ 0 := by
          intro hzero
          rw [hzero, orderTop_zero] at hv'
          exact WithTop.top_ne_coe hv'
        have hvord : (w ^ n - w).order = -(n : ℤ) := by
          exact WithTop.coe_injective ((order_eq_orderTop_of_ne_zero hv0).trans hv')
        rw [coeff_sub, coeff_single_same, ← hvord, ← leadingCoeff_eq, hlead]
        exact sub_ne_zero.mpr (ha w.leadingCoeff).symm
      apply le_antisymm
      · exact orderTop_le_of_coeff_ne_zero hcoeff
      · simpa [hu, hv'] using (min_orderTop_le_orderTop_sub
          (x := (single (-(n : ℤ)) a : k⸨X⸩)) (y := w ^ n - w))
  · have hwpos : 0 ≤ w.order := by omega
    have hmin : (-(n : ℤ) : WithTop ℤ) < min (w ^ n).orderTop w.orderTop := by
      rw [hpow, hwtop, lt_min_iff]
      constructor <;> exact_mod_cast (by nlinarith : -(n : ℤ) < _)
    have hlt : (single (-(n : ℤ)) a : k⸨X⸩).orderTop < (w ^ n - w).orderTop := by
      rw [hu]
      exact hmin.trans_le min_orderTop_le_orderTop_sub
    rw [orderTop_sub hlt, hu]
    simp only [ite_eq_right (by omega : ¬w.order < -1)]

/-- Every translate of `a T⁻ⁿ` by `wⁿ - w` is nonzero, has a pole of order at least `n`,
and its order is divisible by `n`, if `a` is not an `n`-th power. -/
theorem _root_.LaurentSeries.single_sub_pow_sub_self_pole
    (hn : 1 < n) (ha : ∀ b : k, b ^ n ≠ a) (w : k⸨X⸩) :
    single (-(n : ℤ)) a - (w ^ n - w) ≠ 0 ∧
      (single (-(n : ℤ)) a - (w ^ n - w)).order ≤ -(n : ℤ) ∧
      (n : ℤ) ∣ (single (-(n : ℤ)) a - (w ^ n - w)).order := by
  have ht := LaurentSeries.orderTop_single_sub_pow_sub_self hn ha w
  have hne : single (-(n : ℤ)) a - (w ^ n - w) ≠ 0 := by
    intro hz
    simp [hz] at ht
  have ho := WithTop.coe_injective ((order_eq_orderTop_of_ne_zero hne).trans ht)
  refine ⟨hne, ?_, ?_⟩
  · rw [ho]
    split_ifs <;> nlinarith
  · rw [ho]
    split_ifs
    · exact dvd_mul_right _ _
    · exact dvd_neg.mpr (dvd_refl _)

/-- If `a` is not an `n`-th power, no translate of `a T⁻ⁿ` by `wⁿ - w` is regular or has
negative order not divisible by `n`. The regular alternative explicitly includes zero. -/
theorem _root_.LaurentSeries.not_exists_regular_or_pole_not_dvd
    (hn : 1 < n) (ha : ∀ b : k, b ^ n ≠ a) :
    ¬ ∃ w : k⸨X⸩,
      0 ≤ (single (-(n : ℤ)) a - (w ^ n - w)).orderTop ∨
        ((single (-(n : ℤ)) a - (w ^ n - w)).order < 0 ∧
          ¬ (n : ℤ) ∣ (single (-(n : ℤ)) a - (w ^ n - w)).order) := by
  rintro ⟨w, hreg | hpole⟩
  · obtain ⟨hne, hle, -⟩ := LaurentSeries.single_sub_pow_sub_self_pole hn ha w
    rw [← order_eq_orderTop_of_ne_zero hne, WithTop.coe_nonneg] at hreg
    have hnZ : (0 : ℤ) < n := by omega
    omega
  · exact hpole.2 (LaurentSeries.single_sub_pow_sub_self_pole hn ha w).2.2

end TauCeti
