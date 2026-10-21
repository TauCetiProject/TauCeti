/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Multiplication

/-!
# Orders and leading coefficients of power-sub-self Laurent series

If `a` is not an `n`-th power in `k` and `n > 1`, the pole `a T⁻ⁿ` cannot be improved by
subtracting `wⁿ - w` in `k((T))`. Every such representative still has a negative order divisible
by `n`. In characteristic `p`, with `n = p`, this shows why a general theorem guaranteeing
reduced Artin–Schreier representatives for all classes needs a perfect-residue-field
hypothesis: over an imperfect residue field, neither an integral representative nor a
prime-to-`p` pole need exist.

The argument uses the leading coefficient, and does not require a characteristic hypothesis.
It complements the perfect-residue-field reduction in Stichtenoth, *Algebraic Function Fields
and Codes*, second edition, Proposition 3.7.8.
-/

public section

open scoped LaurentSeries

namespace TauCeti

open _root_.HahnSeries

variable {k : Type*} [Ring k] [IsDomain k] {n : ℕ} {a : k}

/-- At a negative order, the power term determines the order of `wⁿ - w` when `n > 1`. -/
theorem laurentSeries_orderTop_pow_sub_self_of_order_neg
    (hn : 1 < n) {w : k⸨X⸩} (hw : w.order < 0) :
    (w ^ n - w).orderTop = ((n : ℤ) * w.order : ℤ) := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [orderTop_sub (laurentSeries_orderTop_pow_lt_orderTop_of_order_neg hn hw),
    laurentSeries_orderTop_pow_of_ne_zero n hw0]

/-- At a negative order, the leading coefficient of `wⁿ - w` is that of `w`, raised to `n`. -/
theorem laurentSeries_leadingCoeff_pow_sub_self_of_order_neg
    (hn : 1 < n) {w : k⸨X⸩} (hw : w.order < 0) :
    (w ^ n - w).leadingCoeff = w.leadingCoeff ^ n := by
  rw [leadingCoeff_sub (laurentSeries_orderTop_pow_lt_orderTop_of_order_neg hn hw),
    hahnSeries_leadingCoeff_pow]

/-- If the coefficient of `a T⁻ⁿ` is not an `n`-th power, subtracting `wⁿ - w` never
cancels its pole. A pole of `w` of order greater than one only makes the pole worse. -/
theorem orderTop_single_sub_pow_sub_self
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
  have hpow := laurentSeries_orderTop_pow_of_ne_zero n hw
  by_cases hneg : w.order < 0
  · have hv := laurentSeries_orderTop_pow_sub_self_of_order_neg hn hneg
    split_ifs with hlow
    · -- A substitution pole of order greater than one dominates the original pole.
      have hlow' : (n : ℤ) * w.order < -(n : ℤ) := by nlinarith
      rw [← neg_sub (w ^ n - w), orderTop_neg, orderTop_sub (by
        rw [hv, hu]; exact_mod_cast hlow'), hv]
    · -- At order minus one, the non-power coefficient prevents cancellation.
      have hw1 : w.order = -1 := by omega
      have hv' : (w ^ n - w).orderTop = (-(n : ℤ) : ℤ) := by
        simpa [hw1] using hv
      have hlead := laurentSeries_leadingCoeff_pow_sub_self_of_order_neg hn hneg
      have hcoeff : (single (-(n : ℤ)) a - (w ^ n - w)).coeff (-(n : ℤ)) ≠ 0 := by
        have hcoeff_lead : (w ^ n - w).coeff (-(n : ℤ)) =
            (w ^ n - w).leadingCoeff := by
          simpa only [hv', WithTop.untop_coe] using
            (coeff_untop_eq_leadingCoeff (x := w ^ n - w)
              (by rw [hv']; exact WithTop.coe_ne_top))
        rw [coeff_sub, coeff_single_same, hcoeff_lead, hlead]
        exact sub_ne_zero.mpr (ha w.leadingCoeff).symm
      apply le_antisymm
      · exact orderTop_le_of_coeff_ne_zero hcoeff
      · simpa [hu, hv'] using (min_orderTop_le_orderTop_sub
          (x := (single (-(n : ℤ)) a : k⸨X⸩)) (y := w ^ n - w))
  · -- An integral substitution cannot affect the original negative-order term.
    have hwpos : 0 ≤ w.order := by omega
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
theorem single_sub_pow_sub_self_ne_zero_and_order_le_and_dvd
    (hn : 1 < n) (ha : ∀ b : k, b ^ n ≠ a) (w : k⸨X⸩) :
    single (-(n : ℤ)) a - (w ^ n - w) ≠ 0 ∧
      (single (-(n : ℤ)) a - (w ^ n - w)).order ≤ -(n : ℤ) ∧
      (n : ℤ) ∣ (single (-(n : ℤ)) a - (w ^ n - w)).order := by
  have ht := orderTop_single_sub_pow_sub_self hn ha w
  have hne := ne_zero_of_coeff_ne_zero (coeff_orderTop_ne ht)
  have ho := WithTop.coe_injective ((order_eq_orderTop_of_ne_zero hne).trans ht)
  refine ⟨hne, ?_, ?_⟩
  · rw [ho]
    split_ifs <;> nlinarith
  · rw [ho]
    split_ifs
    · exact dvd_mul_right _ _
    · exact dvd_neg.mpr (dvd_refl _)

/-- If `a` is not an `n`-th power, no translate of `a T⁻ⁿ` by `wⁿ - w` is integral or has
negative order not divisible by `n`. The integral alternative explicitly includes zero. -/
theorem not_exists_reduced_representative_single_sub_pow_sub_self
    (hn : 1 < n) (ha : ∀ b : k, b ^ n ≠ a) :
    ¬ ∃ w : k⸨X⸩,
      0 ≤ (single (-(n : ℤ)) a - (w ^ n - w)).orderTop ∨
        ((single (-(n : ℤ)) a - (w ^ n - w)).order < 0 ∧
          ¬ (n : ℤ) ∣ (single (-(n : ℤ)) a - (w ^ n - w)).order) := by
  rintro ⟨w, hreg | hpole⟩
  · obtain ⟨hne, hle, -⟩ := single_sub_pow_sub_self_ne_zero_and_order_le_and_dvd hn ha w
    rw [← order_eq_orderTop_of_ne_zero hne, WithTop.coe_nonneg] at hreg
    have hnZ : (0 : ℤ) < n := by omega
    omega
  · exact hpole.2 (single_sub_pow_sub_self_ne_zero_and_order_le_and_dvd hn ha w).2.2

end TauCeti
