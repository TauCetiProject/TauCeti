/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ExtendToLocalization
public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.NovikovSeries.LeadingTerm
public import TauCeti.RingTheory.NovikovSeries.Topology

/-!
# The period valuation and its extension to fractions

When the group ring has no zero divisors, the least period of a nonzero Novikov
series is additive under multiplication. It therefore defines a valuation, with
values in `WithZero (Multiplicative ℝ)`: a nonzero series of order `c` has value
`ofAdd (-c)`. Zero has value zero, independently of the convention `order 0 = 0`.
No injectivity or discreteness assumption on the period homomorphism is needed;
in particular, finite ties in a period fiber are retained.

`periodValuation_le_iff` identifies its closed balls with the existing period
filtration. `fractionValuation` extends it to any fraction ring, and the formula
`fractionValuation_div` computes its value from numerator and denominator orders.
This gives a splitting-free order on fractions of a domain Novikov ring, for use
in cutoff estimates for inverses and based torsion. It does not assert that the
fraction ring is complete, or put a valuation on a ring with zero divisors.

The extension uses Mathlib's `Valuation.extendToLocalization`.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*,
  Forum Math. 14 (2002), Definition 2.6 and Lemma 2.8.
-/

public section

noncomputable section

open scoped nonZeroDivisors

namespace TauCeti.NovikovSeries

section Ring

variable {R H : Type*} [Ring R] [Nontrivial R] [AddMonoid H]
  [NoZeroDivisors (AddMonoidAlgebra R H)] (N : H →+ ℝ)

/-- The multiplicative period valuation: zero has value zero, and a nonzero
series of least period `c` has value `ofAdd (-c)`. -/
def periodValuation : Valuation (NovikovSeries R H N) (WithZero (Multiplicative ℝ)) := by
  classical
  exact {
    toFun := fun a => if a = 0 then 0 else ↑(Multiplicative.ofAdd (-a.order))
    map_zero' := by simp
    map_one' := by simp [← single_zero_one, order_single one_ne_zero]
    map_mul' a b := by
      by_cases ha : a = 0
      · simp [ha]
      by_cases hb : b = 0
      · simp [hb]
      simp [ha, hb, mul_ne_zero ha hb, order_mul ha hb, ofAdd_add, mul_comm]
    map_add_le_max' a b := by
      by_cases ha : a = 0
      · simp [ha]
      by_cases hb : b = 0
      · simp [hb]
      by_cases hab : a + b = 0
      · simp [hab]
      simp only [ha, hb, hab, ↓reduceIte]
      rcases le_total a.order b.order with h | h
      · apply le_trans _ (le_max_left _ _)
        exact WithZero.coe_le_coe.mpr (neg_le_neg ((min_eq_left h ▸
          min_order_le_order_add hab)))
      · apply le_trans _ (le_max_right _ _)
        exact WithZero.coe_le_coe.mpr (neg_le_neg ((min_eq_right h ▸
          min_order_le_order_add hab))) }

/-- The value of a nonzero series records its least period. -/
theorem periodValuation_apply_of_ne_zero {a : NovikovSeries R H N} (ha : a ≠ 0) :
    periodValuation N a = ↑(Multiplicative.ofAdd (-a.order)) := by
  classical
  simp [periodValuation, ha]

/-- The period valuation has trivial support. -/
@[simp]
theorem periodValuation_eq_zero_iff {a : NovikovSeries R H N} :
    periodValuation N a = 0 ↔ a = 0 := by
  classical
  simp [periodValuation]

/-- The period valuation of a nonzero monomial depends only on its exponent. -/
@[simp]
theorem periodValuation_single (h : H) {r : R} (hr : r ≠ 0) :
    periodValuation N (single h r) = ↑(Multiplicative.ofAdd (-N h)) := by
  rw [periodValuation_apply_of_ne_zero N (single_eq_zero_iff.not.2 hr), order_single hr]

/-- Closed valuation balls are exactly the period-filtration subgroups. -/
theorem periodValuation_le_iff (a : NovikovSeries R H N) (C : ℝ) :
    periodValuation N a ≤ ↑(Multiplicative.ofAdd (-C)) ↔
      a ∈ periodFiltration R N C := by
  by_cases ha : a = 0
  · simp [ha]
  rw [periodValuation_apply_of_ne_zero N ha, WithZero.coe_le_coe,
    mem_periodFiltration_iff_le_order ha]
  exact neg_le_neg_iff (α := ℝ)

/-- An open valuation ball consists of zero and the series of order strictly
larger than the cutoff. -/
theorem periodValuation_lt_iff (a : NovikovSeries R H N) (C : ℝ) :
    periodValuation N a < ↑(Multiplicative.ofAdd (-C)) ↔ a = 0 ∨ C < a.order := by
  by_cases ha : a = 0
  · simp [ha]
  rw [periodValuation_apply_of_ne_zero N ha, WithZero.coe_lt_coe]
  simp [ha]

/-- A perturbation above the least period preserves the period valuation, and
therefore cannot turn a nonzero series into zero. -/
theorem periodValuation_eq_of_sub_mem_periodFiltration {a b : NovikovSeries R H N}
    (ha : a ≠ 0) {C : ℝ} (hC : a.order < C)
    (hab : b - a ∈ periodFiltration R N C) :
    periodValuation N b = periodValuation N a := by
  apply Valuation.map_eq_of_sub_lt
  apply ((periodValuation_le_iff N (b - a) C).2 hab).trans_lt
  rw [periodValuation_apply_of_ne_zero N ha, WithZero.coe_lt_coe]
  exact neg_lt_neg hC

/-- A perturbation above the least period of a nonzero series remains nonzero. -/
theorem ne_zero_of_sub_mem_periodFiltration {a b : NovikovSeries R H N}
    (ha : a ≠ 0) {C : ℝ} (hC : a.order < C)
    (hab : b - a ∈ periodFiltration R N C) : b ≠ 0 := by
  have heq := periodValuation_eq_of_sub_mem_periodFiltration N ha hC hab
  intro hb
  apply ha
  apply (periodValuation_eq_zero_iff N).1
  rw [← heq, hb, map_zero]

end Ring

section Fractions

variable {R H : Type*} [CommRing R] [Nontrivial R] [AddCommMonoid H]
  [NoZeroDivisors (AddMonoidAlgebra R H)] (N : H →+ ℝ)

private theorem nonZeroDivisors_le_primeCompl_periodValuation :
    nonZeroDivisors (NovikovSeries R H N) ≤ (periodValuation N).supp.primeCompl := by
  intro a ha
  exact fun h => (nonZeroDivisors.ne_zero ha) ((periodValuation_eq_zero_iff N).1 h)

variable (R) (F : Type*) [CommRing F] [Algebra (NovikovSeries R H N) F]
  [IsFractionRing (NovikovSeries R H N) F]

/-- The period valuation extended to a fraction ring of the Novikov ring.
It is defined without a choice of period-kernel splitting. -/
def fractionValuation : Valuation F (WithZero (Multiplicative ℝ)) :=
  (periodValuation (R := R) N).extendToLocalization
    (nonZeroDivisors_le_primeCompl_periodValuation (R := R) N) F

/-- Extension to fractions preserves the value of each Novikov series. -/
@[simp]
theorem fractionValuation_algebraMap (a : NovikovSeries R H N) :
    fractionValuation R N F (algebraMap (NovikovSeries R H N) F a) =
      periodValuation N a :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ _

/-- The value of a localized fraction is the numerator value times the inverse
of the denominator value. -/
@[simp]
theorem fractionValuation_mk' (a : NovikovSeries R H N)
    (s : nonZeroDivisors (NovikovSeries R H N)) :
    fractionValuation R N F (IsLocalization.mk' F a s) =
      periodValuation N a * (periodValuation N (s : NovikovSeries R H N))⁻¹ :=
  Valuation.extendToLocalization_mk' _ _ _ _ _

end Fractions

section Field

variable {R H : Type*} [CommRing R] [Nontrivial R] [AddCommMonoid H]
  [NoZeroDivisors (AddMonoidAlgebra R H)] (N : H →+ ℝ)
  (F : Type*) [Field F] [Algebra (NovikovSeries R H N) F]
  [IsFractionRing (NovikovSeries R H N) F]

variable (R)

/-- The value of a fraction of two nonzero series is the difference of their
least periods, with the multiplicative valuation sign convention. -/
theorem fractionValuation_div {a b : NovikovSeries R H N} (ha : a ≠ 0) (hb : b ≠ 0) :
    fractionValuation R N F
        (algebraMap (NovikovSeries R H N) F a / algebraMap (NovikovSeries R H N) F b) =
      ↑(Multiplicative.ofAdd (b.order - a.order)) := by
  rw [map_div₀, fractionValuation_algebraMap, fractionValuation_algebraMap,
    periodValuation_apply_of_ne_zero N ha, periodValuation_apply_of_ne_zero N hb]
  simp [div_eq_mul_inv, ← WithZero.coe_mul, ← WithZero.coe_inv,
    ← ofAdd_add, ← ofAdd_neg, sub_eq_add_neg, add_comm]

/-- Inverting a perturbation above the least period loses twice that period in
the cutoff: if `b - a` vanishes below `C > order a`, then the difference of the
inverses in the fraction field has valuation at most `ofAdd (2 * order a - C)`.
The perturbed denominator is nonzero by `ne_zero_of_sub_mem_periodFiltration`. -/
theorem fractionValuation_inv_sub_inv_le {a b : NovikovSeries R H N} (ha : a ≠ 0)
    {C : ℝ} (hC : a.order < C) (hab : b - a ∈ periodFiltration R N C) :
    fractionValuation R N F
        ((algebraMap (NovikovSeries R H N) F b)⁻¹ -
          (algebraMap (NovikovSeries R H N) F a)⁻¹) ≤
      ↑(Multiplicative.ofAdd (2 * a.order - C)) := by
  have heq := periodValuation_eq_of_sub_mem_periodFiltration N ha hC hab
  have hb := ne_zero_of_sub_mem_periodFiltration N ha hC hab
  have hinj := IsFractionRing.injective (NovikovSeries R H N) F
  rw [inv_sub_inv ((map_ne_zero_iff _ hinj).2 hb)
    ((map_ne_zero_iff _ hinj).2 ha), ← map_sub]
  simp only [map_div₀, map_mul, fractionValuation_algebraMap, heq]
  calc
    periodValuation N (a - b) / (periodValuation N a * periodValuation N a) ≤
        ↑(Multiplicative.ofAdd (-C)) / (periodValuation N a * periodValuation N a) := by
      apply div_le_div_of_nonneg_right ?_ zero_le
      rw [Valuation.map_sub_swap]
      exact (periodValuation_le_iff N (b - a) C).2 hab
    _ = ↑(Multiplicative.ofAdd (2 * a.order - C)) := by
      rw [periodValuation_apply_of_ne_zero N ha]
      simp only [← WithZero.coe_mul, ← WithZero.coe_div, ← ofAdd_add, ← ofAdd_sub]
      congr 2
      ring

end Field

end TauCeti.NovikovSeries
