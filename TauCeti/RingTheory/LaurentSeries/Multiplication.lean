/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Multiplication

/-!
# Multiplication of Laurent series

A coefficient of a product is a finite convolution over the interval determined by lower
order bounds on its factors. This form of the coefficient formula is useful when the bounds
are specified in advance, rather than extracted from the supports.

Over a nontrivial semiring without zero divisors, the order of a power of a nonzero Laurent
series is the exponent times its integer order. In particular, a power greater than one
strictly lowers a negative order.
These formulas compare poles of a Laurent series and its powers.
-/

public section

open scoped LaurentSeries

namespace LaurentSeries

/-- A coefficient of a Laurent-series product is the convolution over any interval containing
all potentially nonzero terms, as determined by lower order bounds on the two factors. -/
theorem coeff_mul_eq_sum {R : Type*} [NonUnitalNonAssocSemiring R] {f g : R⸨X⸩}
    {M N : ℤ} (hf : (M : WithTop ℤ) ≤ f.orderTop) (hg : (N : WithTop ℤ) ≤ g.orderTop)
    (n : ℤ) :
    (f * g).coeff n = ∑ i ∈ Finset.Icc M (n - N), f.coeff i * g.coeff (n - i) := by
  classical
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_bij_ne_zero (fun ij _ _ ↦ ij.1) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hij _
    obtain ⟨hi, hj, hij⟩ := Finset.mem_antidiagonal.mp hij
    exact Finset.mem_Icc.mpr ⟨not_lt.mp fun h ↦
      hi (HahnSeries.le_orderTop_iff_forall.mp hf i (by exact_mod_cast h)),
      by
        have : N ≤ j := not_lt.mp fun h ↦
          hj (HahnSeries.le_orderTop_iff_forall.mp hg j (by exact_mod_cast h))
        omega⟩
  · rintro ⟨i, j⟩ hij _ ⟨i', j'⟩ hij' _ h
    rw [Finset.mem_antidiagonal] at hij hij'
    simp only at h
    ext <;> simp only <;> omega
  · intro i _ hi
    refine ⟨(i, n - i), Finset.mem_antidiagonal.mpr ⟨?_, ?_, by omega⟩, hi, rfl⟩
    · intro h
      exact hi (by simp [h])
    · intro h
      exact hi (by simp [h])
  · rintro ⟨i, j⟩ hij _
    obtain ⟨_, _, hij⟩ := Finset.mem_antidiagonal.mp hij
    have hj : n - i = j := by omega
    simp [hj]

end LaurentSeries

namespace TauCeti

open _root_.HahnSeries

variable {k : Type*} [Semiring k] [NoZeroDivisors k] [Nontrivial k] {n : ℕ}

/-- The order of a power of a nonzero Laurent series is the corresponding multiple of its
integer order. -/
theorem laurentSeries_orderTop_pow_of_ne_zero (n : ℕ) {w : k⸨X⸩} (hw : w ≠ 0) :
    (w ^ n).orderTop = ((n : ℤ) * w.order : ℤ) := by
  rw [hahnSeries_orderTop_pow, ← order_eq_orderTop_of_ne_zero hw,
    ← WithTop.coe_nsmul, nsmul_eq_mul]

/-- Raising a Laurent series of negative order to a power greater than one strictly lowers
its order. -/
theorem laurentSeries_orderTop_pow_lt_orderTop_of_order_neg
    (hn : 1 < n) {w : k⸨X⸩} (hw : w.order < 0) :
    (w ^ n).orderTop < w.orderTop := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hnZ : (1 : ℤ) < n := by exact_mod_cast hn
  rw [laurentSeries_orderTop_pow_of_ne_zero n hw0, ← order_eq_orderTop_of_ne_zero hw0]
  exact_mod_cast (by nlinarith : (n : ℤ) * w.order < w.order)

end TauCeti
