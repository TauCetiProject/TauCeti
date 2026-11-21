/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Multiplication
import Mathlib.Tactic.Ring

/-!
# Multiplication of Laurent series

A coefficient of a product is a finite convolution over the interval determined by lower
order bounds on its factors. This form of the coefficient formula is useful when the bounds
are specified in advance, rather than extracted from the supports.

Over a semiring without zero divisors, the order of a power of a nonzero Laurent
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

/-- If `x` vanishes below `M` and `y` vanishes below `N`, then `x * y` vanishes below `M + N`. -/
theorem coeff_mul_eq_zero_of_lt {R : Type*} [NonUnitalNonAssocSemiring R] {x y : R⸨X⸩}
    {M N r : ℤ} (hx : ∀ i < M, x.coeff i = 0) (hy : ∀ i < N, y.coeff i = 0) (hr : r < M + N) :
    (x * y).coeff r = 0 := by
  classical
  rw [coeff_mul_eq_sum
      (HahnSeries.le_orderTop_iff_forall.mpr fun i hi ↦ hx i (by exact_mod_cast hi))
      (HahnSeries.le_orderTop_iff_forall.mpr fun i hi ↦ hy i (by exact_mod_cast hi))]
  exact Finset.sum_eq_zero fun _ h ↦ by simp only [Finset.mem_Icc] at h; omega

end LaurentSeries

namespace PowerSeries

open scoped PowerSeries

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

namespace TauCeti

open _root_.HahnSeries

variable {k : Type*} [Semiring k] [NoZeroDivisors k] {n : ℕ}

/-- The order of a power of a nonzero Laurent series is the corresponding multiple of its
integer order. -/
theorem laurentSeries_orderTop_pow_of_ne_zero (n : ℕ) {w : k⸨X⸩} (hw : w ≠ 0) :
    (w ^ n).orderTop = ((n : ℤ) * w.order : ℤ) := by
  have : Nontrivial k := by
    rw [← not_subsingleton_iff_nontrivial]
    exact fun _ ↦ hw (Subsingleton.elim _ _)
  rw [hahnSeries_orderTop_pow, ← order_eq_orderTop_of_ne_zero hw,
    ← WithTop.coe_nsmul, nsmul_eq_mul]

/-- Raising a Laurent series of negative order to a power greater than one strictly lowers
its order. -/
theorem laurentSeries_orderTop_pow_lt_orderTop_of_order_neg
    (hn : 1 < n) {w : k⸨X⸩} (hw : w.order < 0) :
    (w ^ n).orderTop < w.orderTop := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [laurentSeries_orderTop_pow_of_ne_zero n hw0, ← order_eq_orderTop_of_ne_zero hw0]
  exact_mod_cast (by nlinarith : (n : ℤ) * w.order < w.order)

end TauCeti
