/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic
public import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Order.SuccPred.Int

/-!
# Coefficients of Laurent substitutions

For a nonzero power series `φ` with zero constant coefficient, put `e = ord φ > 0`.
The coefficient of `Xⁿ` in `f(φ)` is the finite sum

`∑ j ∈ [ord f, n / e], coeff_j(f) * coeff_n(φ ^ j)`.

Here both bounds and the powers are integers, and division is Euclidean division, so the
formula includes poles of `f` and negative `n`. More generally any cutoff `N` with `n < e N`
suffices: terms of `f` at exponents at least `N` cannot affect this coefficient. This gives
finite-truncation dependence without imposing a common lower bound on two input series.
The powers of `φ` in the formula are taken in the Laurent field, not in the power-series ring,
where negative powers of a nonunit would not be defined.
-/

public section

open HahnSeries PowerSeries
open scoped LaurentSeries

namespace TauCeti.LaurentSeries

variable {K : Type*} [Field K] {φ : K⟦X⟧}
  (hφ : constantCoeff φ = 0) (hφ₀ : φ ≠ 0)

/-- Agreement of Laurent coefficients below `N` implies agreement after substitution below
`ord(φ) * N`. No common lower bound on the two input series is required. -/
theorem coeff_substAlgHom_eq_of_coeff_eq {f g : K⸨X⸩} {N n : ℤ}
    (hfg : ∀ j < N, f.coeff j = g.coeff j)
    (hn : n < (φ.order.toNat : ℤ) * N) :
    (substAlgHom hφ hφ₀ f).coeff n = (substAlgHom hφ hφ₀ g).coeff n := by
  have hord : (N : WithTop ℤ) ≤ (f - g).orderTop := by
    rw [le_orderTop_iff_forall]
    intro j hj
    simp only [coeff_sub, sub_eq_zero]
    exact hfg j (WithTop.coe_lt_coe.mp hj)
  have hscaled := nsmul_le_nsmul_right hord φ.order.toNat
  rw [← orderTop_substAlgHom hφ hφ₀] at hscaled
  have hzero : (substAlgHom hφ hφ₀ (f - g)).coeff n = 0 :=
    coeff_eq_zero_of_lt_orderTop <| lt_of_lt_of_le
      (by simpa only [← WithTop.coe_nsmul, nsmul_eq_mul, WithTop.coe_lt_coe] using hn)
      hscaled
  simpa only [map_sub, coeff_sub, sub_eq_zero] using hzero

/-- To compute the coefficient of `Xⁿ` after substituting `φ`, it suffices to truncate the
input strictly below any `N` with `n < ord(φ) * N`. -/
@[simp]
theorem coeff_substAlgHom_truncLT {N n : ℤ} (f : K⸨X⸩)
    (hn : n < (φ.order.toNat : ℤ) * N) :
    (substAlgHom hφ hφ₀ (HahnSeries.truncLT N f)).coeff n =
      (substAlgHom hφ hφ₀ f).coeff n := by
  apply coeff_substAlgHom_eq_of_coeff_eq hφ hφ₀ (N := N) _ hn
  intro j hj
  simp [hj]

/-- The coefficient of a general Laurent substitution is a finite sum over the input exponents
from `ord f` to any cutoff `N` satisfying `n < ord(φ) * N`. Negative input exponents contribute
negative powers of `φ` in the Laurent field. -/
theorem coeff_substAlgHom_eq_sum_Ico {N n : ℤ} (f : K⸨X⸩)
    (hn : n < (φ.order.toNat : ℤ) * N) :
    (substAlgHom hφ hφ₀ f).coeff n =
      ∑ j ∈ Finset.Ico f.order N, f.coeff j * ((φ : K⸨X⸩) ^ j).coeff n := by
  classical
  rw [← coeff_substAlgHom_truncLT hφ hφ₀ f hn,
    ← _root_.LaurentSeries.toLaurentSeries_trunc,
    _root_.LaurentSeries.trunc_eq_sum_Ico, map_sum, map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [LaurentPolynomial.toLaurentSeries_single, substAlgHom_single,
    C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

/-- The coefficient of `Xⁿ` in `f(φ)` is the finite sum over input exponents from `ord f` through
`⌊n / ord φ⌋`, inclusive. The integer division and negative Laurent powers make the formula
valid also for negative output exponents. -/
theorem coeff_substAlgHom_eq_sum_Icc (f : K⸨X⸩) (n : ℤ) :
    (substAlgHom hφ hφ₀ f).coeff n =
      ∑ j ∈ Finset.Icc f.order (n / (φ.order.toNat : ℤ)),
        f.coeff j * ((φ : K⸨X⸩) ^ j).coeff n := by
  have he : (0 : ℤ) < φ.order.toNat := by
    exact_mod_cast Nat.pos_of_ne_zero (toNat_order_ne_zero hφ hφ₀)
  have hn : n < (φ.order.toNat : ℤ) * (n / (φ.order.toNat : ℤ) + 1) := by
    have := Int.emod_lt_of_pos n he
    have := Int.emod_add_ediv_mul n (φ.order.toNat : ℤ)
    nlinarith
  simpa only [Finset.Ico_add_one_right_eq_Icc] using
    coeff_substAlgHom_eq_sum_Ico hφ hφ₀ f hn

end TauCeti.LaurentSeries
