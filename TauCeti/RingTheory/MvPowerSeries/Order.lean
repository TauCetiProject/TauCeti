/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Order

/-!
# Lowest-degree homogeneous components of powers

If a series has order at least `p`, the degree-`n * p` homogeneous component of its `n`-th power
is the `n`-th power of its degree-`p` component. This reduces lowest-degree coefficient
computations for powers to homogeneous series, over arbitrary semirings.

For two-variable series with linear coefficients one, the degree-one component is `X + Y`.
Over a ring, vanishing of the constant coefficient then puts the remainder after subtracting
`X + Y` in order at least two.
-/

public section

namespace MvPowerSeries

section Powers

variable {σ R : Type*} [Semiring R] {f : MvPowerSeries σ R}

/-- The lowest possible homogeneous component of a power is the corresponding power of the
lowest possible homogeneous component. -/
theorem homogeneousComponent_pow_of_le_order {p : ℕ} (hf : p ≤ f.order) (n : ℕ) :
    homogeneousComponent (n * p) (f ^ n) = (homogeneousComponent p f) ^ n := by
  classical
  induction n with
  | zero =>
    ext d
    by_cases hd : d = 0 <;>
      simp [coeff_homogeneousComponent, coeff_one, Finsupp.degree_eq_zero_iff, hd]
  | succ n ih =>
    have hn : (n * p : ℕ) ≤ (f ^ n).order := by
      simpa only [nsmul_eq_mul, Nat.cast_mul] using
        (nsmul_le_nsmul_right hf n).trans (le_order_pow n)
    rw [pow_succ, Nat.succ_mul, homogeneousComponent_mul_of_le_order hn hf, ih, pow_succ]

end Powers

open Finsupp

variable {R : Type*} {f : MvPowerSeries (Fin 2) R}

/-- A series whose two linear coefficients are one has degree-one homogeneous component
`X + Y`, independently of its constant coefficient. -/
theorem homogeneousComponent_one_eq_X_add_X [Semiring R]
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) :
    homogeneousComponent 1 f = X 0 + X 1 := by
  ext d
  rw [coeff_homogeneousComponent]
  by_cases hdeg : d.degree = 1
  · obtain ⟨j, rfl⟩ := (Set.ext_iff.mp range_single_one d).mpr hdeg
    fin_cases j <;> simp [hX, hY, coeff_X, single_eq_single_iff]
  · have hX' : d ≠ single 0 1 := fun h ↦ hdeg (by simp [h])
    have hY' : d ≠ single 1 1 := fun h ↦ hdeg (by simp [h])
    simp [hdeg, coeff_X, hX', hY']

section Ring

variable [Ring R]

/-- A power series in two variables with zero constant coefficient and linear part `X + Y` differs
from `X + Y` by a series of order at least two. -/
theorem two_le_order_sub_X_add_X (h₀ : f.constantCoeff = 0)
    (hX : coeff (single 0 1) f = 1) (hY : coeff (single 1 1) f = 1) :
    2 ≤ (f - (X 0 + X 1)).order := by
  refine nat_le_order (n := 2) fun d hd => ?_
  have hdeg : d.degree = 0 ∨ d.degree = 1 := by omega
  rcases hdeg with hdeg | hdeg
  · simp [(degree_eq_zero_iff d).mp hdeg, h₀]
  · have hc := congrArg (coeff d) (homogeneousComponent_one_eq_X_add_X hX hY)
    simp only [coeff_homogeneousComponent, ite_eq_left hdeg] at hc
    simp [hc]

end Ring

end MvPowerSeries
