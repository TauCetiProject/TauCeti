/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.Data.Nat.Choose.Cast

/-!
# The functional equation of the exponential for substituted series

For series `a` and `b` without constant term in any number of variables over a `ℚ`-algebra,
`exp (a + b) = exp a * exp b`, where `exp g` is the substitution `(PowerSeries.exp A).subst g`.
The universal case `exp (X₀ + X₁) = exp X₀ * exp X₁` in two variables is the identity
`(m + n).choose m / (m + n)! = 1 / m! * 1 / n!` between coefficients; substituting `a` and `b` for
`X₀` and `X₁` gives the general case.

## Main declarations

* `PowerSeries.subst_exp_add`: `exp (a + b) = exp a * exp b`.

## Provenance

Adapted from `New.expSubst_add` in `src/Lib/General/Algebra/IntegralPowerSeries.lean` of the Lean
proof of the Riemann hypothesis by Levent Alpöge with Claude, as published under Apache 2.0 at
https://github.com/leanprover-community/riemann-hypothesis (commit `3ad0b4b58709`), where the
coefficients are in `ℂ_[p]`. Here they are in any commutative `ℚ`-algebra.
-/

public section

namespace PowerSeries

variable {A σ : Type*} [CommRing A] [Algebra ℚ A]

/-- **The functional equation of the exponential.** For multivariate series `a` and `b` without
constant term, `exp (a + b) = exp a * exp b`. -/
theorem subst_exp_add {a b : MvPowerSeries σ A} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    (exp A).subst (a + b) = (exp A).subst a * (exp A).subst b := by
  -- The universal case in two variables, compared coefficient by coefficient.
  have h_univ : (exp A).subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) =
      (exp A).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A) *
        (exp A).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A) := by
    ext e
    rw [coeff_subst_X_zero_add_X_one, coeff_subst_X_zero_subst_mul_X_one]
    simp only [coeff_exp, ← map_natCast (algebraMap ℚ A), ← map_mul]
    congr 1
    rw [Nat.cast_add_choose ℚ]
    field_simp
  have hab : MvPowerSeries.HasSubst ![a, b] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (by simp [Fin.forall_fin_two, ha, hb])
  -- Substituting `a` for `X₀` and `b` for `X₁` commutes with the exponential.
  have h_comm (F : MvPowerSeries (Fin 2) A) (hF : MvPowerSeries.constantCoeff F = 0) :
      ((exp A).subst F).subst ![a, b] = (exp A).subst (F.subst ![a, b]) :=
    MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero hF).const hab _
  simpa [MvPowerSeries.subst_add hab, MvPowerSeries.subst_mul hab, h_comm,
    MvPowerSeries.subst_X hab] using congrArg (MvPowerSeries.subst ![a, b]) h_univ

end PowerSeries
