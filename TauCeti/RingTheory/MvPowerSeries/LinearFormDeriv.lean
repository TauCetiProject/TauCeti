/-
Copyright (c) 2026 TauCeti Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.RingTheory.MvPowerSeries.Rescale

import Mathlib.Data.Fin.VecNotation
import TauCeti.RingTheory.MvPowerSeries.Derivative

/-!
# Linear-form substitution and transport uniqueness for multivariate power series

This file defines the linear form `∑ x, c x • X x` as a multivariate power series, proves the
chain rule and rescaling identity for substituting a linear form into a univariate power series,
and proves uniqueness for the two-variable transport operator `∂₀ - ∂₁` with initial condition
along `z₀ = 0`.

## Main definitions and results

* `TauCeti.linearSeries`: the homogeneous linear form `∑ x, c x • X x` in `MvPowerSeries X R`.
* `TauCeti.hasSubst_linearSeries`: `linearSeries c` has constant term `0` and is substitutable.
* `TauCeti.pderiv_subst_linearSeries`: `∂_x (g(c · z)) = c x • g'(c · z)`.
* `TauCeti.rescale_subst_linearSeries_eq_mul`: rescaling `g(c · z)` by `a` gives `g((a * c) · z)`.
* `TauCeti.eq_of_pderiv_sub_eq_of_rescale_eq`: over a characteristic-zero domain, a bivariate power
  series is uniquely determined by `∂₀ E - ∂₁ E` and its restriction `E(0, z₁)`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file `src/Lib/CM/Integrality/LogTheta.lean`
(`New.hasSubst_linearSeries`, `New.pderiv_subst_linearSeries`,
`New.rescale_subst_linearSeries_eq_mul`, `New.eq_of_pderiv_sub_eq_of_rescale_eq`).
-/

@[expose] public section

namespace TauCeti

open MvPowerSeries

section LinearForms

variable {X R : Type*} [Fintype X] [CommRing R]

/-- The homogeneous linear form `∑ x, c x • X x` in `MvPowerSeries X R`. -/
noncomputable def linearSeries (c : X → R) : MvPowerSeries X R :=
  ∑ x : X, c x • MvPowerSeries.X x

/-- The linear form `linearSeries c = ∑ x, c x • X x` has constant term zero, so it can be
substituted into a univariate power series. -/
theorem hasSubst_linearSeries (c : X → R) : PowerSeries.HasSubst (linearSeries c) := by
  refine .of_constantCoeff_zero ?_
  simp [linearSeries, map_sum, MvPowerSeries.constantCoeff_X]

/-- The chain rule for a univariate power series `g` composed with a linear form: the partial
derivative of `g(c · z)` in the variable `z_x` is `c x` times `g'(c · z)`. -/
theorem pderiv_subst_linearSeries (c : X → R) (g : PowerSeries R) (x : X) :
    pderiv x (g.subst (linearSeries c)) =
      c x • (PowerSeries.derivative g).subst (linearSeries c) := by
  classical
  have hp : pderiv x (linearSeries c) = C (c x) := by
    simp [linearSeries, pderiv_X, Pi.single_apply, smul_eq_C_mul]
  rw [PowerSeries.subst_def, pderiv_subst (hasSubst_linearSeries c).const,
    Fintype.sum_unique, hp, smul_eq_C_mul, mul_comm]
  rfl

/-- Rescaling the variables of `g(c · z)` by `a` multiplies the coefficients of the linear form
by `a`. -/
theorem rescale_subst_linearSeries_eq_mul (a c : X → R) (g : PowerSeries R) :
    rescale a (g.subst (linearSeries c)) = g.subst (linearSeries (a * c)) := by
  have ha : HasSubst (a • (MvPowerSeries.X : X → MvPowerSeries X R)) := .smul_X a
  have h_linear : (linearSeries c).subst (a • MvPowerSeries.X) = linearSeries (a * c) := by
    simp only [linearSeries, ← coe_substAlgHom ha, map_sum, map_smul, substAlgHom_X,
      Pi.smul_apply', Pi.mul_apply, smul_smul, mul_comm]
  rw [rescale_eq_subst, PowerSeries.subst_def,
    subst_comp_subst_apply (hasSubst_linearSeries c).const ha, h_linear, PowerSeries.subst_def]

end LinearForms

/-- Over a characteristic-zero domain, a formal power series in two variables is uniquely
determined by its image under `∂₀ - ∂₁` and its restriction to `z₀ = 0`. -/
theorem eq_of_pderiv_sub_eq_of_rescale_eq {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {E F : MvPowerSeries (Fin 2) R}
    (h_deriv : E.pderiv 0 - E.pderiv 1 = F.pderiv 0 - F.pderiv 1)
    (h_zero : E.rescale ![0, 1] = F.rescale ![0, 1]) : E = F := by
  ext D
  induction hD : D 0 generalizing D with
  | zero =>
    simpa [coeff_rescale, Finsupp.prod_pow, hD] using congrArg (coeff D) h_zero
  | succ n ih =>
    set D' : Fin 2 →₀ ℕ := D - Finsupp.single 0 1 with hD'
    have h_one : coeff (D' + Finsupp.single 1 1) E = coeff (D' + Finsupp.single 1 1) F :=
      ih _ (by simp [hD', hD])
    have h_add : D' + Finsupp.single 0 1 = D := tsub_add_cancel_of_le (by simp [hD])
    simpa [coeff_pderiv, h_one, h_add, Nat.cast_add_one_ne_zero] using congrArg (coeff D') h_deriv

end TauCeti
