/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Differentiation of Laurent series

The coefficientwise formal derivative of Laurent series satisfies the Leibniz rule over any
commutative ring. Bundling it as a derivation allows the universal property of Kähler
differentials to compare it with differentiation of algebraic functions in a local parameter.

The underlying linear map is Mathlib's `LaurentSeries.derivative`; no new differentiation
operation is introduced.
-/

public section

open HahnSeries

namespace TauCeti.LaurentSeries

variable (R : Type*) [CommRing R]

-- Multiplication by `X` turns differentiation into the support-preserving Euler operator.
private theorem coeff_X_mul_derivative (f : LaurentSeries R) (n : ℤ) :
    (single 1 (1 : R) * _root_.LaurentSeries.derivative R f).coeff n =
      (n : R) * f.coeff n := by
  rw [coeff_single_mul, one_mul]
  simp [_root_.LaurentSeries.derivative_apply, sub_add_cancel]

private theorem support_X_mul_derivative (f : LaurentSeries R) :
    (single 1 (1 : R) * _root_.LaurentSeries.derivative R f).support ⊆ f.support := by
  intro n hn
  rw [mem_support, coeff_X_mul_derivative] at hn
  exact (mem_support f n).mpr (right_ne_zero_of_mul hn)

/-- The coefficientwise Laurent derivative satisfies the product rule, in arbitrary
characteristic. -/
theorem derivative_mul (f g : LaurentSeries R) :
    _root_.LaurentSeries.derivative R (f * g) =
      f * _root_.LaurentSeries.derivative R g +
        g * _root_.LaurentSeries.derivative R f := by
  classical
  have hEuler : single 1 (1 : R) * _root_.LaurentSeries.derivative R (f * g) =
      f * (single 1 (1 : R) * _root_.LaurentSeries.derivative R g) +
        (single 1 (1 : R) * _root_.LaurentSeries.derivative R f) * g := by
    ext n
    rw [coeff_X_mul_derivative, coeff_mul, coeff_add,
      coeff_mul_right' g.isPWO_support (support_X_mul_derivative R g),
      coeff_mul_left' f.isPWO_support (support_X_mul_derivative R f),
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    have hij' := (Finset.mem_antidiagonal.mp hij).2.2
    rw [coeff_X_mul_derivative, coeff_X_mul_derivative, ← hij', Int.cast_add]
    ring
  have h' : single 1 (1 : R) * _root_.LaurentSeries.derivative R (f * g) =
      single 1 (1 : R) *
        (f * _root_.LaurentSeries.derivative R g +
          g * _root_.LaurentSeries.derivative R f) := by
    simpa only [mul_add, mul_assoc, mul_left_comm, mul_comm] using hEuler
  ext n
  have h := congrArg (fun s : LaurentSeries R ↦ s.coeff (n + 1)) h'
  simpa only [coeff_single_mul_add, one_mul] using h

/-- Formal Laurent differentiation as a derivation. Its linear map is the existing
coefficientwise derivative. -/
noncomputable def derivativeDerivation : Derivation R (LaurentSeries R) (LaurentSeries R) where
  -- The source algebra action and the coefficientwise scalar action agree propositionally.
  toFun f := _root_.LaurentSeries.derivative R f
  map_add' f g := (_root_.LaurentSeries.derivative R).map_add f g
  map_smul' c f := by
    ext n
    simp [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C]
  map_one_eq_zero' := by
    ext n
    suffices n + 1 = 0 → (n : R) + 1 = 0 by
      simpa [_root_.LaurentSeries.derivative_apply, coeff_one]
    intro h
    simpa using congrArg (fun i : ℤ ↦ (i : R)) h
  leibniz' f g := by
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] using derivative_mul R f g

/-- The bundled Laurent derivation evaluates as the coefficientwise derivative. -/
@[simp]
theorem derivativeDerivation_apply (f : LaurentSeries R) :
    derivativeDerivation R f = _root_.LaurentSeries.derivative R f := (rfl)

end TauCeti.LaurentSeries
