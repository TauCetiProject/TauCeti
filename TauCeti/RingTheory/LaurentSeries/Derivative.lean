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

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- Formal Laurent differentiation as a derivation. Its linear map is the existing
coefficientwise derivative. -/
noncomputable def laurentSeriesDerivation :
    Derivation R (LaurentSeries R) (LaurentSeries R) where
  toFun f := _root_.LaurentSeries.derivative R f
  map_add' f g := (_root_.LaurentSeries.derivative R).map_add f g
  map_smul' c f := by
    -- The source uses the algebra action; Mathlib's derivative uses the coefficientwise action.
    rw [Algebra.smul_def, laurentSeries_algebraMap_mul_eq_smul]
    exact map_smul (_root_.LaurentSeries.derivative R) c f
  map_one_eq_zero' := by
    ext n
    suffices n + 1 = 0 → (n : R) + 1 = 0 by
      simpa [_root_.LaurentSeries.derivative_apply, coeff_one]
    intro h
    simpa using congrArg (fun i : ℤ ↦ (i : R)) h
  leibniz' f g := by
    simpa only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul, mul_comm, add_comm] using
      _root_.LaurentSeries.derivative_mul f g

/-- The bundled Laurent derivation evaluates as the coefficientwise derivative. -/
@[simp]
theorem laurentSeriesDerivation_apply (f : LaurentSeries R) :
    laurentSeriesDerivation R f = _root_.LaurentSeries.derivative R f := (rfl)

end TauCeti
