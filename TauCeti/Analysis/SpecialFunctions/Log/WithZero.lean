/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.NNReal.Basic

/-!
# The exponential with an adjoined zero

`Real.expOrderMonoidIsoWithZero` extends `Real.expOrderIso` to an ordered multiplicative
isomorphism from `WithZero (Multiplicative ℝ)` to the nonnegative reals.
-/

public section

open scoped NNReal WithZero

namespace Real

/-- On finite exponents the map is the exponential, and the adjoined zero maps to zero. -/
noncomputable def expOrderMonoidIsoWithZero : WithZero (Multiplicative ℝ) ≃*o ℝ≥0 :=
  let e : Multiplicative ℝ ≃*o ℝ≥0ˣ :=
    { toMulEquiv :=
        { toEquiv :=
            (Multiplicative.ofAdd : ℝ ≃ Multiplicative ℝ).symm.trans
              (Real.expOrderIso.toEquiv.trans (Nonneg.unitsEquivPos ℝ).symm.toEquiv)
          map_mul' x y := by
            apply Units.ext
            apply NNReal.eq
            exact Real.exp_add x.toAdd y.toAdd }
      map_le_map_iff' := fun {x y} ↦ by
        exact Real.exp_le_exp }
  e.withZero.trans OrderMonoidIso.withZeroUnits

/-- The scalar evaluation rule for the extended exponential on finite exponents. This projection
lets callers compute with the isomorphism without unfolding its construction. -/
@[simp]
theorem expOrderMonoidIsoWithZero_apply_exp (x : ℝ) :
    (expOrderMonoidIsoWithZero (WithZero.exp x) : ℝ) = exp x := (rfl)

/-- The inverse extended exponential is the real logarithm at positive arguments. -/
theorem expOrderMonoidIsoWithZero_symm_apply_of_ne_zero {r : ℝ≥0} (hr : r ≠ 0) :
    expOrderMonoidIsoWithZero.symm r = WithZero.exp (log (r : ℝ)) := by
  rw [OrderMonoidIso.symm_apply_eq]
  apply NNReal.eq
  exact (Real.exp_log (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr))).symm

end Real
