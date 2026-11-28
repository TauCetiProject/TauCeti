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
  let toUnits : Set.Ioi (0 : ℝ) ≃ ℝ≥0ˣ := (Nonneg.unitsEquivPos ℝ).symm.toEquiv
  let f : Multiplicative ℝ ≃ ℝ≥0ˣ :=
    Multiplicative.toAdd.trans (Real.expOrderIso.toEquiv.trans toUnits)
  have hUnits (r : Set.Ioi (0 : ℝ)) : ((toUnits r).val : ℝ) = (r : ℝ) :=
    Nonneg.val_unitsEquivPos_symm_apply_coe ℝ r
  have hf (x : Multiplicative ℝ) : ((f x).val : ℝ) = Real.exp x.toAdd := by
    simp only [f, Equiv.trans_apply, OrderIso.coe_toEquiv, hUnits, Real.coe_expOrderIso_apply]
  let e : Multiplicative ℝ ≃*o ℝ≥0ˣ :=
    { toMulEquiv :=
        { toEquiv := f
          map_mul' x y := by
            apply Units.ext
            apply NNReal.eq
            simp only [Units.val_mul, NNReal.coe_mul, Equiv.toFun_as_coe, hf, toAdd_mul,
              Real.exp_add] }
      map_le_map_iff' := by
        intro x y
        simp only [← Units.val_le_val, ← NNReal.coe_le_coe, Equiv.toFun_as_coe, hf, Real.exp_le_exp,
          Multiplicative.toAdd_le] }
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
  rw [expOrderMonoidIsoWithZero_apply_exp]
  exact (Real.exp_log (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr))).symm

end Real
