/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import TauCeti.Analysis.SpecialFunctions.Log.WithZero
public import TauCeti.RingTheory.Valuation.ToAdditive

/-!
# Real additive valuations from valuations of rank at most one

`Valuation.normAddValuation` uses the real embedding in `Valuation.RankLeOne` and the
conversion `Valuation.addVal`. Its finite values are the negative logarithms of the associated
norm, and its infinite values occur exactly on the support of the valuation.

For the rank-one construction over a field, see Neukirch, *Algebraic Number Theory*,
Chapter II, §3.
-/

public section

open scoped NNReal WithZero

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) [v.RankLeOne]

/-- The real additive valuation given by the negative logarithm of the chosen rank-at-most-one
norm, with value `⊤` at elements of norm zero. -/
noncomputable def normAddValuation : AddValuation R (WithTop ℝ) :=
  let f : ℝ≥0 →*₀o ℝᵐ⁰ := Real.expOrderMonoidIsoWithZero.symm
  let g : v.ValueGroup₀ →*₀o NNReal :=
    { RankLeOne.hom' v with monotone' := (RankLeOne.strictMono' (v := v)).monotone }
  (v.restrict.map (f.comp g)).addVal

/-- Evaluation via the inverse exponential and the additive value-group dictionary.
This expansion stays out of the simp set so that support and comparison lemmas can match
applications of `normAddValuation`. -/
theorem normAddValuation_apply (x : R) :
    v.normAddValuation x =
      WithZero.negLog (Real.expOrderMonoidIsoWithZero.symm (RankLeOne.hom' v (v.restrict x))) := by
  simp only [normAddValuation, addVal_apply, map_apply, OrderMonoidWithZeroHom.comp_apply,
    OrderMonoidWithZeroHom.coe_toOrderMonoidWithZeroHom, OrderMonoidWithZeroHom.coe_mk]

variable {v} in
/-- The real additive valuation is infinite exactly on the support of the valuation. -/
@[simp]
theorem normAddValuation_eq_top_iff {x : R} : v.normAddValuation x = ⊤ ↔ v x = 0 := by
  rw [normAddValuation_apply, WithZero.negLog_eq_top]
  calc
    _ ↔ RankLeOne.hom' v (v.restrict x) = 0 :=
      MonoidWithZeroHom.map_eq_zero_iff (f := .ofClass Real.expOrderMonoidIsoWithZero.symm)
    _ ↔ v.restrict x = 0 := MonoidWithZeroHom.map_eq_zero_iff
    _ ↔ v x = 0 := v.restrict_eq_zero_iff

/-- Away from the support, the real additive valuation is the negative logarithm of the norm
associated to the chosen embedding of the value group. -/
theorem normAddValuation_apply_of_ne_zero {x : R} (hx : v x ≠ 0) :
    v.normAddValuation x = ((-Real.log (v.norm x) : ℝ) : WithTop ℝ) := by
  have hnorm : 0 < v.norm x := v.norm_pos_iff_valuation_pos.mpr (pos_iff_ne_zero.mpr hx)
  have h : RankLeOne.hom' v (v.restrict x) ≠ 0 :=
    (NNReal.coe_pos.mp (v.norm_def ▸ hnorm)).ne'
  rw [normAddValuation_apply, Real.expOrderMonoidIsoWithZero_symm_apply_of_ne_zero h,
    WithZero.negLog_exp, Valuation.norm_def]

variable {v} in
/-- Passing to the real additive valuation reverses the order on values. -/
@[simp]
theorem normAddValuation_le_normAddValuation_iff {x y : R} :
    v.normAddValuation x ≤ v.normAddValuation y ↔ v y ≤ v x := by
  rw [normAddValuation_apply, normAddValuation_apply, WithZero.negLog_le_negLog,
    map_le_map_iff Real.expOrderMonoidIsoWithZero.symm,
    (RankLeOne.strictMono' (v := v)).le_iff_le, v.restrict_le_iff]

end Valuation
