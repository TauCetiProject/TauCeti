/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Negative exponential on the extended nonnegative reals

`ENNReal.expNeg` takes values in `ℝ≥0`, agrees with the negative exponential at finite
arguments, and vanishes at infinity. It is continuous, antitone, and converts addition
into multiplication, also for infinite sums and products. The value at infinity permits
Laplace functionals of measures without assuming that every test integral is finite.

The construction uses Mathlib's `EReal.exp`, including its continuity at minus infinity.
-/

public section

noncomputable section

open scoped ENNReal NNReal

namespace ENNReal

/-- The negative exponential, with value zero at infinity. -/
def expNeg (x : ℝ≥0∞) : ℝ≥0 := (EReal.exp (-x.toEReal)).toNNReal

/-- Compatibility with the extended-real exponential. -/
theorem coe_expNeg (x : ℝ≥0∞) : (expNeg x : ℝ≥0∞) = EReal.exp (-x.toEReal) :=
  coe_toNNReal (by simp)

/-- An infinite argument contributes zero. -/
@[simp] theorem expNeg_top : expNeg ∞ = 0 := by simp [expNeg]

/-- At finite arguments this is the ordinary negative exponential. -/
@[simp] theorem expNeg_coe (x : ℝ≥0) : expNeg (x : ℝ≥0∞) = Real.toNNReal (Real.exp (-x)) := by
  simp [expNeg, EReal.coe_nnreal_eq_coe_real, ← EReal.coe_neg, ENNReal.ofReal]

/-- The negative exponential at zero is one. -/
@[simp] theorem expNeg_zero : expNeg 0 = 1 := by simp [expNeg]

/-- Only an infinite argument contributes zero. -/
@[simp] theorem expNeg_eq_zero_iff {x : ℝ≥0∞} : expNeg x = 0 ↔ x = ∞ := by
  rw [← ENNReal.coe_eq_zero, coe_expNeg]
  simp

/-- The extended negative exponential is antitone, including at infinity. -/
theorem antitone_expNeg : Antitone expNeg := by
  intro x y h
  rw [← ENNReal.coe_le_coe, coe_expNeg, coe_expNeg]
  exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h))

/-- All values of the negative exponential lie in the unit interval. -/
theorem expNeg_le_one (x : ℝ≥0∞) : expNeg x ≤ 1 := by
  simpa using antitone_expNeg (a := 0) (b := x) bot_le

/-- Addition becomes multiplication, even when an argument is infinite. -/
@[simp] theorem expNeg_add (x y : ℝ≥0∞) : expNeg (x + y) = expNeg x * expNeg y := by
  simp only [expNeg, EReal.coe_ennreal_add,
    EReal.neg_add (.inl (EReal.coe_ennreal_ne_bot _)) (.inr (EReal.coe_ennreal_ne_bot _)),
    sub_eq_add_neg, EReal.exp_add, toNNReal_mul]

/-- Continuity includes convergence to zero when the argument tends to infinity. -/
@[fun_prop] theorem continuous_expNeg : Continuous expNeg := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (ENNReal.tendsto_toNNReal (by simp : EReal.exp (-x.toEReal) ≠ ∞)).comp
    (ENNReal.continuous_exp.continuousAt.comp (continuous_coe_ennreal_ereal.continuousAt.neg))

/-- A finite sum becomes a product, including infinite summands. -/
theorem expNeg_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    expNeg (∑ i ∈ s, a i) = ∏ i ∈ s, expNeg (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

/-- The negative exponential of an extended nonnegative series is the infinite product
of the negative exponentials. Divergent series give a zero product. -/
theorem coe_expNeg_tsum {ι : Type*} (a : ι → ℝ≥0∞) :
    (expNeg (∑' i, a i) : ℝ≥0∞) = ∏' i, (expNeg (a i) : ℝ≥0∞) := by
  have h := (continuous_coe.comp continuous_expNeg).continuousAt.tendsto.comp
    (CompleteLattice.summable.hasSum (f := a))
  simp only [Function.comp_def, expNeg_sum, ofNNReal_finsetProd] at h
  exact tendsto_nhds_unique h (ENNReal.multipliable_of_le_one
    (fun i ↦ coe_le_one_iff.mpr (expNeg_le_one (a i)))).hasProd

/-- Measurability of the extended negative exponential. -/
@[fun_prop] theorem measurable_expNeg : Measurable expNeg := continuous_expNeg.measurable

end ENNReal
