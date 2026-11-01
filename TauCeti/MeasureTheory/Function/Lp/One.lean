/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The constant one and indicator classes in `L∞`

This file defines the constant-one element of `L∞` on an arbitrary measure space, and the class
in `L∞` of the indicator function of a measurable set. Unlike `MeasureTheory.Lp.const` and
`MeasureTheory.indicatorConstLp`, the constructions need no finiteness hypothesis on the measure,
because the essential supremum of a bounded function is always finite.

The constant one is an order unit for the essential supremum norm, `f ≤ ‖f‖ • 1`
(`TauCeti.le_norm_smul_linftyOne`). This is the domination hypothesis of the automatic continuity
results for positive functionals in `TauCeti.Analysis.Normed.Order.PositiveLinearMap`. Indicator
classes are additive on disjoint sets and vanish on null sets, so a linear functional on `L∞`
restricts to a finitely additive set function on the measurable sets which vanishes on null sets.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

namespace TauCeti

/-- The constant-one element of `L∞(μ)`. -/
noncomputable def linftyOne : Lp ℝ ∞ μ :=
  (memLp_top_const (1 : ℝ)).toLp fun _ => 1

/-- The representative of `linftyOne` is almost everywhere the constant function one. -/
theorem coeFn_linftyOne :
    (linftyOne (Ω := Ω) (μ := μ) : Ω → ℝ) =ᵐ[μ] fun _ => 1 :=
  MemLp.coeFn_toLp (memLp_top_const (1 : ℝ))

/-- The constant class one is an order unit for the essential supremum norm. -/
theorem le_norm_smul_linftyOne (f : Lp ℝ ∞ μ) : f ≤ ‖f‖ • linftyOne := by
  rw [← Lp.coeFn_le]
  filter_upwards [ae_le_lpNorm_exponent_top (Lp.memLp f), Lp.coeFn_smul ‖f‖ linftyOne,
    coeFn_linftyOne] with x hx hsmul h1
  rw [hsmul, Pi.smul_apply, h1, smul_eq_mul, mul_one]
  exact (Real.le_norm_self _).trans hx

variable {s t : Set Ω}

/-- The class in `L∞(μ)` of the indicator function of a measurable set `s`. Unlike
`MeasureTheory.indicatorConstLp ∞`, no finiteness of `μ s` is required. -/
noncomputable def linftyIndicator (hs : MeasurableSet s) : Lp ℝ ∞ μ :=
  ((memLp_top_const (1 : ℝ)).indicator hs.nullMeasurableSet).toLp (s.indicator fun _ => 1)

/-- The representative of `linftyIndicator hs` is almost everywhere the indicator function of
`s`. -/
theorem coeFn_linftyIndicator (hs : MeasurableSet s) :
    (linftyIndicator (μ := μ) hs : Ω → ℝ) =ᵐ[μ] s.indicator fun _ => 1 :=
  MemLp.coeFn_toLp _

/-- On a set of finite measure, `linftyIndicator` is Mathlib's indicator class
`MeasureTheory.indicatorConstLp` with exponent `∞`. -/
theorem indicatorConstLp_top_one (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    indicatorConstLp ∞ hs hμs (1 : ℝ) = linftyIndicator hs :=
  Lp.ext (indicatorConstLp_coeFn.trans (coeFn_linftyIndicator hs).symm)

@[simp]
theorem linftyIndicator_univ : linftyIndicator (μ := μ) MeasurableSet.univ = linftyOne :=
  Lp.ext ((coeFn_linftyIndicator _).trans (by simpa using coeFn_linftyOne.symm))

/-- Indicator classes add on disjoint sets. -/
theorem linftyIndicator_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    linftyIndicator (μ := μ) (hs.union ht) = linftyIndicator hs + linftyIndicator ht := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) (hs.union ht), coeFn_linftyIndicator (μ := μ) hs,
    coeFn_linftyIndicator (μ := μ) ht, Lp.coeFn_add (linftyIndicator (μ := μ) hs)
      (linftyIndicator ht)] with x hst' hs' ht' hadd
  rw [hst', hadd, Pi.add_apply, hs', ht', Set.indicator_union_of_disjoint hst]

/-- An indicator class is nonnegative. -/
theorem linftyIndicator_nonneg (hs : MeasurableSet s) : 0 ≤ linftyIndicator (μ := μ) hs := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_linftyIndicator (μ := μ) hs] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- The indicator class of a null set vanishes. -/
theorem linftyIndicator_of_measure_eq_zero (hs : MeasurableSet s) (hμs : μ s = 0) :
    linftyIndicator (μ := μ) hs = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) hs, Lp.coeFn_zero ℝ ∞ μ,
    measure_eq_zero_iff_ae_notMem.1 hμs] with x hx h0 hxs
  rw [hx, h0, Set.indicator_of_notMem hxs, Pi.zero_apply]

@[simp]
theorem linftyIndicator_empty : linftyIndicator (μ := μ) MeasurableSet.empty = 0 :=
  linftyIndicator_of_measure_eq_zero _ measure_empty

end TauCeti
