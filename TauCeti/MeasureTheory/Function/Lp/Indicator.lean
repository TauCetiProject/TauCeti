/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.MeasureTheory.Function.SimpleFunc.Dense

/-!
# Indicator classes in `Lᵖ`

The class `MeasureTheory.indicatorConstLp p hs hμs c` of `s.indicator fun _ => c` is linear in the
constant `c`: Mathlib provides additivity, `MeasureTheory.indicatorConstLp_add`, and this file adds
compatibility with scalar multiplication. Together with the norm formula
`MeasureTheory.norm_indicatorConstLp`, this makes `c ↦ indicatorConstLp p hs hμs c` a bounded
linear map, so closed subspaces of `Lᵖ` can be tested on indicator classes of a dense set of
constants.

In `L∞` the indicator of any measurable set is essentially bounded, whatever its measure. The
class `TauCeti.linftyIndicator μ s hs` of `1_s` in real `L∞(μ)` therefore needs no finiteness of
`μ s`, unlike `indicatorConstLp`. It is additive on disjoint sets, nonnegative, vanishes on null
sets, and equals the constant one at `univ`.

## Main declarations

* `TauCeti.indicatorConstLp_smul`: the indicator class of `a • c` is `a` times that of `c`.
* `TauCeti.linftyIndicator μ s hs`: the class in `L∞(μ)` of the indicator of a measurable set.
* `MeasureTheory.SimpleFunc.toLpTop_piecewise_const_zero`: the class of a simple function
  `c • 1_s` is `c • linftyIndicator μ s hs`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α 𝕜 E : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [NormedAddCommGroup E]
  [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {s : Set α}

/-- A version of `Set.indicator_const_smul` for `MeasureTheory.indicatorConstLp`. -/
theorem indicatorConstLp_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (a : 𝕜) (c : E) :
    indicatorConstLp p hs hμs (a • c) = a • indicatorConstLp p hs hμs c := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := a • c),
    Lp.coeFn_smul a (indicatorConstLp p hs hμs c),
    indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)] with x h₁ h₂ h₃
  rw [h₁, h₂, Pi.smul_apply, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

end TauCeti

noncomputable section

open Set
open scoped ENNReal

namespace TauCeti

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α}

variable (μ) in
/-- The class in `L∞(μ)` of the indicator function of a measurable set. Unlike
`MeasureTheory.indicatorConstLp`, it needs no finiteness of `μ s`. -/
def linftyIndicator (s : Set α) (hs : MeasurableSet s) : Lp ℝ ∞ μ :=
  SimpleFunc.toLpTop μ ℝ (SimpleFunc.piecewise s hs (SimpleFunc.const α 1) 0)

/-- A constant multiple of an indicator, as a simple function, has class a multiple of
`TauCeti.linftyIndicator`. -/
@[simp]
theorem _root_.MeasureTheory.SimpleFunc.toLpTop_piecewise_const_zero (hs : MeasurableSet s)
    (c : ℝ) : SimpleFunc.toLpTop μ ℝ (SimpleFunc.piecewise s hs (SimpleFunc.const α c) 0) =
      c • linftyIndicator μ s hs := by
  rw [linftyIndicator, ← map_smul]
  congr 1
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- The class `TauCeti.linftyIndicator μ s hs` is almost everywhere the indicator of `s`. -/
theorem coeFn_linftyIndicator (hs : MeasurableSet s) :
    linftyIndicator μ s hs =ᵐ[μ] s.indicator 1 := by
  filter_upwards [SimpleFunc.coeFn_toLpTop (μ := μ) (𝕜 := ℝ)
    (SimpleFunc.piecewise s hs (SimpleFunc.const α (1 : ℝ)) 0)] with x hx
  rw [linftyIndicator, hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

/-- The indicator of the empty set vanishes in `L∞`. -/
@[simp]
theorem linftyIndicator_empty : linftyIndicator μ ∅ MeasurableSet.empty = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) MeasurableSet.empty, Lp.coeFn_zero ℝ ∞ μ]
    with x h h0
  rw [h, h0, Set.indicator_empty, Pi.zero_apply]

/-- The indicator of the whole space is the constant one in `L∞`. -/
@[simp]
theorem linftyIndicator_univ : linftyIndicator μ univ MeasurableSet.univ = linftyOne := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) MeasurableSet.univ, coeFn_linftyOne (μ := μ)]
    with x h h1
  rw [h, h1, Set.indicator_univ, Pi.one_apply]

/-- Indicators of disjoint measurable sets add in `L∞`. -/
theorem linftyIndicator_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    linftyIndicator μ (s ∪ t) (hs.union ht) = linftyIndicator μ s hs + linftyIndicator μ t ht := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) (hs.union ht), coeFn_linftyIndicator (μ := μ) hs,
    coeFn_linftyIndicator (μ := μ) ht, Lp.coeFn_add (linftyIndicator μ s hs)
      (linftyIndicator μ t ht)] with x h hsx htx hadd
  rw [h, hadd, Pi.add_apply, hsx, htx, Set.indicator_union_of_disjoint hst]

/-- The indicator of a measurable set is nonnegative in `L∞`. -/
theorem linftyIndicator_nonneg (hs : MeasurableSet s) : 0 ≤ linftyIndicator μ s hs := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [coeFn_linftyIndicator (μ := μ) hs] with x hx
  rw [hx]
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

/-- The indicator of a null set vanishes in `L∞`. -/
theorem linftyIndicator_of_measure_eq_zero (hs : MeasurableSet s) (h : μ s = 0) :
    linftyIndicator μ s hs = 0 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_linftyIndicator (μ := μ) hs, Lp.coeFn_zero ℝ ∞ μ,
    measure_eq_zero_iff_ae_notMem.1 h] with x hx h0 hxs
  rw [hx, h0, Set.indicator_of_notMem hxs, Pi.zero_apply]

end TauCeti

end
