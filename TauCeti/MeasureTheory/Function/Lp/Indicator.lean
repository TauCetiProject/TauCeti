/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import TauCeti.MeasureTheory.Function.Lp.One

/-!
# Indicator classes in `Lᵖ` and `L∞`

The class `MeasureTheory.indicatorConstLp p hs hμs c` of `s.indicator fun _ => c` is linear in the
constant `c`: Mathlib provides additivity, `MeasureTheory.indicatorConstLp_add`, and this file adds
compatibility with scalar multiplication. Together with the norm formula
`MeasureTheory.norm_indicatorConstLp`, this makes `c ↦ indicatorConstLp p hs hμs c` a bounded
linear map, so closed subspaces of `Lᵖ` can be tested on indicator classes of a dense set of
constants.

In `L∞` the indicator function of a measurable set is essentially bounded whatever the measure of
the set, so `MeasureTheory.indicatorConstLpTop μ hs c` is defined for sets of arbitrary measure;
Mathlib's `MeasureTheory.indicatorConstLp` requires `μ s ≠ ∞`.

## Main declarations

* `TauCeti.indicatorConstLp_smul`: the indicator class of `a • c` is `a` times that of `c`.
* `MeasureTheory.indicatorConstLpTop`: the class in `L∞` of `s.indicator fun _ ↦ c`, for a
  measurable set `s` of arbitrary measure. It is additive on disjoint sets, compatible with
  scalar multiplication, and the constant one on the whole space.
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

namespace MeasureTheory

open Set
open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α] (μ : Measure α) [NormedAddCommGroup E] {s : Set α}

/-- The class in `L∞` of the indicator function of a measurable set `s` with value `c`. Unlike
`MeasureTheory.indicatorConstLp`, no finiteness of `μ s` is needed. -/
noncomputable def indicatorConstLpTop (hs : MeasurableSet s) (c : E) : Lp E ∞ μ :=
  ((memLp_top_const c).indicator hs.nullMeasurableSet).toLp (s.indicator fun _ => c)

/-- The indicator class of `s` with value `c` is represented by `s.indicator fun _ ↦ c`. -/
theorem indicatorConstLpTop_coeFn (hs : MeasurableSet s) (c : E) :
    indicatorConstLpTop μ hs c =ᵐ[μ] s.indicator fun _ => c :=
  MemLp.coeFn_toLp _

/-- The indicator class of the whole space is the constant one. -/
@[simp]
theorem indicatorConstLpTop_univ : indicatorConstLpTop μ MeasurableSet.univ (1 : ℝ) =
    TauCeti.linftyOne := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLpTop_coeFn μ MeasurableSet.univ (1 : ℝ), TauCeti.coeFn_linftyOne]
    with x h h1
  rw [h, h1, indicator_univ]

/-- The indicator class of a null set vanishes. -/
theorem indicatorConstLpTop_eq_zero (hs : MeasurableSet s) (hμs : μ s = 0) (c : E) :
    indicatorConstLpTop μ hs c = 0 := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLpTop_coeFn μ hs c, Lp.coeFn_zero E ∞ μ,
    measure_eq_zero_iff_ae_notMem.1 hμs] with x h h0 hx
  rw [h, h0, indicator_of_notMem hx, Pi.zero_apply]

/-- Indicator classes add on disjoint sets. -/
theorem indicatorConstLpTop_union {t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) (c : E) :
    indicatorConstLpTop μ (hs.union ht) c =
      indicatorConstLpTop μ hs c + indicatorConstLpTop μ ht c := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLpTop_coeFn μ (hs.union ht) c, indicatorConstLpTop_coeFn μ hs c,
    indicatorConstLpTop_coeFn μ ht c, Lp.coeFn_add (indicatorConstLpTop μ hs c)
      (indicatorConstLpTop μ ht c)] with x h hs' ht' hadd
  rw [hadd, Pi.add_apply, h, hs', ht', indicator_union_of_disjoint hst]

/-- A version of `Set.indicator_const_smul` for `MeasureTheory.indicatorConstLpTop`. -/
theorem indicatorConstLpTop_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (hs : MeasurableSet s) (a : 𝕜) (c : E) :
    indicatorConstLpTop μ hs (a • c) = a • indicatorConstLpTop μ hs c := by
  refine Lp.ext ?_
  filter_upwards [indicatorConstLpTop_coeFn μ hs (a • c), indicatorConstLpTop_coeFn μ hs c,
    Lp.coeFn_smul a (indicatorConstLpTop μ hs c)] with x h h' hsmul
  rw [hsmul, Pi.smul_apply, h, h', indicator_const_smul_apply]

/-- A real indicator class is nonnegative when its value is. -/
theorem indicatorConstLpTop_nonneg (hs : MeasurableSet s) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ indicatorConstLpTop μ hs c := by
  rw [← Lp.coeFn_nonneg]
  filter_upwards [indicatorConstLpTop_coeFn μ hs c] with x h
  rw [h]
  exact indicator_nonneg (fun _ _ => hc) x

end MeasureTheory
