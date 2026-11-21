/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.L0.Algebra

/-!
# Indicator-constant classes in `L⁰(μ; E)`

For a null-measurable set `s` and a constant `c : E`, `TauCeti.L0.indicatorConst hs c` is the
class in `TauCeti.L0 E μ` of `s.indicator (fun _ ↦ c)`. Unlike `MeasureTheory.indicatorConstLp`,
no finiteness assumption on `μ s` is required.

On a finite measure space, `TauCeti.L0.dist_indicatorConst_zero` evaluates the `L⁰` distance from
an indicator-constant class to `0` as `μ.real s * (dist c 0 / (1 + dist c 0))`, yielding
`μ.real s / 2` for a unit-height real indicator (`TauCeti.L0.dist_indicatorConst_one_zero`), in
contrast to its disagreement measure `μ.real s` (`TauCeti.L0.measureReal_indicatorConst_ne_zero`).

## Main declarations

* `TauCeti.L0.indicatorConst`: class in `L0 E μ` of `s.indicator (fun _ ↦ c)` for a
  null-measurable set `s`.
* `TauCeti.L0.indicatorConst_add`, `indicatorConst_neg`, `indicatorConst_sub`,
  `smul_indicatorConst`, `ofLp_indicatorConstLp`: algebraic and `Lᵖ` compatibility laws.
* `TauCeti.L0.dist_indicatorConst_zero`, `measureReal_indicatorConst_ne_zero`,
  `dist_indicatorConst_one_zero`: closed-form `L⁰` distance and support measure of indicator
  classes.
-/

public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.L0

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Class in `L0 E μ` of the indicator `s.indicator (fun _ ↦ c)` of a null-measurable set `s`.
Unlike `MeasureTheory.indicatorConstLp`, no finiteness hypothesis on `μ s` is required. -/
def indicatorConst [TopologicalSpace E] [Zero E] {s : Set Ω} (hs : NullMeasurableSet s μ) (c : E) :
    L0 E μ :=
  ofFun (s.indicator fun _ ↦ c) (aestronglyMeasurable_const.indicator₀ hs)

/-- `indicatorConst hs c` is the `L0.ofFun` class of `s.indicator (fun _ ↦ c)`. -/
theorem indicatorConst_eq_ofFun [TopologicalSpace E] [Zero E] {s : Set Ω}
    (hs : NullMeasurableSet s μ) (c : E) :
    indicatorConst hs c =
      ofFun (s.indicator fun _ ↦ c) (aestronglyMeasurable_const.indicator₀ hs) :=
  (rfl)

/-- Forgetting the wrapper on `indicatorConst` gives the native quotient class of the indicator. -/
@[simp]
theorem toAEEqFun_indicatorConst [TopologicalSpace E] [Zero E] {s : Set Ω}
    (hs : NullMeasurableSet s μ) (c : E) :
    (indicatorConst hs c).toAEEqFun =
      AEEqFun.mk (s.indicator fun _ ↦ c) (aestronglyMeasurable_const.indicator₀ hs) :=
  toAEEqFun_ofFun _ _

/-- The representative of `indicatorConst hs c` agrees with `s.indicator (fun _ ↦ c)` almost
everywhere. -/
theorem coeFn_indicatorConst [TopologicalSpace E] [Zero E] {s : Set Ω}
    (hs : NullMeasurableSet s μ) (c : E) :
    (indicatorConst hs c : Ω → E) =ᵐ[μ] s.indicator fun _ ↦ c :=
  coeFn_ofFun _ _

/-- The indicator of the empty set in `L0` is `0`. -/
@[simp]
theorem indicatorConst_empty [TopologicalSpace E] [Zero E]
    (hs : NullMeasurableSet (∅ : Set Ω) μ) (c : E) :
    indicatorConst hs c = 0 := by
  rw [indicatorConst_eq_ofFun, ofFun_eq_zero]
  simp [Pi.zero_def]

/-- The indicator with value `0` in `L0` is `0`. -/
@[simp]
theorem indicatorConst_zero [TopologicalSpace E] [Zero E] {s : Set Ω}
    (hs : NullMeasurableSet s μ) :
    indicatorConst hs (0 : E) = 0 := by
  rw [indicatorConst_eq_ofFun, ofFun_eq_zero]
  simp [Pi.zero_def]

/-- The indicator of `Set.univ` in `L0` is the constant class `const μ c`. -/
@[simp]
theorem indicatorConst_univ [TopologicalSpace E] [Zero E]
    (hs : NullMeasurableSet (Set.univ : Set Ω) μ) (c : E) :
    indicatorConst hs c = const μ c := by
  rw [indicatorConst_eq_ofFun, ← ofFun_const, ofFun_eq_ofFun]
  simp

/-- `indicatorConst` commutes with addition in the constant value. -/
theorem indicatorConst_add [TopologicalSpace E] [AddZeroClass E] [ContinuousAdd E] {s : Set Ω}
    (hs : NullMeasurableSet s μ) (c c' : E) :
    indicatorConst hs (c + c') = indicatorConst hs c + indicatorConst hs c' := by
  rw [indicatorConst_eq_ofFun, indicatorConst_eq_ofFun, indicatorConst_eq_ofFun, ofFun_add_ofFun,
    ofFun_eq_ofFun]
  exact Filter.EventuallyEq.of_eq (Set.indicator_add _ _ _)

/-- `indicatorConst` commutes with negation in the constant value. -/
theorem indicatorConst_neg [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] {s : Set Ω}
    (hs : NullMeasurableSet s μ) (c : E) :
    indicatorConst hs (-c) = -indicatorConst hs c := by
  rw [indicatorConst_eq_ofFun, indicatorConst_eq_ofFun, neg_ofFun, ofFun_eq_ofFun]
  exact Filter.EventuallyEq.of_eq (Set.indicator_neg _ _)

/-- `indicatorConst` commutes with subtraction in the constant value. -/
theorem indicatorConst_sub [TopologicalSpace E] [AddGroup E] [IsTopologicalAddGroup E] {s : Set Ω}
    (hs : NullMeasurableSet s μ) (c c' : E) :
    indicatorConst hs (c - c') = indicatorConst hs c - indicatorConst hs c' := by
  rw [indicatorConst_eq_ofFun, indicatorConst_eq_ofFun, indicatorConst_eq_ofFun, ofFun_sub_ofFun,
    ofFun_eq_ofFun]
  exact Filter.EventuallyEq.of_eq (Set.indicator_sub _ _ _)

/-- Scalar multiplication commutes with `indicatorConst`. -/
theorem smul_indicatorConst {𝕜 : Type*} [TopologicalSpace E] [Zero E] [SMulZeroClass 𝕜 E]
    [ContinuousConstSMul 𝕜 E] {s : Set Ω} (hs : NullMeasurableSet s μ) (a : 𝕜) (c : E) :
    a • indicatorConst hs c = indicatorConst hs (a • c) := by
  rw [indicatorConst_eq_ofFun, indicatorConst_eq_ofFun, smul_ofFun, ofFun_eq_ofFun]
  exact Filter.EventuallyEq.of_eq (Set.indicator_const_smul s a fun _ ↦ c).symm

/-- Including `indicatorConstLp` into `L0` gives `indicatorConst`. -/
@[simp]
theorem ofLp_indicatorConstLp [NormedAddCommGroup E] {p : ℝ≥0∞} {s : Set Ω}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E) :
    ofLp (indicatorConstLp p hs hμs c) = indicatorConst hs.nullMeasurableSet c := by
  refine ext ?_
  rw [coeFn_ofLp]
  exact (indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs) (c := c)).trans
    (coeFn_indicatorConst hs.nullMeasurableSet c).symm

/-- Closed-form `L⁰` distance from an indicator-constant class `indicatorConst hs c` to `0`:
`dist (indicatorConst hs c) 0 = μ.real s * (dist c 0 / (1 + dist c 0))`. -/
theorem dist_indicatorConst_zero [PseudoMetricSpace E] [Zero E] [IsFiniteMeasure μ] {s : Set Ω}
    (hs : NullMeasurableSet s μ) (c : E) :
    dist (indicatorConst hs c) 0 = μ.real s * (dist c 0 / (1 + dist c 0)) := by
  rw [indicatorConst_eq_ofFun, ← const_zero, ← ofFun_const, dist_ofFun]
  have hpt : (fun x ↦ dist (s.indicator (fun _ : Ω ↦ c) x) 0 /
      (1 + dist (s.indicator (fun _ : Ω ↦ c) x) 0)) =
      s.indicator (fun _ : Ω ↦ dist c 0 / (1 + dist c 0)) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hpt, integral_indicator₀ hs, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]

/-- The real measure of the support `{x | indicatorConst hs c x ≠ 0}` equals `μ.real s` whenever
`c ≠ 0`. -/
theorem measureReal_indicatorConst_ne_zero [TopologicalSpace E] [Zero E] {s : Set Ω}
    (hs : NullMeasurableSet s μ) {c : E} (hc : c ≠ 0) :
    μ.real {x | indicatorConst hs c x ≠ 0} = μ.real s := by
  refine measureReal_congr ?_
  filter_upwards [coeFn_indicatorConst hs c] with x hx
  rw [Set.mem_ofPred_eq, hx, Set.indicator_apply_ne_zero]
  simp [hc]

/-- For a unit-height real indicator `1_s`, `dist (indicatorConst hs 1) 0 = μ.real s / 2`, half of
the disagreement measure `μ.real {x | indicatorConst hs 1 x ≠ 0} = μ.real s`. -/
theorem dist_indicatorConst_one_zero [IsFiniteMeasure μ] {s : Set Ω}
    (hs : NullMeasurableSet s μ) :
    dist (indicatorConst hs (1 : ℝ)) 0 = μ.real s / 2 := by
  rw [dist_indicatorConst_zero hs (1 : ℝ)]
  norm_num
  ring

end TauCeti.L0
