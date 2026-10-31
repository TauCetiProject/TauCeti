/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import Mathlib.MeasureTheory.Measure.AddContent

/-!
# Integrating simple functions against a finitely additive content

Let `ν` be a real content on a family `C` of sets containing every measurable set. A real simple
function `g` is integrated against `ν` by the finite sum

```text
∑ c ∈ g.range, c * ν {x | g x = c}.
```

This is linear in `g` because `ν` is additive on disjoint measurable sets. Its absolute value is at
most `ν univ` times any uniform bound of `g` when `ν` is nonnegative on measurable sets, and it only
depends on the almost-everywhere class of `g` when `ν` vanishes on null measurable sets. Neither
uses countable additivity.

The finite sums are Mathlib's `MeasureTheory.SimpleFunc.setToSimpleFunc`, taken with respect to
the zero measure: for it, `MeasureTheory.FinMeasAdditive` is plain finite additivity on disjoint
measurable sets, and every simple function is integrable.

This is the integral on simple functions underlying the correspondences between positive
functionals and contents, `PositiveLinearMap.addContentEquiv` for bounded functions on a discrete
space and `PositiveLinearMap.ofAddContentLpTop` for `L∞`.

## Main definitions

* `MeasureTheory.AddContent.integralSimple`: the integral of simple functions against a content,
  as a linear map.

## Main results

* `MeasureTheory.AddContent.integralSimple_piecewise`: the integral of `c` on `s` and `0` off `s`
  is `c * ν s`.
* `MeasureTheory.AddContent.eq_integralSimple`: a linear functional on simple functions with these
  values is the integral against `ν`.
* `MeasureTheory.AddContent.abs_integralSimple_le`: for nonnegative `ν`, the integral of a function
  bounded by `c` is at most `c * ν univ` in absolute value.
* `MeasureTheory.AddContent.integralSimple_congr_ae`: for `ν` vanishing on null sets, the integral
  only depends on the almost-everywhere class.
-/

public section

noncomputable section

open Set

namespace MeasureTheory.AddContent

variable {α : Type*} [MeasurableSpace α] {C : Set (Set α)} (ν : AddContent ℝ C)
  (hC : ∀ s, MeasurableSet s → s ∈ C)

/-- The set function `s ↦ ν s • id`, in the form used by `SimpleFunc.setToSimpleFunc`. -/
private def contentCLM (s : Set α) : ℝ →L[ℝ] ℝ :=
  ν s • ContinuousLinearMap.id ℝ ℝ

include hC in
private theorem finMeasAdditive_contentCLM :
    FinMeasAdditive (0 : Measure α) (contentCLM ν) := by
  intro s t hs ht _ _ hst
  simp [contentCLM, addContent_union' (hC s hs) (hC t ht) (hC _ (hs.union ht)) hst, add_smul]

/-- The integral of real simple functions against a real content `ν` on a family of sets
containing the measurable sets, `g ↦ ∑ c ∈ g.range, c * ν {x | g x = c}`. -/
def integralSimple : SimpleFunc α ℝ →ₗ[ℝ] ℝ where
  toFun := SimpleFunc.setToSimpleFunc (contentCLM ν)
  map_add' _ _ := SimpleFunc.setToSimpleFunc_add _ (finMeasAdditive_contentCLM ν hC)
    integrable_zero_measure integrable_zero_measure
  map_smul' c _ := SimpleFunc.setToSimpleFunc_smul_real _ (finMeasAdditive_contentCLM ν hC) c
    integrable_zero_measure

/-- The integral of a simple function `g` against `ν` is `∑ c ∈ g.range, c * ν (g ⁻¹' {c})`. -/
theorem integralSimple_apply (g : SimpleFunc α ℝ) :
    ν.integralSimple hC g = ∑ c ∈ g.range, c * ν (g ⁻¹' {c}) := by
  simp [integralSimple, SimpleFunc.setToSimpleFunc, contentCLM, mul_comm]

/-- The integral of the simple function equal to `c` on `s` and to `0` off `s` is `c * ν s`. -/
theorem integralSimple_piecewise {s : Set α} (hs : MeasurableSet s) (c : ℝ) :
    ν.integralSimple hC (SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0)) =
      c * ν s := by
  change SimpleFunc.setToSimpleFunc (contentCLM ν) _ = _
  rw [SimpleFunc.setToSimpleFunc_indicator _ (by simp [contentCLM])]
  simp [contentCLM, mul_comm]

/-- A linear functional on simple functions taking the value `c * ν s` at the simple function equal
to `c` on `s` and to `0` off `s` is the integral against `ν`. -/
theorem eq_integralSimple {L : SimpleFunc α ℝ →ₗ[ℝ] ℝ}
    (h : ∀ s (hs : MeasurableSet s) (c : ℝ),
      L (SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0)) = c * ν s) :
    L = ν.integralSimple hC := by
  ext g
  induction g using SimpleFunc.induction with
  | const c hs => rw [h, integralSimple_piecewise]
  | add _ hf hg => simp_all

variable {ν}

/-- For `ν` nonnegative on measurable sets, the integral of a simple function bounded above by `c`
is at most `c * ν univ`. -/
theorem integralSimple_le (hν : ∀ s, MeasurableSet s → 0 ≤ ν s) {g : SimpleFunc α ℝ} {c : ℝ}
    (h : ∀ x, g x ≤ c) : ν.integralSimple hC g ≤ c * ν univ := by
  have := SimpleFunc.setToSimpleFunc_mono (finMeasAdditive_contentCLM ν hC)
    (fun s hs _ x hx => by simpa [contentCLM] using mul_nonneg (hν s hs) hx)
    integrable_zero_measure integrable_zero_measure
    ((SimpleFunc.coe_le_coe (f := g) (g := SimpleFunc.const α c)).1 fun x => by
      simpa using h x)
  rw [SimpleFunc.setToSimpleFunc_const _ (by simp [contentCLM])] at this
  simpa [integralSimple, contentCLM, mul_comm] using this

/-- For `ν` nonnegative on measurable sets, the integral of a simple function bounded by `c` in
absolute value is at most `c * ν univ` in absolute value. -/
theorem abs_integralSimple_le (hν : ∀ s, MeasurableSet s → 0 ≤ ν s) {g : SimpleFunc α ℝ} {c : ℝ}
    (h : ∀ x, |g x| ≤ c) : |ν.integralSimple hC g| ≤ c * ν univ := by
  refine abs_le.2 ⟨?_, integralSimple_le hC hν fun x => le_of_abs_le (h x)⟩
  have := integralSimple_le hC hν (g := -g) (c := c) fun x => by
    simpa using (neg_le_abs (g x)).trans (h x)
  rw [map_neg] at this
  linarith

/-- For `ν` vanishing on `μ`-null measurable sets, the integral of a simple function against `ν`
only depends on its `μ`-almost-everywhere class. -/
theorem integralSimple_congr_ae {μ : Measure α}
    (hnull : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0) {g g' : SimpleFunc α ℝ}
    (h : g =ᵐ[μ] g') : ν.integralSimple hC g = ν.integralSimple hC g' := by
  refine SimpleFunc.setToSimpleFunc_congr' _ (finMeasAdditive_contentCLM ν hC)
    integrable_zero_measure integrable_zero_measure fun x y hxy => ?_
  have hmeas := (SimpleFunc.measurableSet_fiber g x).inter (SimpleFunc.measurableSet_fiber g' y)
  -- The set where `g = x` and `g' = y` lies in the null set where `g ≠ g'`.
  have hnull' : μ (g ⁻¹' {x} ∩ g' ⁻¹' {y}) = 0 :=
    measure_mono_null (fun z hz => by simp_all) (ae_iff.1 h)
  simp [contentCLM, hnull _ hmeas hnull']

end MeasureTheory.AddContent
