/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import Mathlib.MeasureTheory.Measure.AddContent

/-!
# Integrating simple functions against a content

Let `ν` be a real-valued content on a family of sets `C` that contains every measurable set. A
real simple function `g` is integrated against `ν` by the finite sum

```text
∫ g dν = ∑ c ∈ range g, c * ν {x | g x = c}.
```

This is linear in `g`, takes the value `c * ν s` at `c` times the indicator of a measurable set
`s`, and, when `ν` is nonnegative on measurable sets, is bounded by `c * ν univ` for `g ≤ c`.
When `ν` vanishes on the measurable null sets of a measure `μ`, it only depends on the
`μ`-almost-everywhere class of `g`. Only finite additivity of `ν` is used.

The sum is Mathlib's `MeasureTheory.SimpleFunc.setToSimpleFunc` for the set function
`s ↦ ν s • id`, which is `FinMeasAdditive` for the zero measure: for it, `FinMeasAdditive` is plain
finite additivity on disjoint measurable sets, and every function is integrable.

This is the first step in extending a finitely additive set function to a positive functional on
a space of bounded functions, by continuity from the dense subspace of simple functions.

## Main definitions

* `MeasureTheory.SimpleFunc.integralAddContent ν hC`: integration of real simple functions against
  a real content `ν`, as a linear map.
-/

public section

noncomputable section

open Set Filter

namespace MeasureTheory.SimpleFunc

variable {α : Type*} [MeasurableSpace α] {C : Set (Set α)}

/-- The set function `s ↦ ν s • id`, in the form used by `SimpleFunc.setToSimpleFunc`. -/
private def contentCLM (ν : AddContent ℝ C) (s : Set α) : ℝ →L[ℝ] ℝ :=
  ν s • ContinuousLinearMap.id ℝ ℝ

private theorem finMeasAdditive_contentCLM (ν : AddContent ℝ C)
    (hC : ∀ s, MeasurableSet s → s ∈ C) : FinMeasAdditive (0 : Measure α) (contentCLM ν) := by
  intro s t hs ht _ _ hst
  simp [contentCLM, addContent_union' (hC s hs) (hC t ht) (hC _ (hs.union ht)) hst, add_smul]

/-- The integral `∑ c ∈ range g, c * ν {x | g x = c}` of a real simple function `g` against a
real content `ν` on a family of sets containing the measurable sets. -/
def integralAddContent (ν : AddContent ℝ C) (hC : ∀ s, MeasurableSet s → s ∈ C) :
    SimpleFunc α ℝ →ₗ[ℝ] ℝ where
  toFun := setToSimpleFunc (contentCLM ν)
  map_add' _ _ := setToSimpleFunc_add _ (finMeasAdditive_contentCLM ν hC)
    integrable_zero_measure integrable_zero_measure
  map_smul' c _ := setToSimpleFunc_smul_real _ (finMeasAdditive_contentCLM ν hC) c
    integrable_zero_measure

variable {ν : AddContent ℝ C} {hC : ∀ s, MeasurableSet s → s ∈ C}

private theorem integralAddContent_eq_setToSimpleFunc (g : SimpleFunc α ℝ) :
    integralAddContent ν hC g = setToSimpleFunc (contentCLM ν) g :=
  (rfl)

/-- The integral of a simple function against a content is the sum over its values `c` of `c`
times the content of the fiber of `c`. -/
theorem integralAddContent_apply (g : SimpleFunc α ℝ) :
    integralAddContent ν hC g = ∑ c ∈ g.range, c * ν (g ⁻¹' {c}) := by
  simp [integralAddContent_eq_setToSimpleFunc, setToSimpleFunc, contentCLM, mul_comm]

/-- The integral of `c` times the indicator of a measurable set `s` is `c * ν s`. -/
theorem integralAddContent_piecewise_const {s : Set α} (hs : MeasurableSet s) (c : ℝ) :
    integralAddContent ν hC (piecewise s hs (const α c) (const α 0)) = c * ν s := by
  rw [integralAddContent_eq_setToSimpleFunc,
    setToSimpleFunc_indicator _ (by simp [contentCLM])]
  simp [contentCLM, mul_comm]

/-- Against a content which is nonnegative on measurable sets, a simple function bounded above by
`c` has integral at most `c * ν univ`. -/
theorem integralAddContent_le (hν : ∀ s, MeasurableSet s → 0 ≤ ν s) {g : SimpleFunc α ℝ} {c : ℝ}
    (h : ∀ x, g x ≤ c) : integralAddContent ν hC g ≤ c * ν univ := by
  have := setToSimpleFunc_mono (finMeasAdditive_contentCLM ν hC)
    (fun s hs _ x hx => by simpa [contentCLM] using mul_nonneg (hν s hs) hx)
    integrable_zero_measure integrable_zero_measure
    ((coe_le_coe (f := g) (g := const α c)).1 fun x => by simpa using h x)
  rw [setToSimpleFunc_const _ (by simp [contentCLM])] at this
  simpa [integralAddContent_eq_setToSimpleFunc, contentCLM, mul_comm] using this

/-- Against a content which vanishes on the measurable `μ`-null sets, the integral of a simple
function only depends on its `μ`-almost-everywhere class. -/
theorem integralAddContent_congr {μ : Measure α}
    (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0) {f g : SimpleFunc α ℝ} (h : f =ᵐ[μ] g) :
    integralAddContent ν hC f = integralAddContent ν hC g := by
  refine setToSimpleFunc_congr' _ (finMeasAdditive_contentCLM ν hC)
    integrable_zero_measure integrable_zero_measure fun x y hxy => ?_
  have hm := (measurableSet_fiber f x).inter (measurableSet_fiber g y)
  have hnull : μ (f ⁻¹' {x} ∩ g ⁻¹' {y}) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (ae_iff.1 h)
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at hz
    simp only [mem_ofPred_eq, hz.1, hz.2]
    exact hxy
  simp [contentCLM, hνμ _ hm hnull]

end MeasureTheory.SimpleFunc
