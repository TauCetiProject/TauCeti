/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import Mathlib.MeasureTheory.Measure.AddContent

/-!
# Integration of simple functions against a real content

Let `ν` be a real-valued content on a ring of sets `C` that contains the measurable sets of `α`.
A real simple function `f` is integrated against `ν` by the finite sum
`∑ c ∈ f.range, ν (f ⁻¹' {c}) * c` (`MeasureTheory.AddContent.integralSimple`). Neither the sum
nor its properties involve countable additivity.

The sum is Mathlib's `MeasureTheory.SimpleFunc.setToSimpleFunc` for the set function
`s ↦ ν s • id`, taken with the zero measure: for it, `FinMeasAdditive` is finite additivity on
disjoint measurable sets, and every simple function is integrable. This gives linearity, the value
`c * ν s` at `c` times the indicator of a measurable set `s`, and, for nonnegative `ν`, the bound
`|∫ f dν| ≤ c * ν univ` whenever `|f| ≤ c`. If `ν` vanishes on the null sets of a measure `μ`,
the integral depends only on the `μ`-almost everywhere class of `f`.

These finite sums underlie the correspondences between positive linear functionals and
nonnegative contents in `TauCeti/Topology/ContinuousMap/Bounded/AddContent.lean` (bounded
functions on a discrete space, contents on all subsets) and
`TauCeti/MeasureTheory/Function/Lp/AddContent.lean` (`L∞`, contents on the measurable sets).

## Main definitions

* `MeasureTheory.AddContent.integralSimple`: the integral of real simple functions against a real
  content, as a linear map.

## Main results

* `MeasureTheory.AddContent.integralSimple_piecewise`: the integral of `c` times an indicator.
* `MeasureTheory.AddContent.abs_integralSimple_le`: for a nonnegative content, the integral is
  bounded by the total mass times a pointwise bound.
* `MeasureTheory.AddContent.integralSimple_congr_ae`: for a content vanishing on `μ`-null sets,
  the integral depends only on the `μ`-a.e. class.
-/

public section

noncomputable section

open Set

namespace MeasureTheory.AddContent

variable {α : Type*} [MeasurableSpace α] {C : Set (Set α)} (ν : AddContent ℝ C)
  (hC : IsSetRing C) (hCm : ∀ s, MeasurableSet s → s ∈ C)

include hC hCm in
private theorem finMeasAdditive_smul_id :
    FinMeasAdditive (0 : Measure α) fun s => ν s • ContinuousLinearMap.id ℝ ℝ := by
  intro s t hs ht _ _ hst
  simp [addContent_union hC (hCm s hs) (hCm t ht) hst, add_smul]

/-- The integral `∑ c ∈ f.range, ν (f ⁻¹' {c}) * c` of real simple functions `f` against a real
content `ν` on a ring of sets containing the measurable sets. -/
def integralSimple : SimpleFunc α ℝ →ₗ[ℝ] ℝ where
  toFun := SimpleFunc.setToSimpleFunc fun s => ν s • ContinuousLinearMap.id ℝ ℝ
  map_add' _ _ := SimpleFunc.setToSimpleFunc_add _ (finMeasAdditive_smul_id ν hC hCm)
    integrable_zero_measure integrable_zero_measure
  map_smul' c _ := SimpleFunc.setToSimpleFunc_smul_real _ (finMeasAdditive_smul_id ν hC hCm) c
    integrable_zero_measure

private theorem integralSimple_eq_setToSimpleFunc (f : SimpleFunc α ℝ) :
    ν.integralSimple hC hCm f =
      SimpleFunc.setToSimpleFunc (fun s => ν s • ContinuousLinearMap.id ℝ ℝ) f :=
  (rfl)

/-- The integral of a simple function against a content is the sum, over its values `c`, of `c`
times the content of the fiber over `c`. -/
theorem integralSimple_apply (f : SimpleFunc α ℝ) :
    ν.integralSimple hC hCm f = ∑ c ∈ f.range, ν (f ⁻¹' {c}) * c := by
  simp [integralSimple_eq_setToSimpleFunc, SimpleFunc.setToSimpleFunc]

/-- The integral of `c` times the indicator of a measurable set `s` is `c * ν s`. -/
theorem integralSimple_piecewise {s : Set α} (hs : MeasurableSet s) (c : ℝ) :
    ν.integralSimple hC hCm
      (SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0)) = c * ν s := by
  rw [integralSimple_eq_setToSimpleFunc, SimpleFunc.setToSimpleFunc_indicator _ (by simp)]
  simp [mul_comm]

variable {ν}

/-- Against a nonnegative content, a simple function bounded above by `c` has integral at most
`c * ν univ`. -/
theorem integralSimple_le (hν : ∀ s, MeasurableSet s → 0 ≤ ν s) {f : SimpleFunc α ℝ} {c : ℝ}
    (h : ∀ x, f x ≤ c) : ν.integralSimple hC hCm f ≤ c * ν univ := by
  have := SimpleFunc.setToSimpleFunc_mono (finMeasAdditive_smul_id ν hC hCm)
    (fun s hs _ x hx => by simpa using mul_nonneg (hν s hs) hx)
    integrable_zero_measure integrable_zero_measure
    ((SimpleFunc.coe_le_coe (f := f) (g := SimpleFunc.const α c)).1 fun x => by
      simpa using h x)
  rw [SimpleFunc.setToSimpleFunc_const _ (by simp)] at this
  simpa [integralSimple_eq_setToSimpleFunc, mul_comm] using this

/-- Against a nonnegative content, a simple function bounded in absolute value by `c` has
integral of absolute value at most `c * ν univ`. -/
theorem abs_integralSimple_le (hν : ∀ s, MeasurableSet s → 0 ≤ ν s) {f : SimpleFunc α ℝ}
    {c : ℝ} (h : ∀ x, |f x| ≤ c) : |ν.integralSimple hC hCm f| ≤ c * ν univ := by
  rw [abs_le]
  refine ⟨?_, integralSimple_le hC hCm hν fun x => (le_abs_self _).trans (h x)⟩
  have := integralSimple_le hC hCm hν (f := -f) fun x => (neg_le_abs _).trans (h x)
  rw [map_neg] at this
  linarith

/-- If a content vanishes on the measurable `μ`-null sets, the integral of a simple function
against it depends only on its `μ`-almost everywhere class. -/
theorem integralSimple_congr_ae {μ : Measure α}
    (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0) {f g : SimpleFunc α ℝ} (h : f =ᵐ[μ] g) :
    ν.integralSimple hC hCm f = ν.integralSimple hC hCm g := by
  refine SimpleFunc.setToSimpleFunc_congr' _ (finMeasAdditive_smul_id ν hC hCm)
    integrable_zero_measure integrable_zero_measure fun x y hxy => ?_
  have hnull : μ (f ⁻¹' {x} ∩ g ⁻¹' {y}) = 0 :=
    measure_mono_null (fun z hz => by
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff] at hz
      simpa [hz.1, hz.2] using hxy) (ae_iff.1 h)
  simp [hνμ _ ((SimpleFunc.measurableSet_fiber f x).inter (SimpleFunc.measurableSet_fiber g y))
    hnull]

end MeasureTheory.AddContent
