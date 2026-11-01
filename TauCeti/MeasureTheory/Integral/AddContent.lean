/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import Mathlib.MeasureTheory.Measure.AddContent

/-!
# Integrating simple functions against a finitely additive set function

Let `ν` be a real-valued finitely additive set function (`MeasureTheory.AddContent ℝ C`) defined
on a family of sets `C` containing every measurable set. A real simple function `f` is integrated
against `ν` by the finite sum

```text
∫ f dν = ∑_{c ∈ range f} ν {x | f x = c} * c.
```

This is Mathlib's `MeasureTheory.SimpleFunc.setToSimpleFunc` for the set function
`s ↦ ν s • id`, and it is linear in `f`. No countable additivity and no reference measure are
involved. When `ν` is nonnegative, the integral is monotone, and when `ν` vanishes on the
measurable null sets of a measure `μ`, it only depends on the `μ`-almost-everywhere class of `f`.

These finite sums are the first step in integrating bounded functions against a finitely additive
probability, for instance in the correspondence between means and finitely additive
probabilities on a discrete group, or between positive functionals on `L∞(μ)` and finitely
additive set functions vanishing on `μ`-null sets.

## Main definitions

* `MeasureTheory.AddContent.integralSimple ν hC`: the integral of real simple functions against
  `ν`, as a linear map.

## Main results

* `MeasureTheory.AddContent.integralSimple_piecewise_const`: the integral of `c` times the
  indicator of a measurable set `s` is `c * ν s`.
* `MeasureTheory.AddContent.integralSimple_mono`: the integral against a nonnegative `ν` is
  monotone.
* `MeasureTheory.AddContent.integralSimple_congr_ae`: if `ν` vanishes on measurable `μ`-null sets,
  then simple functions which agree `μ`-almost everywhere have the same integral.
-/

public section

noncomputable section

open Set

namespace MeasureTheory.AddContent

variable {α : Type*} [MeasurableSpace α] {C : Set (Set α)} (ν : AddContent ℝ C)
  (hC : ∀ s, MeasurableSet s → s ∈ C)

/-- The set function `s ↦ ν s • id` is finitely additive on measurable sets. We use the zero
measure for `FinMeasAdditive`: then every measurable set has finite measure, and every simple
function is integrable. -/
private theorem finMeasAdditive_smul_id (hC : ∀ s, MeasurableSet s → s ∈ C) :
    FinMeasAdditive (0 : Measure α) fun s => ν s • ContinuousLinearMap.id ℝ ℝ := by
  intro s t hs ht _ _ hst
  beta_reduce
  rw [addContent_union' (hC s hs) (hC t ht) (hC _ (hs.union ht)) hst, add_smul]

/-- The integral `∑_{c ∈ range f} ν {x | f x = c} * c` of a real simple function `f` against a
finitely additive set function `ν` defined on all measurable sets, as a linear map. -/
def integralSimple (hC : ∀ s, MeasurableSet s → s ∈ C) : SimpleFunc α ℝ →ₗ[ℝ] ℝ where
  toFun f := f.setToSimpleFunc fun s => ν s • ContinuousLinearMap.id ℝ ℝ
  map_add' _ _ := SimpleFunc.setToSimpleFunc_add _ (finMeasAdditive_smul_id ν hC)
    integrable_zero_measure integrable_zero_measure
  map_smul' c _ := SimpleFunc.setToSimpleFunc_smul_real _ (finMeasAdditive_smul_id ν hC) c
    integrable_zero_measure

theorem integralSimple_apply (f : SimpleFunc α ℝ) :
    ν.integralSimple hC f = ∑ c ∈ f.range, ν (f ⁻¹' {c}) * c :=
  (rfl)

/-- The integral of `c` times the indicator function of a measurable set `s` is `c * ν s`. -/
theorem integralSimple_piecewise_const {s : Set α} (hs : MeasurableSet s) (c : ℝ) :
    ν.integralSimple hC (SimpleFunc.piecewise s hs (SimpleFunc.const α c) (SimpleFunc.const α 0)) =
      c * ν s := by
  rw [integralSimple, LinearMap.coe_mk, AddHom.coe_mk,
    SimpleFunc.setToSimpleFunc_indicator _ (by simp), smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_comm]

/-- The integral of a constant function `c` is `c * ν univ`. -/
@[simp]
theorem integralSimple_const (c : ℝ) :
    ν.integralSimple hC (SimpleFunc.const α c) = c * ν univ := by
  rw [integralSimple, LinearMap.coe_mk, AddHom.coe_mk,
    SimpleFunc.setToSimpleFunc_const _ (by simp), smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, mul_comm]

variable {ν hC}

/-- The integral against a nonnegative finitely additive set function is monotone. -/
theorem integralSimple_mono (hν : ∀ s ∈ C, 0 ≤ ν s) {f g : SimpleFunc α ℝ} (hfg : f ≤ g) :
    ν.integralSimple hC f ≤ ν.integralSimple hC g :=
  SimpleFunc.setToSimpleFunc_mono (finMeasAdditive_smul_id ν hC)
    (fun s hs _ x hx => by simpa using mul_nonneg (hν s (hC s hs)) hx)
    integrable_zero_measure integrable_zero_measure hfg

/-- If `ν` vanishes on the measurable `μ`-null sets, the integral of a simple function only
depends on its `μ`-almost-everywhere class. -/
theorem integralSimple_congr_ae {μ : Measure α} (hνμ : ∀ s, MeasurableSet s → μ s = 0 → ν s = 0)
    {f g : SimpleFunc α ℝ} (hfg : f =ᵐ[μ] g) :
    ν.integralSimple hC f = ν.integralSimple hC g := by
  refine SimpleFunc.setToSimpleFunc_congr' _ (finMeasAdditive_smul_id ν hC)
    integrable_zero_measure integrable_zero_measure fun x y hxy => ?_
  have hs := (SimpleFunc.measurableSet_fiber f x).inter (SimpleFunc.measurableSet_fiber g y)
  beta_reduce
  rw [hνμ _ hs (measure_mono_null (fun z hz => ?_) (ae_iff.1 hfg)), zero_smul]
  exact fun h => hxy (hz.1.symm.trans (h.trans hz.2))

end MeasureTheory.AddContent
