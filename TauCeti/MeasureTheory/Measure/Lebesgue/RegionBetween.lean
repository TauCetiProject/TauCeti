/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Topology.Order.RegionBetween
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The volume of a closed region between two functions

Mathlib computes the volume of the open region `regionBetween f g s` between two measurable
functions as the Lebesgue integral of `g - f` over `s` (`volume_regionBetween_eq_lintegral'`).
This file gives the same formula for the closed region `TauCeti.closedRegionBetween f g s`, which
also contains the two graphs.

## Main results

* `TauCeti.measurableSet_closedRegionBetween`: the closed region between two measurable functions
  on a measurable set is measurable.
* `TauCeti.volume_closedRegionBetween_eq_lintegral`: its volume is `∫⁻ y in s, ofReal (g y - f y)`.
* `TauCeti.volume_closedRegionBetween_zero_sub_mul`: the trapezoid under `t ↦ a - k t` over
  `[0, b]` has area `a b - k b² / 2`.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {s : Set α}

/-- The closed region between two measurable functions on a measurable set is measurable. -/
theorem measurableSet_closedRegionBetween (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) : MeasurableSet (closedRegionBetween f g s) := by
  rw [show closedRegionBetween f g s = {p | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} from
    ext fun _ ↦ mem_closedRegionBetween]
  exact measurableSet_region_between_cc hf hg hs

/-- The volume of the closed region between two measurable functions on a measurable set is the
Lebesgue integral of their difference. This is the closed counterpart of
`volume_regionBetween_eq_lintegral'`. -/
theorem volume_closedRegionBetween_eq_lintegral (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    μ.prod volume (closedRegionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  rw [Measure.prod_apply (measurableSet_closedRegionBetween hf hg hs), ← lintegral_indicator hs]
  congr 1
  ext x
  by_cases hx : x ∈ s
  · have hpre : Prod.mk x ⁻¹' closedRegionBetween f g s = Icc (f x) (g x) := by
      ext t
      simp [hx]
    rw [hpre, Real.volume_Icc, indicator_of_mem hx, Pi.sub_apply]
  · have hpre : Prod.mk x ⁻¹' closedRegionBetween f g s = ∅ :=
      eq_empty_of_forall_notMem fun t ht ↦ hx (mem_closedRegionBetween.1 ht).1
    rw [hpre, measure_empty, indicator_of_notMem hx]

/-- **The area of a trapezoid.** For `0 ≤ a` and `k b ≤ a`, the closed region under
`t ↦ a - k t` over `[0, b]` has area `ENNReal.ofReal (a b - k b² / 2)`: this is `a b - k b² / 2`
when `0 ≤ b`, while for `b < 0` the region is empty and has area zero. -/
theorem volume_closedRegionBetween_zero_sub_mul {a b k : ℝ} (ha : 0 ≤ a) (hkb : k * b ≤ a) :
    volume (closedRegionBetween 0 (fun t ↦ a - k * t) (Icc 0 b)) =
      ENNReal.ofReal (a * b - k * b ^ 2 / 2) := by
  rw [Measure.volume_eq_prod,
    volume_closedRegionBetween_eq_lintegral measurable_zero (by fun_prop) measurableSet_Icc,
    sub_zero]
  rcases lt_or_ge b 0 with hb | hb
  · -- For `b < 0` the region is empty, and `a b - k b² / 2 ≤ a b / 2 ≤ 0`.
    rw [Icc_eq_empty_of_lt hb, Measure.restrict_empty, lintegral_zero_measure, eq_comm,
      ENNReal.ofReal_eq_zero]
    nlinarith
  have hpos : ∀ t ∈ Icc 0 b, 0 ≤ a - k * t := by
    rintro t ⟨ht₀, htb⟩
    rcases le_total 0 k with hk | hk
    · nlinarith
    · nlinarith
  have hint : ∫ t in (0)..b, (a - k * t) = a * b - k * b ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous fun t : ℝ ↦ k * t).intervalIntegrable 0 b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, integral_id]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous fun t : ℝ ↦ a - k * t).integrableOn_Icc)
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hpos)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb, hint]

end TauCeti
