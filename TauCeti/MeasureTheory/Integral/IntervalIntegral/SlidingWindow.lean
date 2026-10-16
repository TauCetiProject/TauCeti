/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Integrating sliding-window integrals on the line

For `f : ℝ → ℝ≥0∞` and `h : ℝ`, integrating the window integrals `∫⁻ r in Ioc t (t + h), f r`
over all `t` gives `ENNReal.ofReal h * ∫⁻ r, f r`. For `0 ≤ h` this is Tonelli's theorem: the
windows `Ioc t (t + h)` of length `h` cover each point of the line for a set of `t` of length `h`;
for `h < 0` the windows are empty and both sides vanish. Restricted to the starting points
`t ∈ Ioc a (b - h)`, whose windows lie in `Ioc a b`, this bounds the integrated window integrals by
`ENNReal.ofReal h * ∫⁻ r in Ioc a b, f r`.

This is the averaging step that turns pointwise bounds of a difference quotient over a window of
length `h > 0` by `h⁻¹ * ∫⁻ r in Ioc t (t + h), f r` into a bound of its integral by `∫⁻ f`.

## Main results

* `TauCeti.lintegral_setLIntegral_Ioc_add`:
  `∫⁻ t, ∫⁻ r in Ioc t (t + h), f r = ENNReal.ofReal h * ∫⁻ r, f r`.
* `TauCeti.setLIntegral_setLIntegral_Ioc_add_le`: the windows starting in `Ioc a (b - h)` give at
  most `ENNReal.ofReal h * ∫⁻ r in Ioc a b, f r`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- Integrating the integrals of `f` over the sliding windows `Ioc t (t + h)` over all starting
points `t` gives `ENNReal.ofReal h` times the integral of `f`: for `0 ≤ h` this is `h` times the
integral, and for `h < 0` the windows are empty and both sides vanish. -/
theorem lintegral_setLIntegral_Ioc_add {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f) (h : ℝ) :
    ∫⁻ t, ∫⁻ r in Ioc t (t + h), f r = ENNReal.ofReal h * ∫⁻ r, f r := by
  set g := hf.mk f
  have hg : Measurable g := hf.measurable_mk
  have hwindow (t : ℝ) : ∫⁻ r in Ioc t (t + h), f r = ∫⁻ r, (Ioc t (t + h)).indicator g r := by
    rw [lintegral_indicator measurableSet_Ioc]
    exact lintegral_congr_ae (ae_restrict_of_ae hf.ae_eq_mk)
  -- The window `Ioc t (t + h)` contains `r` exactly when `t ∈ Ico (r - h) r`.
  have hswap (t r : ℝ) :
      (Ioc t (t + h)).indicator g r = (Ico (r - h) r).indicator (fun _ ↦ g r) t := by
    simp only [indicator, mem_Ioc, mem_Ico]
    grind
  have hmeas : Measurable (Function.uncurry fun t r ↦ (Ioc t (t + h)).indicator g r) := by
    have hS : MeasurableSet {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 ≤ q.1 + h} :=
      (measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.add_const h))
    convert (hg.comp measurable_snd).indicator hS using 1
    ext ⟨t, r⟩
    simp [indicator, mem_Ioc]
  simp_rw [hwindow]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  simp_rw [hswap, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, sub_sub_cancel]
  rw [lintegral_mul_const _ hg, mul_comm, lintegral_congr_ae hf.ae_eq_mk]

/-- Integrating the integrals of `f` over the sliding windows `Ioc t (t + h)` that lie in
`Ioc a b`, that is over the starting points `t ∈ Ioc a (b - h)`, gives at most `ENNReal.ofReal h`
times the integral of `f` over `Ioc a b`. -/
theorem setLIntegral_setLIntegral_Ioc_add_le {f : ℝ → ℝ≥0∞} {a b : ℝ}
    (hf : AEMeasurable f (volume.restrict (Ioc a b))) (h : ℝ) :
    ∫⁻ t in Ioc a (b - h), ∫⁻ r in Ioc t (t + h), f r ≤
      ENNReal.ofReal h * ∫⁻ r in Ioc a b, f r := by
  -- Inside `Ioc a b`, `f` agrees with its extension by zero, to which the global identity applies.
  have hwindow : ∀ t ∈ Ioc a (b - h),
      ∫⁻ r in Ioc t (t + h), f r = ∫⁻ r in Ioc t (t + h), (Ioc a b).indicator f r :=
    fun t ht ↦ setLIntegral_congr_fun measurableSet_Ioc fun r hr ↦
      (indicator_of_mem (show r ∈ Ioc a b from ⟨ht.1.trans hr.1, by linarith [hr.2, ht.2]⟩)
        f).symm
  calc ∫⁻ t in Ioc a (b - h), ∫⁻ r in Ioc t (t + h), f r
      = ∫⁻ t in Ioc a (b - h), ∫⁻ r in Ioc t (t + h), (Ioc a b).indicator f r :=
        setLIntegral_congr_fun measurableSet_Ioc hwindow
    _ ≤ ∫⁻ t, ∫⁻ r in Ioc t (t + h), (Ioc a b).indicator f r := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal h * ∫⁻ r in Ioc a b, f r := by
      rw [lintegral_setLIntegral_Ioc_add ((aemeasurable_indicator_iff measurableSet_Ioc).2 hf),
        lintegral_indicator measurableSet_Ioc]

end TauCeti
