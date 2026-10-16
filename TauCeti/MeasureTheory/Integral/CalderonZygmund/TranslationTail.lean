/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Hörmander's condition from the tail of an integrable kernel

For an integrable function `f` on a normed additive group with a right-invariant measure,
translating by `h` maps `{‖x‖ > 2 ‖h‖}` into `{‖x‖ > ‖h‖}`, so

`∫_{‖x‖ > 2 ‖h‖} ‖f (x - h) - f x‖ dx ≤ 2 ∫_{‖x‖ > ‖h‖} ‖f x‖ dx`.

This is the crude form of Hörmander's condition for the convolution kernel `f`, used at the scales
where its tail is small: in the proof of the Mihlin–Hörmander multiplier theorem it handles the
Littlewood–Paley pieces of frequency `2 ^ j > ‖h‖⁻¹`.

## Main declarations

* `MeasureTheory.Integrable.setIntegral_norm_comp_sub_le`: the translate of `f` on
  `{‖x‖ > 2 ‖h‖}` is controlled by the tail of `f` on `{‖x‖ > ‖h‖}`.
* `MeasureTheory.Integrable.setIntegral_norm_comp_sub_sub_le`: Hörmander's condition bounded by
  twice the tail.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 6.2 (proof of Theorem 6.2.7).
-/

public section

namespace MeasureTheory.Integrable

variable {G E : Type*} [NormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] {μ : Measure G} [μ.IsAddRightInvariant] {f : G → E}

/-- Translating by `h` maps `{‖x‖ > 2 ‖h‖}` into `{‖x‖ > ‖h‖}`, so the integral of `‖f (x - h)‖`
over the first set is at most that of `‖f x‖` over the second. -/
theorem setIntegral_norm_comp_sub_le (hf : Integrable f μ) (h : G) :
    ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f (x - h)‖ ∂μ ≤ ∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ := by
  have hS : MeasurableSet {x : G | 2 * ‖h‖ < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hT : MeasurableSet {x : G | ‖h‖ < ‖x‖} := measurableSet_lt measurable_const measurable_norm
  rw [← integral_indicator hS, ← integral_indicator hT,
    ← integral_sub_right_eq_self (fun x ↦ {x : G | ‖h‖ < ‖x‖}.indicator (‖f ·‖) x) h]
  refine integral_mono ((hf.comp_sub_right h).norm.indicator hS)
    ((hf.norm.indicator hT).comp_sub_right h) fun x ↦ ?_
  by_cases hx : x ∈ {x : G | 2 * ‖h‖ < ‖x‖}
  · have hx' : x - h ∈ {x : G | ‖h‖ < ‖x‖} := by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      linarith [norm_sub_norm_le x h]
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
  · rw [Set.indicator_of_notMem hx]
    exact Set.indicator_nonneg (fun _ _ ↦ norm_nonneg _) _

/-- **Hörmander's condition from the tail of the kernel.** On `{‖x‖ > 2 ‖h‖}`, the difference
`f (x - h) - f x` is controlled by twice the tail of `f` on `{‖x‖ > ‖h‖}`. -/
theorem setIntegral_norm_comp_sub_sub_le (hf : Integrable f μ) (h : G) :
    ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f (x - h) - f x‖ ∂μ ≤
      2 * ∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ := by
  have hST : {x : G | 2 * ‖h‖ < ‖x‖} ⊆ {x | ‖h‖ < ‖x‖} :=
    Set.ofPred_subset_ofPred.2 fun x hx ↦ by linarith [norm_nonneg h]
  calc ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f (x - h) - f x‖ ∂μ
      ≤ ∫ x in {x | 2 * ‖h‖ < ‖x‖}, (‖f (x - h)‖ + ‖f x‖) ∂μ :=
        setIntegral_mono ((hf.comp_sub_right h).sub hf).norm.integrableOn
          ((hf.comp_sub_right h).norm.add hf.norm).integrableOn fun x ↦ norm_sub_le _ _
    _ = (∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f (x - h)‖ ∂μ) + ∫ x in {x | 2 * ‖h‖ < ‖x‖}, ‖f x‖ ∂μ :=
        integral_add (hf.comp_sub_right h).norm.integrableOn hf.norm.integrableOn
    _ ≤ (∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ) + ∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ := by
        gcongr ?_ + ?_
        · exact hf.setIntegral_norm_comp_sub_le h
        · exact setIntegral_mono_set hf.norm.integrableOn (.of_forall fun _ ↦ norm_nonneg _)
            (.of_forall hST)
    _ = 2 * ∫ x in {x | ‖h‖ < ‖x‖}, ‖f x‖ ∂μ := by ring

end MeasureTheory.Integrable
