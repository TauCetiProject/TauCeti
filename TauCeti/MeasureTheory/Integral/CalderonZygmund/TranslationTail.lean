/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Analysis.Normed.Group.BallSphere

/-!
# Hörmander's condition from the integrable tail of a kernel

Let `f` be a function on a seminormed additive group with a right-invariant measure, integrable
on `{‖x‖ > r}`. Since `x ↦ x - h` maps `{‖x‖ > s}` into `{‖x‖ > r}` whenever `r + ‖h‖ ≤ s`,

`∫_{‖x‖ > s} ‖f (x - h) - f x‖ dx ≤ 2 ∫_{‖x‖ > r} ‖f x‖ dx`.

With `r = ‖h‖` and `s = 2 ‖h‖` this is the crude form of Hörmander's condition for the convolution
kernel `f`, used at the scales where its tail is small: in the proof of the Mihlin–Hörmander
multiplier theorem it handles the Littlewood–Paley pieces of frequency `2 ^ j > ‖h‖⁻¹`.

## Main declarations

* `MeasureTheory.IntegrableOn.setIntegral_norm_comp_sub_le`: the translate of `f` on
  `{‖x‖ > s}` is controlled by the tail of `f` on `{‖x‖ > r}`.
* `MeasureTheory.IntegrableOn.setIntegral_norm_comp_sub_sub_le`: Hörmander's condition bounded by
  twice the tail.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 6.2 (proof of Theorem 6.2.7).
-/

public section

namespace MeasureTheory.IntegrableOn

variable {G E : Type*} [SeminormedAddGroup G] {h : G} {r s : ℝ} [MeasurableSpace G]
  [MeasurableAdd G] [NormedAddCommGroup E] {μ : Measure G} [μ.IsAddRightInvariant] {f : G → E}

/-- If `f` is integrable on `{‖x‖ > r}` and `r + ‖h‖ ≤ s`, the integral of `‖f (x - h)‖` over
`{‖x‖ > s}` is at most that of `‖f x‖` over `{‖x‖ > r}`. -/
theorem setIntegral_norm_comp_sub_le (hf : IntegrableOn f {x | r < ‖x‖} μ) (hrs : r + ‖h‖ ≤ s) :
    ∫ x in {x | s < ‖x‖}, ‖f (x - h)‖ ∂μ ≤ ∫ x in {x | r < ‖x‖}, ‖f x‖ ∂μ := by
  rw [← (measurePreserving_sub_right μ h).setIntegral_image_emb
    (MeasurableEquiv.subRight h).measurableEmbedding (‖f ·‖)]
  exact setIntegral_mono_set hf.norm (.of_forall fun _ ↦ norm_nonneg _)
    (.of_forall (TauCeti.image_sub_const_setOf_lt_norm_subset hrs))

/-- **Hörmander's condition from the tail of the kernel.** If `r + ‖h‖ ≤ s`, then on `{‖x‖ > s}`
the difference `f (x - h) - f x` is controlled by twice the tail of `f` on `{‖x‖ > r}`. The
classical case is `r = ‖h‖` and `s = 2 * ‖h‖`. -/
theorem setIntegral_norm_comp_sub_sub_le (hf : IntegrableOn f {x | r < ‖x‖} μ)
    (hrs : r + ‖h‖ ≤ s) :
    ∫ x in {x | s < ‖x‖}, ‖f (x - h) - f x‖ ∂μ ≤ 2 * ∫ x in {x | r < ‖x‖}, ‖f x‖ ∂μ := by
  have hsr : {x : G | s < ‖x‖} ⊆ {x | r < ‖x‖} := fun x (hx : s < ‖x‖) ↦
    lt_of_le_of_lt (by linarith [norm_nonneg h]) hx
  have hf₁ : IntegrableOn (fun x ↦ f (x - h)) {x | s < ‖x‖} μ :=
    ((measurePreserving_sub_right μ h).integrableOn_image
      (MeasurableEquiv.subRight h).measurableEmbedding).1
        (hf.mono_set (TauCeti.image_sub_const_setOf_lt_norm_subset hrs))
  have hf₂ : IntegrableOn f {x | s < ‖x‖} μ := hf.mono_set hsr
  calc ∫ x in {x | s < ‖x‖}, ‖f (x - h) - f x‖ ∂μ
      ≤ ∫ x in {x | s < ‖x‖}, (‖f (x - h)‖ + ‖f x‖) ∂μ :=
        setIntegral_mono (hf₁.sub hf₂).norm (hf₁.norm.add hf₂.norm) fun x ↦ norm_sub_le _ _
    _ = (∫ x in {x | s < ‖x‖}, ‖f (x - h)‖ ∂μ) + ∫ x in {x | s < ‖x‖}, ‖f x‖ ∂μ :=
        integral_add hf₁.norm hf₂.norm
    _ ≤ (∫ x in {x | r < ‖x‖}, ‖f x‖ ∂μ) + ∫ x in {x | r < ‖x‖}, ‖f x‖ ∂μ := by
        gcongr ?_ + ?_
        · exact hf.setIntegral_norm_comp_sub_le hrs
        · exact setIntegral_mono_set hf.norm (.of_forall fun _ ↦ norm_nonneg _) (.of_forall hsr)
    _ = 2 * ∫ x in {x | r < ‖x‖}, ‖f x‖ ∂μ := (two_mul _).symm

end MeasureTheory.IntegrableOn
