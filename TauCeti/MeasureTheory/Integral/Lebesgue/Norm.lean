/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Squared triangle inequality and tail comparison for lower integrals

The lower Lebesgue integral of `‖f - g‖ₑ ^ 2` is at most twice the sum of the lower integrals of
`‖f - h‖ₑ ^ 2` and `‖g - h‖ₑ ^ 2`. Only the first of the two summands needs to be almost
everywhere measurable, and the integrals may be infinite.

## Main statements

* `TauCeti.lintegral_enorm_sub_sq_le_two_mul`: the squared triangle inequality through an
  intermediate function, integrated against an arbitrary measure.
* `TauCeti.tendsto_measure_le_lintegral_of_le_two_mul_add`: if
  `g k s x ≤ 2 * f₁ k s x + 2 * f₂ k s x` and the lower integrals of `f₁` and `f₂` tend to `0`
  in `ν`-measure, then so does the lower integral of `g`.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [SeminormedAddCommGroup E]

/-- **Squared triangle inequality for lower square energies.** The lower square energy of
`f - g` is at most twice the sum of those of `f - h` and `g - h`. -/
theorem lintegral_enorm_sub_sq_le_two_mul {f g h : α → E}
    (hfh : AEMeasurable (fun x ↦ ‖f x - h x‖ₑ ^ 2) μ) :
    ∫⁻ x, ‖f x - g x‖ₑ ^ 2 ∂μ ≤
      2 * ((∫⁻ x, ‖f x - h x‖ₑ ^ 2 ∂μ) + ∫⁻ x, ‖g x - h x‖ₑ ^ 2 ∂μ) := by
  rw [← lintegral_add_left' hfh, ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_mono fun x ↦ ?_
  have hx := ENNReal.ofReal_le_ofReal (norm_sub_sq_le_two_mul (f x) (g x) (h x))
  simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _),
    ofReal_norm, ENNReal.ofReal_ofNat] using hx

/-- If `g k s x ≤ 2 * f₁ k s x + 2 * f₂ k s x` pointwise with `f₁ k · x` almost everywhere
measurable, and both `∫⁻ s, f₁ k s x ∂μ` and `∫⁻ s, f₂ k s x ∂μ` converge to `0` in `ν`-measure,
then `∫⁻ s, g k s x ∂μ` also converges to `0` in `ν`-measure. -/
theorem tendsto_measure_le_lintegral_of_le_two_mul_add
    {ι β : Type*} [MeasurableSpace β] {ν : Measure β} {l : Filter ι}
    {f₁ f₂ g : ι → α → β → ℝ≥0∞}
    (hf₁ : ∀ k x, AEMeasurable (fun s ↦ f₁ k s x) μ)
    (hle : ∀ k s x, g k s x ≤ 2 * f₁ k s x + 2 * f₂ k s x)
    (h₁ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ ν {x | ε ≤ ∫⁻ s, f₁ k s x ∂μ}) l (𝓝 0))
    (h₂ : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ ν {x | ε ≤ ∫⁻ s, f₂ k s x ∂μ}) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ ν {x | ε ≤ ∫⁻ s, g k s x ∂μ}) l (𝓝 0) := by
  have hε4 : (0 : ℝ≥0∞) < ε / 4 := ENNReal.div_pos hε.ne' (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using (h₁ _ hε4).add (h₂ _ hε4)) (fun _ ↦ bot_le) fun k ↦
    (measure_mono fun x hx ↦ ?_).trans (measure_union_le _ _)
  have htri : ε ≤ 2 * (∫⁻ s, f₁ k s x ∂μ) + 2 * ∫⁻ s, f₂ k s x ∂μ :=
    hx.trans ((lintegral_mono (hle k · x)).trans (by
      rw [lintegral_add_left' ((hf₁ k x).const_mul 2),
        lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top,
        lintegral_const_mul' 2 _ ENNReal.ofNat_ne_top]))
  by_contra hnot
  obtain ⟨h1, h2⟩ := not_or.mp hnot
  simp only [Set.mem_ofPred_eq, not_le] at h1 h2
  have hlt := ENNReal.add_lt_add
    (ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top h1)
    (ENNReal.mul_lt_mul_right two_ne_zero ENNReal.ofNat_ne_top h2)
  have h4 : (2 : ℝ≥0∞) * (ε / 4) + 2 * (ε / 4) = ε := by
    calc (2 : ℝ≥0∞) * (ε / 4) + 2 * (ε / 4) = 4 * (ε / 4) := by ring
      _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  exact (h4 ▸ hlt).not_ge htri

end TauCeti
