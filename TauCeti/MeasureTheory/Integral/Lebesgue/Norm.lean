/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Data.ENNReal.Inv

/-!
# Squared triangle inequality for lower square energies

The lower Lebesgue integral of `‖f - g‖ₑ ^ 2` is at most twice the sum of the lower integrals of
`‖f - h‖ₑ ^ 2` and `‖g - h‖ₑ ^ 2`. Only the first of the two summands needs to be almost
everywhere measurable, and the integrals may be infinite.

Consequently, if two families of functions converge in section square energy in measure to a
common target, their differences converge in section square energy in measure to zero.

## Main statements

* `TauCeti.lintegral_enorm_sub_sq_le_two_mul`: the squared triangle inequality through an
  intermediate function, integrated against an arbitrary measure.
* `TauCeti.tendsto_measure_le_lintegral_enorm_sub_sq`: convergence in section square energy in
  measure to a common target transfers to differences.
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

/-- If two families `K` and `L` converge in section square energy in `ν`-measure to a common
target `H`, then the section square energies of `K - L` converge to zero in `ν`-measure. Only
sectionwise almost-everywhere measurability of the `K - H` square errors is required. -/
theorem tendsto_measure_le_lintegral_enorm_sub_sq {β ι : Type*} [MeasurableSpace β]
    {ν : Measure β} {l : Filter ι} {K L : ι → α → β → E} {H : α → β → E}
    (hmeas : ∀ᶠ k in l, ∀ y, AEMeasurable (fun x ↦ ‖K k x y - H x y‖ₑ ^ 2) μ)
    (hKH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ ν {y | ε ≤ ∫⁻ x, ‖K k x y - H x y‖ₑ ^ 2 ∂μ})
      l (𝓝 0))
    (hLH : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ ν {y | ε ≤ ∫⁻ x, ‖L k x y - H x y‖ₑ ^ 2 ∂μ})
      l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ ν {y | ε ≤ ∫⁻ x, ‖K k x y - L k x y‖ₑ ^ 2 ∂μ}) l (𝓝 0) := by
  set η := ε / (2 * 2)
  have hη : 0 < η := ENNReal.div_pos hε.ne' (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [add_zero] using (hKH η hη).add (hLH η hη))
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hmeas] with k hk
  refine (measure_mono fun y hy ↦ ?_).trans (measure_union_le _ _)
  exact ENNReal.div_two_mul_le_or_div_two_mul_le_of_le_mul_add
    (hy.trans (lintegral_enorm_sub_sq_le_two_mul (hk y)))

end TauCeti
