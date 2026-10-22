/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of parametric and weighted integrals

Mathlib's `continuousOn_integral_of_compact_support` gives continuity of a parametric integral on
a set. This file records its global form: a jointly continuous integrand which vanishes unless the
integration variable lies in a fixed compact set has a continuous parametric integral, against any
measure which is finite on compact sets. It also records that the indicator function of a
bounded interval `[a, b)` is integrable against a locally finite measure.

Pairing with a bounded scalar multiplier supported in a set is continuous for the `L¹` distance
on that set; the domain needs only a measurable space.

## Main statements

* `TauCeti.continuous_integral_of_compact_support`: the parametric integral of a jointly
  continuous integrand which vanishes unless `r ∈ K`, for compact `K`, is continuous.
* `TauCeti.integrable_indicator_Ico_one`: the indicator function of `[a, b)` is integrable.
* `TauCeti.tendsto_integral_smul_of_tendsto_lintegral_enorm_sub`: bounded scalar pairings
  preserve `L¹` convergence on a set containing the multiplier's support.
-/

public section

open MeasureTheory Function Set Filter
open scoped ENNReal Topology

namespace TauCeti

/-- The parametric integral `s ↦ ∫ r, F s r` of a jointly continuous integrand which vanishes
unless `r ∈ K`, for compact `K`, is continuous. -/
theorem continuous_integral_of_compact_support {X Y E : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : X → Y → E} {K : Set Y} (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (hK : IsCompact K) (hFc : Continuous (uncurry F)) (hF : ∀ s r, F s r ≠ 0 → r ∈ K) :
    Continuous fun s => ∫ r, F s r ∂μ :=
  continuousOn_univ.mp <| continuousOn_integral_of_compact_support hK hFc.continuousOn
    fun s r _ hr => by_contra fun h => hr (hF s r h)

/-- The indicator function of a bounded interval `[a, b)` is integrable against a locally finite
measure. -/
theorem integrable_indicator_Ico_one {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [LinearOrder α] [OrderClosedTopology α] [OpensMeasurableSpace α] [CompactIccSpace α]
    {μ : Measure α} [IsLocallyFiniteMeasure μ] (a b : α) :
    Integrable ((Ico a b).indicator (1 : α → ℝ)) μ :=
  (integrableOn_const measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico

/-- Pairing with a bounded scalar multiplier supported in `s` preserves `L¹(s)` convergence.
The approximating pairings need only be eventually integrable, and the limiting pairing
needs only to be almost everywhere strongly measurable. -/
theorem tendsto_integral_smul_of_tendsto_lintegral_enorm_sub {α 𝕜 F ι : Type*}
    [MeasurableSpace α] [NormedField 𝕜] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace 𝕜 F] {μ : Measure α} {s : Set α} {l : Filter ι}
    {c : α → 𝕜} {K : ℝ}
    (hK : ∀ x, ‖c x‖ ≤ K) (hcsupp : ∀ x ∉ s, c x = 0)
    {a : ι → α → F} {b : α → F} (ha : ∀ᶠ i in l, Integrable (fun x => c x • a i x) μ)
    (hb : AEStronglyMeasurable (fun x => c x • b x) μ)
    (hab : Tendsto (fun i => ∫⁻ x in s, ‖a i x - b x‖ₑ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, c x • a i x ∂μ) l (𝓝 (∫ x, c x • b x ∂μ)) := by
  refine tendsto_integral_of_L1 (fun x => c x • b x) hb ha ?_
  have hlim : Tendsto (fun i => ENNReal.ofReal K * ∫⁻ x in s, ‖a i x - b x‖ₑ ∂μ) l
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K) hab
      (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) fun i => ?_
  have hsupp : Function.support (fun x => ‖c x • (a i x - b x)‖ₑ) ⊆ s := by
    intro x hx
    by_contra hxs
    exact hx (by simp [hcsupp x hxs])
  calc ∫⁻ x, ‖c x • a i x - c x • b x‖ₑ ∂μ
      = ∫⁻ x, ‖c x • (a i x - b x)‖ₑ ∂μ := by
        congr with x
        rw [smul_sub]
    _ = ∫⁻ x in s, ‖c x • (a i x - b x)‖ₑ ∂μ :=
        (setLIntegral_eq_of_support_subset hsupp).symm
    _ ≤ ∫⁻ x in s, ENNReal.ofReal K * ‖a i x - b x‖ₑ ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [enorm_smul]
        gcongr
        simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hK x)
    _ = ENNReal.ofReal K * ∫⁻ x in s, ‖a i x - b x‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end TauCeti
