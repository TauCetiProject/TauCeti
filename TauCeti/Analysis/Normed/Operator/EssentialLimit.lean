/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Essential right limits through a bounded operator

Let `ι : V →L[𝕜] H` be a bounded operator, let `u : ℝ → V`, and let `w : ℝ → H` be continuous from
the right at `a` and agree with `ι ∘ u` at almost every time close to `a` on the right, that is,
along the filter `𝓝[>] a ⊓ ae volume` of essential right limits. This file shows that if `w a` is
not of the form `ι v`, then `u` cannot stay bounded near `a`, and cannot be modified on a null set
to become continuous from the right at `a`.

* `TauCeti.tendsto_norm_atTop_of_eventuallyEq_of_notMem_range`: for reflexive `V`,
  `‖u t‖ → ∞` along `𝓝[>] a ⊓ ae volume`. If `‖u t‖ ≤ M` frequently, then `w a`, a limit of
  values `ι (u t)`, lies in the image of the closed ball of radius `M`, which is closed by
  reflexivity (`ContinuousLinearMap.isClosed_image_closedBall`).
* `TauCeti.not_exists_continuousWithinAt_eventuallyEq_of_notMem_range`: without reflexivity, no
  `v : ℝ → V` continuous from the right at `a` agrees with `u` along `𝓝[>] a ⊓ ae volume`, since
  `ι ∘ u` would tend both to `ι (v a)` and to `w a` along this nontrivial filter.

These are the function-level facts behind the sharpness of the pivot space as the target of the
energy space of a Gelfand triple (`TauCeti.EvolutionSpace.tendsto_norm_value_atTop`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 3.
-/

public section

namespace TauCeti

open MeasureTheory Filter Set Topology NormedSpace Metric

variable {𝕜 V H : Type*} [RCLike 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] {ι : V →L[𝕜] H} {a : ℝ}

/-- **Blow-up at an initial value outside the range.** Let `ι : V →L[𝕜] H` be bounded, with `V`
reflexive, let `u : ℝ → V`, and let `w : ℝ → H` be continuous from the right at `a` and agree with
`ι ∘ u` at almost every time close to `a` on the right. If `w a` is not of the form `ι v`, then
`‖u t‖ → ∞` as `t → a⁺` outside a null set. -/
theorem tendsto_norm_atTop_of_eventuallyEq_of_notMem_range
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V)) {u : ℝ → V} {w : ℝ → H}
    (hw : ContinuousWithinAt w (Ioi a) a)
    (huw : ∀ᶠ t in 𝓝[>] a ⊓ ae volume, ι (u t) = w t) (ha : w a ∉ range ι) :
    Tendsto (fun t ↦ ‖u t‖) (𝓝[>] a ⊓ ae volume) atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  -- `w a` lies outside the closed set `ι '' closedBall 0 M`, and so does `w t` for `t` near `a`.
  have hwa : w a ∉ ι '' closedBall 0 M := fun h ↦ ha (image_subset_range _ _ h)
  filter_upwards [(hw.tendsto.mono_left inf_le_left).eventually
    ((ι.isClosed_image_closedBall hV 0 M).isOpen_compl.mem_nhds hwa), huw] with t ht hut
  exact le_of_not_gt fun hlt ↦ ht ⟨u t, mem_closedBall_zero_iff.2 hlt.le, hut⟩

/-- **No representative continuous at an initial value outside the range.** Let `ι : V →L[𝕜] H`
be bounded, let `u : ℝ → V`, and let `w : ℝ → H` be continuous from the right at `a` and agree with
`ι ∘ u` at almost every time close to `a` on the right. If `w a` is not of the form `ι v`, then no
function `v : ℝ → V` continuous from the right at `a` agrees with `u` at almost every time close to
`a` on the right. -/
theorem not_exists_continuousWithinAt_eventuallyEq_of_notMem_range {u : ℝ → V} {w : ℝ → H}
    (hw : ContinuousWithinAt w (Ioi a) a)
    (huw : ∀ᶠ t in 𝓝[>] a ⊓ ae volume, ι (u t) = w t) (ha : w a ∉ range ι) :
    ¬ ∃ v : ℝ → V, ContinuousWithinAt v (Ioi a) a ∧ u =ᶠ[𝓝[>] a ⊓ ae volume] v := by
  rintro ⟨v, hv, huv⟩
  have haClosure : a ∈ closure (Ioi a) := by
    rw [closure_Ioi]
    exact self_mem_Ici
  have := isOpen_Ioi.neBot_nhdsWithin_inf_ae (μ := volume) haClosure
  -- Along the nontrivial essential right filter, `ι ∘ u` tends to both `ι (v a)` and `w a`.
  have hv' : Tendsto (fun t ↦ ι (u t)) (𝓝[>] a ⊓ ae volume) (𝓝 (ι (v a))) :=
    (((ι.continuous.tendsto _).comp hv.tendsto).mono_left inf_le_left).congr'
      (huv.mono fun t ht ↦ by simp only [Function.comp_apply, ht])
  have hw' : Tendsto (fun t ↦ ι (u t)) (𝓝[>] a ⊓ ae volume) (𝓝 (w a)) :=
    (hw.tendsto.mono_left inf_le_left).congr' (huw.mono fun _ ht ↦ ht.symm)
  exact ha ⟨v a, tendsto_nhds_unique hv' hw'⟩

end TauCeti
