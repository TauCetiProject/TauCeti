/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import TauCeti.Analysis.Sobolev.EvolutionSpace.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Initial values outside the energy space force blow-up

Let `ι : V →L[𝕜] H` be a bounded operator from a reflexive normed space, such as the inclusion
`V ↪ H` of a Gelfand triple. An element `u` of the energy space
`TauCeti.EvolutionSpace ι a b = L²(a, b; V) ∩ H¹(a, b; V*)` has a representative continuous on
`[a, b]` with values in `H` (`TauCeti.EvolutionSpace.toContinuousMap`), but its values `u(t)` lie in
`V` only for almost every `t`. This file shows that the continuity into `H` cannot be improved to
continuity into `V` in general: if the initial value `u(a) ∈ H` is not of the form `ι v`, then

`‖u(t)‖_V → ∞` as `t → a⁺`, essentially,

that is, along the filter `𝓝[>] a ⊓ ae volume` of times close to `a` on the right outside a null
set (`TauCeti.EvolutionSpace.tendsto_norm_value_atTop`). In particular `u` has no representative
with values in `V` that is continuous from the right at `a`
(`TauCeti.EvolutionSpace.not_exists_continuousWithinAt_ae_eq`).

The argument does not use the equation: it needs only a function `u : ℝ → V` and a representative
`w` of `ι ∘ u` continuous from the right at `a`
(`TauCeti.tendsto_norm_atTop_of_eventuallyEq_of_notMem_range`). If `‖u(tₙ)‖ ≤ M` along times
`tₙ → a⁺` with `ι (u tₙ) = w tₙ`, then `w a = lim ι (u tₙ)` lies in the image of the closed ball
of radius `M`, which is closed by reflexivity (`ContinuousLinearMap.isClosed_image_closedBall`), so
`w a` lies in the range of `ι`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.9.2, Theorem 3 (the embedding of the
  energy space into `C([0, T]; L²)`).
-/

public section

namespace TauCeti

open MeasureTheory Filter Set Topology NormedSpace Metric

section Function

variable {𝕜 V H : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
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
  by_contra hM
  have hfreq : ∃ᶠ t in 𝓝[>] a ⊓ ae volume, ‖u t‖ ≤ M ∧ ι (u t) = w t :=
    ((not_eventually.1 hM).and_eventually huw).mono fun t ht ↦ ⟨(not_le.1 ht.1).le, ht.2⟩
  -- Times `tₙ ∈ (a, a + 1 / (n + 1))` at which `‖u tₙ‖ ≤ M` and `ι (u tₙ) = w tₙ`.
  have hseq (n : ℕ) : ∃ t ∈ Ioo a (a + 1 / (n + 1)), ‖u t‖ ≤ M ∧ ι (u t) = w t :=
    frequently_iff.1 hfreq (mem_inf_of_left (Ioo_mem_nhdsGT (lt_add_of_pos_right a
      Nat.one_div_pos_of_nat)))
  choose t ht hut using hseq
  have hta : Tendsto t atTop (𝓝[>] a) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n ↦ (ht n).1⟩
    have hupper : Tendsto (fun n : ℕ ↦ a + 1 / ((n : ℝ) + 1)) atTop (𝓝 a) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add a
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun n ↦ (ht n).1.le) fun n ↦ (ht n).2.le
  have hmem : w a ∈ ι '' closedBall 0 M :=
    (ι.isClosed_image_closedBall hV 0 M).mem_of_tendsto (hw.tendsto.comp hta)
      (Eventually.of_forall fun n ↦ ⟨u (t n), mem_closedBall_zero_iff.2 (hut n).1, (hut n).2⟩)
  exact ha (image_subset_range _ _ hmem)

/-- **No representative continuous at an initial value outside the range.** Under the hypotheses of
`TauCeti.tendsto_norm_atTop_of_eventuallyEq_of_notMem_range`, no function `v : ℝ → V` continuous
from the right at `a` agrees with `u` at almost every time close to `a` on the right. -/
theorem not_exists_continuousWithinAt_eventuallyEq_of_notMem_range
    (hV : Function.Surjective (inclusionInDoubleDual 𝕜 V)) {u : ℝ → V} {w : ℝ → H}
    (hw : ContinuousWithinAt w (Ioi a) a)
    (huw : ∀ᶠ t in 𝓝[>] a ⊓ ae volume, ι (u t) = w t) (ha : w a ∉ range ι) :
    ¬ ∃ v : ℝ → V, ContinuousWithinAt v (Ioi a) a ∧ u =ᶠ[𝓝[>] a ⊓ ae volume] v := by
  rintro ⟨v, hv, huv⟩
  have := isOpen_Ioi.neBot_nhdsWithin_inf_ae (μ := volume)
    (show a ∈ closure (Ioi a) by rw [closure_Ioi]; exact self_mem_Ici)
  have hbdd : ∀ᶠ t in 𝓝[>] a ⊓ ae volume, ‖u t‖ < ‖v a‖ + 1 :=
    ((hv.norm.tendsto.eventually (gt_mem_nhds (lt_add_one ‖v a‖))).filter_mono inf_le_left).and
      huv |>.mono fun t ht ↦ ht.2 ▸ ht.1
  obtain ⟨t, hgt, hlt⟩ := ((tendsto_norm_atTop_of_eventuallyEq_of_notMem_range hV hw huw
    ha).eventually (eventually_ge_atTop (‖v a‖ + 1))).and hbdd |>.exists
  exact hgt.not_gt hlt

end Function

namespace EvolutionSpace

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι : V →L[ℝ] H} {a b : ℝ}

/-- Almost every time close to `a` on the right is almost every time in `(a, b)`. -/
private theorem nhdsGT_inf_ae_le_ae_restrict_Ioo (hab : a < b) :
    𝓝[>] a ⊓ ae volume ≤ ae (volume.restrict (Ioo a b)) := by
  rw [ae_restrict_eq measurableSet_Ioo]
  exact le_inf inf_le_right (inf_le_left.trans (le_principal_iff.2 (Ioo_mem_nhdsGT hab)))

/-- **Blow-up in the energy space.** Let `V` be reflexive and let `u` be an element of the energy
space `L²(a, b; V) ∩ H¹(a, b; V*)` whose initial value `u(a) ∈ H`, the value at `a` of its
continuous representative, is not of the form `ι v`. Then `‖u(t)‖_V → ∞` as `t → a⁺`, outside a
null set. -/
theorem tendsto_norm_value_atTop (hV : Function.Surjective (inclusionInDoubleDual ℝ V))
    (hab : a < b) (u : EvolutionSpace ι a b)
    (hu : toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ ∉ range ι) :
    Tendsto (fun t ↦ ‖value u t‖) (𝓝[>] a ⊓ ae volume) atTop :=
  tendsto_norm_atTop_of_eventuallyEq_of_notMem_range hV
    ((toContinuousMap hab u).continuous.comp continuous_projIcc).continuousWithinAt
    ((value_ae_eq_toContinuousMap hab u).filter_mono (nhdsGT_inf_ae_le_ae_restrict_Ioo hab))
    (by simpa only [Function.comp_apply, projIcc_left])

/-- **The energy space is not contained in `C([a, b]; V)`.** Let `V` be reflexive and let `u` be an
element of the energy space whose initial value `u(a) ∈ H` is not of the form `ι v`. Then `u` has
no representative with values in `V` that is continuous from the right at `a`, let alone one
continuous on `[a, b]`. -/
theorem not_exists_continuousWithinAt_ae_eq (hV : Function.Surjective (inclusionInDoubleDual ℝ V))
    (hab : a < b) (u : EvolutionSpace ι a b)
    (hu : toContinuousMap hab u ⟨a, left_mem_Icc.2 hab.le⟩ ∉ range ι) :
    ¬ ∃ v : ℝ → V, ContinuousWithinAt v (Ioi a) a ∧
      value u =ᵐ[volume.restrict (Ioo a b)] v := fun ⟨v, hv, huv⟩ ↦
  not_exists_continuousWithinAt_eventuallyEq_of_notMem_range hV
    ((toContinuousMap hab u).continuous.comp continuous_projIcc).continuousWithinAt
    ((value_ae_eq_toContinuousMap hab u).filter_mono (nhdsGT_inf_ae_le_ae_restrict_Ioo hab))
    (by simpa only [Function.comp_apply, projIcc_left])
    ⟨v, hv, huv.filter_mono (nhdsGT_inf_ae_le_ae_restrict_Ioo hab)⟩

end EvolutionSpace

end TauCeti
