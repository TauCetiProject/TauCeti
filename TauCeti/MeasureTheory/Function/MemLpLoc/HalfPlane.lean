/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.MeasureTheory.Function.MemLpLoc
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local `Lᵖ` classes on half-planes and half-discs

For an open planar set `Ω`, the relatively open subset `U = Ω ∩ {0 ≤ im}` of the closed upper
half-plane meets the real axis, which is Lebesgue null. A function is therefore locally `Lᵖ` on `U`
exactly when it is `Lᵖ` on the open upper half `W ∩ {0 < im}` of every open set `W` whose closure
is compact and contained in `Ω` (`TauCeti.memLpLoc_inter_setOf_im_nonneg_iff`).
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-- **Local `Lᵖ` on a half-disc through upper halves.** A function is locally `Lᵖ` on
`Ω ∩ {0 ≤ im}`, up to the real axis, exactly when it is `Lᵖ` on the upper half `W ∩ {0 < im}` of
every open `W` whose closure is compact and contained in `Ω`. The real axis is null, so the
compact sets reaching it see no more than these upper halves. -/
theorem memLpLoc_inter_setOf_im_nonneg_iff {p : ℝ≥0∞} {Ω : Opens ℂ}
    {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} :
    MemLpLoc p ((Ω : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) f ↔
      ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) → closure (W : Set ℂ) ⊆ Ω →
        MemLp f p (volume.restrict (W.upperHalf : Set ℂ)) := by
  refine ⟨fun hf W hWc hWΩ => ?_, fun h => memLpLoc_iff.2 fun K hKU hK => ?_⟩
  · have hK : IsCompact (closure (W : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im}) :=
      hWc.inter_right (isClosed_le continuous_const Complex.continuous_im)
    refine (memLpLoc_iff.1 hf _ (Set.inter_subset_inter_left _ hWΩ) hK).mono_measure
      (Measure.restrict_mono ?_ le_rfl)
    intro z hz
    obtain ⟨hzW, hz0⟩ := Opens.mem_upperHalf.1 hz
    exact ⟨subset_closure hzW, hz0.le⟩
  · obtain ⟨W, hWo, hKW, hWΩ, hWc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen
      (hKU.trans Set.inter_subset_left)
    refine (h ⟨W, hWo⟩ hWc hWΩ).mono_measure (Measure.restrict_mono_ae ?_)
    filter_upwards [(Complex.setOf_le_im_ae_eq 0).subset] with z hz hzK
    exact Opens.mem_upperHalf.2 ⟨hKW hzK, hz (hKU hzK).2⟩

end TauCeti
