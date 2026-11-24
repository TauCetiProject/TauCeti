/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable

/-!
# Almost everywhere strong measurability across null augmentation

Adjoining ambient null sets to a σ-algebra preserves almost everywhere strong measurability
for completely metrizable targets. The original σ-algebra need not be related to the measure's
ambient σ-algebra. Representatives are selected through piecewise combinations and limits;
complete metrizability ensures that the limit representative is measurable.
-/

public section

open MeasureTheory Filter TopologicalSpace
open scoped Topology

namespace TauCeti.MeasureTheory

/-- Adjoining ambient null sets to an arbitrary σ-algebra does not change almost everywhere
strong measurability for a completely metrizable target. No inclusion between the original
σ-algebra and the measure's ambient σ-algebra is required. -/
@[simp]
theorem aestronglyMeasurable_eventuallyMeasurableSpace_iff {Ω β : Type*}
    {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} [TopologicalSpace β]
    [IsCompletelyMetrizableSpace β] {f : Ω → β} :
    AEStronglyMeasurable[eventuallyMeasurableSpace m (ae μ)] f μ ↔
      AEStronglyMeasurable[m] f μ := by
  classical
  refine ⟨?_, fun hf ↦ hf.mono le_eventuallyMeasurableSpace⟩
  rintro ⟨g, hg, hfg⟩
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · exact StronglyMeasurable.of_subsingleton_dom.aestronglyMeasurable
  have : Nonempty β := hΩ.map f
  have hgm : ∀ (g : Ω → β), StronglyMeasurable[eventuallyMeasurableSpace m (ae μ)] g →
      AEStronglyMeasurable[m] g μ := by
    intro g hg
    induction g, hg using StronglyMeasurable.induction' with
    | const c => exact stronglyMeasurable_const.aestronglyMeasurable
    | @pcw f g s _ _ hs ihf ihg =>
      obtain ⟨t, ht, hst⟩ := hs
      refine ⟨t.piecewise (ihf.mk f) (ihg.mk g),
        ihf.stronglyMeasurable_mk.piecewise ht ihg.stronglyMeasurable_mk, ?_⟩
      filter_upwards [hst, ihf.ae_eq_mk, ihg.ae_eq_mk] with ω hω hfω hgω
      simp only [Set.piecewise, ← hω, hfω, hgω]
    | @lim f g _ _ ih hlim =>
      let : MeasurableSpace Ω := m
      refine ⟨fun ω ↦ limUnder atTop (fun n ↦ (ih n).mk (f n) ω),
        StronglyMeasurable.limUnder (fun n ↦ (ih n).stronglyMeasurable_mk), ?_⟩
      filter_upwards [ae_all_iff.2 (fun n ↦ (ih n).ae_eq_mk)] with ω hω
      have hlim' := hlim ω
      simp only [hω] at hlim'
      exact hlim'.limUnder_eq.symm
  exact (hgm g hg).congr hfg.symm

end TauCeti.MeasureTheory
