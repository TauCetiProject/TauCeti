/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Topology.Sequences

/-!
# Claims determined by dense observations

For a process with almost surely continuous paths, observing a dense set of times determines
all observation-measurable real or complex claims up to almost-everywhere equality. The sample
space need not be a continuous-path space, and the observation sigma algebra need not contain
the ambient null sets. The conclusion uses almost-everywhere strong measurability, not literal
measurability of an arbitrary raw version.

The proof reconstructs the process from sequential limits of dense observations and uses
Mathlib's measurable factorization theorem. This permits finite-observation approximation on
the original probability space, without identifying that space with a path space.
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

namespace TauCeti

/-- Dense observations of an almost surely continuous process determine every claim that is
almost surely measurable from the full process. No completeness of the observation field or
of the sample measure is required. -/
theorem aestronglyMeasurable_of_dense_observations
    {Ω ι Y E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m : MeasurableSpace Ω}
    [TopologicalSpace ι] [FirstCountableTopology ι]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [IsCompletelyMetrizableSpace Y] [Nonempty Y]
    [TopologicalSpace E] [IsCompletelyMetrizableSpace E] [Nonempty E]
    {X : ι → Ω → Y} {D : Set ι} (hD : Dense D)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hm : ∀ t ∈ D, StronglyMeasurable[m] (X t))
    {f : Ω → E}
    (hf : AEStronglyMeasurable[MeasurableSpace.comap (fun ω t ↦ X t ω) inferInstance] f P) :
    AEStronglyMeasurable[m] f P := by
  classical
  have hseq (t : ι) := mem_closure_iff_seq_limit.mp (hD t)
  choose u hu hlim using hseq
  let Z : ι → Ω → Y := fun t ω ↦ limUnder atTop (fun n ↦ X (u t n) ω)
  have hZ (t : ι) : StronglyMeasurable[m] (Z t) :=
    StronglyMeasurable.limUnder (fun n ↦ hm (u t n) (hu t n))
  have heq : (fun ω t ↦ X t ω) =ᵐ[P] (fun ω t ↦ Z t ω) := by
    filter_upwards [hc] with ω hω
    apply funext
    intro t
    simpa only [Z, Function.comp_def] using
      ((hω.tendsto t).comp (hlim t)).limUnder_eq.symm
  obtain ⟨g, hg, hgf⟩ := hf.stronglyMeasurable_mk.exists_eq_measurable_comp
  refine ⟨fun ω ↦ g (fun t ↦ Z t ω),
    hg.comp_measurable (Measurable.of_eval fun t ↦ (hZ t).measurable), ?_⟩
  filter_upwards [hf.ae_eq_mk, heq] with ω hfω hω
  rw [hfω, hgf, Function.comp_apply, hω]

end TauCeti
