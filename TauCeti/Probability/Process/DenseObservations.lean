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

For a process indexed by a first-countable space `ι` with almost surely continuous paths into
a completely metrizable Borel space `Y`, observing a dense set `D` of times determines all
observation-measurable claims valued in any completely metrizable space `E`, up to
almost-everywhere equality. The observations at times in `D` must be strongly measurable for
the chosen observation sigma algebra. The sample space need not be a continuous-path space,
and the observation sigma algebra need not contain the ambient null sets. The conclusion uses
almost-everywhere strong measurability, not literal measurability of an arbitrary raw version.

The proof reconstructs the process from sequential limits of dense observations and uses
Mathlib's measurable factorization theorem. This permits finite-observation approximation on
the original probability space, without identifying that space with a path space.
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

namespace TauCeti

/-- For a first-countable index space `ι` and completely metrizable spaces `Y` and `E`, with
`Y` carrying its Borel sigma algebra, dense observations of an almost surely continuous
process determine every `E`-valued claim almost surely strongly measurable from the full
process. Each observation `X t` for `t ∈ D` must be `m`-strongly measurable. No completeness of
the observation field or of the sample measure is required. -/
theorem aestronglyMeasurable_of_dense_of_aestronglyMeasurable_comap
    {Ω ι Y E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {m : MeasurableSpace Ω}
    [TopologicalSpace ι] [FirstCountableTopology ι]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [IsCompletelyMetrizableSpace Y]
    [TopologicalSpace E] [IsCompletelyMetrizableSpace E]
    {X : ι → Ω → Y} {D : Set ι} (hD : Dense D)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω))
    (hm : ∀ t ∈ D, StronglyMeasurable[m] (X t))
    {f : Ω → E}
    (hf : AEStronglyMeasurable[MeasurableSpace.comap (fun ω t ↦ X t ω) inferInstance] f P) :
    AEStronglyMeasurable[m] f P := by
  classical
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · exact AEStronglyMeasurable.of_subsingleton_dom
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨t₀⟩⟩
  · exact hf.mono (by rw [MeasurableSpace.comap_process_pi]; simp)
  have : Nonempty Y := ⟨X t₀ ω₀⟩
  have : Nonempty E := ⟨f ω₀⟩
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
