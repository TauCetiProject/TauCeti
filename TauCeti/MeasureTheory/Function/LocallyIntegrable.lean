/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Separation.Regular

/-!
# Local integrability

Local integrability on an open set is equivalent to local integrability on every open subdomain
whose closure is compact and contained in the original set. This form is useful when a proof can be
localized to relatively compact subdomains.

For an additive Haar measure, local integrability is also preserved by translating a function onto
any set whose translate stays inside the original domain.

A function locally integrable on a null-measurable set `s`, vanishing almost everywhere on `s` off
a null-measurable compact `K ⊆ s`, is integrable on the whole space after extension by zero. This
is the step that turns a local hypothesis plus compact support into a global one. Both sets are
asked to be null-measurable explicitly because nothing here ties the topology on `X` to its
measurable space -- there is no `OpensMeasurableSpace` or `BorelSpace` assumption, so neither
compactness nor closedness of `K` carries any measurability with it. (Absent a separation axiom
`K` need not even be closed, but that is the lesser obstacle.)

## Main declarations

* `MeasureTheory.LocallyIntegrableOn.comp_add_right_of_mapsTo`: translation onto a smaller set
  preserves local integrability.
* `TauCeti.locallyIntegrableOn_iff_forall_isCompact_closure`: characterization by relatively
  compact open subdomains.
* `TauCeti.integrable_indicator_of_isCompact`: extension by zero of a function locally integrable
  on a null-measurable set, supported in a null-measurable compact subset of it, is integrable.

## Attribution

The characterization adapts Mathlib's `locallyIntegrableOn_iff` and
`LocallyIntegrableOn.integrableOn_compact_subset`, combined with
`exists_open_between_and_isCompact_closure` to reach relatively compact open subdomains.
-/

public section

open MeasureTheory Set TopologicalSpace

namespace MeasureTheory

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [BorelSpace E]
  [NormedAddCommGroup F] {mu : Measure E} [mu.IsAddHaarMeasure] {Omega V : Set E}
  {u : E → F} {h : E}

/-- Local integrability is preserved by a translation whose image stays in the original
domain. -/
theorem LocallyIntegrableOn.comp_add_right_of_mapsTo
    (hu : LocallyIntegrableOn u Omega mu) (hVO : MapsTo (· + h) V Omega) :
    LocallyIntegrableOn (fun x => u (x + h)) V mu := by
  intro x hx
  obtain ⟨s, hs, hus⟩ := hu (x + h) (hVO hx)
  refine ⟨(· + h) ⁻¹' s, ?_, ?_⟩
  · exact ((continuous_id.add continuous_const).continuousWithinAt.tendsto_nhdsWithin hVO) hs
  · simpa only [Function.comp_def] using
      ((measurePreserving_add_right mu h).integrableOn_comp_preimage
        (Homeomorph.addRight h).measurableEmbedding).2 hus

end MeasureTheory

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] {μ : Measure X}

section RelativelyCompactSubdomains

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] [PseudoMetrizableSpace ε]
  [LocallyCompactSpace X] [RegularSpace X] {f : X → ε} {Ω : Opens X}

/-- A function is locally integrable on an open set exactly when it is locally integrable on every
open subdomain with compact closure contained in that set. -/
theorem locallyIntegrableOn_iff_forall_isCompact_closure :
    LocallyIntegrableOn f Ω μ ↔
      ∀ V : Opens X, IsCompact (closure (V : Set X)) → closure (V : Set X) ⊆ Ω →
        LocallyIntegrableOn f V μ := by
  constructor
  · intro hf V _ hV
    exact hf.mono_set (subset_closure.trans hV)
  · intro h
    refine (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 ?_
    intro K hKΩ hK
    obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
      exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
    exact (h ⟨V, hVo⟩ hVc hVΩ).integrableOn_compact_subset hKV hK

end RelativelyCompactSubdomains

section ExtendByZero

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [PseudoMetrizableSpace ε]
  {f : X → ε} {s K : Set X}

/-- A function locally integrable on a null-measurable set `s` and vanishing almost everywhere on
`s` off a null-measurable compact `K ⊆ s` is, after extension by zero, integrable on the whole
space.

`K` carries its own null-measurability hypothesis rather than inheriting one from compactness:
no assumption here relates the topology on `X` to its measurable space, so a compact -- or even
closed -- set need not be measurable at all. -/
theorem integrable_indicator_of_isCompact (hs : NullMeasurableSet s μ) (hK : IsCompact K)
    (hKmeas : NullMeasurableSet K μ) (hKs : K ⊆ s) (hloc : LocallyIntegrableOn f s μ)
    (hf : ∀ᵐ x ∂μ.restrict s, x ∉ K → f x = 0) :
    Integrable (s.indicator f) μ := by
  have hae : s.indicator f =ᵐ[μ] K.indicator f := by
    filter_upwards [(ae_restrict_iff'₀ hs).1 hf] with x hx
    by_cases hxs : x ∈ s
    · by_cases hxK : x ∈ K
      · rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hxK]
      · rw [Set.indicator_of_mem hxs, Set.indicator_of_notMem hxK, hx hxs hxK]
    · rw [Set.indicator_of_notMem hxs, Set.indicator_of_notMem fun hxK => hxs (hKs hxK)]
  exact ((hloc.integrableOn_compact_subset hKs hK).integrable_indicator₀ hKmeas).congr hae.symm

end ExtendByZero

end TauCeti
