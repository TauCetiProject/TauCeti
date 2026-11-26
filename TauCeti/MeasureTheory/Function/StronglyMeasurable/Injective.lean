/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.FiniteSupport

/-!
# Recovering strong measurability through injective operators

A continuous injection from a Polish space into a metrizable space detects strong
measurability and almost everywhere strong measurability. The inverse need not be continuous:
Mathlib's Lusin–Souslin theorem `Continuous.measurableEmbedding` supplies its measurability.

For a continuous linear operator, it suffices that the operator be injective on a complete
separable supporting subspace. The subspace need contain the function's values only almost
everywhere. The finite-support versions hold for arbitrary measures, because injectivity on
the supporting subspace also detects zeros. Neither ambient space needs to be separable or
complete.

## References

* Hytönen, van Neerven, Veraar and Weis, *Analysis in Banach Spaces*, Volume I,
  Example 1.1.26, pp. 11–12.
-/

public section

open MeasureTheory Set TopologicalSpace

section Polish

variable {α E F : Type*} [MeasurableSpace α] [TopologicalSpace E] [PolishSpace E]
  [TopologicalSpace F] [MetrizableSpace F] {g : E → F} {f : α → E} {μ : Measure α}

/-- A continuous injection from a Polish space detects strong measurability. -/
theorem Continuous.stronglyMeasurable_comp_iff_of_injective (hg : Continuous g)
    (hinj : Function.Injective g) : StronglyMeasurable (g ∘ f) ↔ StronglyMeasurable f := by
  borelize E F
  refine ⟨fun h ↦ ?_, hg.comp_stronglyMeasurable⟩
  exact ((hg.measurableEmbedding hinj).measurable_comp_iff.1 h.measurable).stronglyMeasurable

/-- A continuous injection from a Polish space detects a.e. strong measurability. -/
theorem Continuous.aestronglyMeasurable_comp_iff_of_injective (hg : Continuous g)
    (hinj : Function.Injective g) :
    AEStronglyMeasurable (g ∘ f) μ ↔ AEStronglyMeasurable f μ := by
  borelize E F
  refine ⟨fun h ↦ ?_, hg.comp_aestronglyMeasurable⟩
  exact ((hg.measurableEmbedding hinj).aemeasurable_comp_iff.1 h.aemeasurable).aestronglyMeasurable

end Polish

namespace ContinuousLinearMap

variable {α 𝕜 X Y : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {μ : Measure α} {f : α → X}

/-- An operator injective on a complete separable subspace containing the range of `f`
detects strong measurability. Completeness is required only of the supporting subspace. -/
theorem stronglyMeasurable_comp_iff_of_injOn (T : X →L[𝕜] Y) (E : Submodule 𝕜 X)
    [CompleteSpace E] [SeparableSpace E] (hinj : Set.InjOn T E)
    (hf : ∀ s, f s ∈ E) : StronglyMeasurable (T ∘ f) ↔ StronglyMeasurable f := by
  let g : α → E := fun s ↦ ⟨f s, hf s⟩
  have hT : Function.Injective (T.comp E.subtypeL) := fun x y h ↦
    Subtype.ext (hinj x.property y.property h)
  refine ⟨fun h ↦ ?_, T.continuous.comp_stronglyMeasurable⟩
  have hg : StronglyMeasurable g :=
    ((T.comp E.subtypeL).continuous.stronglyMeasurable_comp_iff_of_injective hT).1 h
  exact continuous_subtypeVal.comp_stronglyMeasurable hg

/-- An operator injective on a complete separable subspace containing the values of `f`
almost everywhere detects a.e. strong measurability. -/
theorem aestronglyMeasurable_comp_iff_of_injOn (T : X →L[𝕜] Y) (E : Submodule 𝕜 X)
    [CompleteSpace E] [SeparableSpace E] (hinj : Set.InjOn T E)
    (hf : ∀ᵐ s ∂μ, f s ∈ E) :
    AEStronglyMeasurable (T ∘ f) μ ↔ AEStronglyMeasurable f μ := by
  classical
  let g : α → E := fun s ↦ if h : f s ∈ E then ⟨f s, h⟩ else 0
  have hfg : (fun s ↦ (g s : X)) =ᵐ[μ] f := by
    filter_upwards [hf] with s hs
    simp [g, hs]
  have hT : Function.Injective (T.comp E.subtypeL) := fun x y h ↦
    Subtype.ext (hinj x.property y.property h)
  refine ⟨fun h ↦ ?_, T.continuous.comp_aestronglyMeasurable⟩
  have hg : AEStronglyMeasurable g μ :=
    ((T.comp E.subtypeL).continuous.aestronglyMeasurable_comp_iff_of_injective hT).1
      (h.congr (hfg.fun_comp T).symm)
  exact (continuous_subtypeVal.comp_aestronglyMeasurable hg).congr hfg

/-- An operator injective on a complete separable supporting subspace detects finite strong
measurability, without a sigma-finiteness assumption on the measure. -/
theorem finStronglyMeasurable_comp_iff_of_injOn (T : X →L[𝕜] Y) (E : Submodule 𝕜 X)
    [CompleteSpace E] [SeparableSpace E] (hinj : Set.InjOn T E)
    (hf : ∀ s, f s ∈ E) :
    FinStronglyMeasurable (T ∘ f) μ ↔ FinStronglyMeasurable f μ := by
  have hzero (s : α) : T (f s) = 0 ↔ f s = 0 := by
    constructor
    · intro h
      exact hinj (hf s) E.zero_mem (h.trans T.map_zero.symm)
    · intro h
      simp [h]
  simp only [finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite,
    T.stronglyMeasurable_comp_iff_of_injOn E hinj hf, Function.comp_apply, hzero]

/-- An operator injective on a complete separable subspace containing the values of `f`
almost everywhere detects a.e. finite strong measurability for arbitrary measures. -/
theorem aefinStronglyMeasurable_comp_iff_of_injOn (T : X →L[𝕜] Y) (E : Submodule 𝕜 X)
    [CompleteSpace E] [SeparableSpace E] (hinj : Set.InjOn T E)
    (hf : ∀ᵐ s ∂μ, f s ∈ E) :
    AEFinStronglyMeasurable (T ∘ f) μ ↔ AEFinStronglyMeasurable f μ := by
  have hzero (s : Set α) : (T ∘ f) =ᵐ[μ.restrict sᶜ] 0 ↔ f =ᵐ[μ.restrict sᶜ] 0 := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · filter_upwards [ae_restrict_of_ae hf, h] with x hx hTx
      exact hinj hx E.zero_mem (hTx.trans T.map_zero.symm)
    · filter_upwards [h] with x hx
      simp [hx]
  simp only [TauCeti.aefinStronglyMeasurable_iff_aestronglyMeasurable_and_exists_set_sigmaFinite,
    T.aestronglyMeasurable_comp_iff_of_injOn E hinj hf, hzero]

end ContinuousLinearMap
