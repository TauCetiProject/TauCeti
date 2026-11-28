/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.StronglyMeasurable.ScalarTests
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import TauCeti.Analysis.Normed.Operator.Norming

/-!
# Almost everywhere Pettis measurability

Scalar a.e. measurability and an essentially separable range characterize a.e. strong
measurability. On a complete separable supporting subspace, any separating family of
continuous linear functionals suffices. Each scalar test may have its own exceptional null
set. The full-dual criterion requires no completeness of the target or supporting subspace.

The proofs apply the pointwise Pettis criteria to the null-measurable σ-algebra and then
use Mathlib's `aestronglyMeasurable_iff_nullMeasurable_separable` to return to the original
measure space.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, §1.1.b, Theorem 1.1.20 and Corollaries 1.1.21–1.1.25.
-/

public section

open MeasureTheory Set TopologicalSpace

namespace TauCeti

section Uniqueness

variable {𝕜 X S : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [MeasurableSpace S] {μ : Measure S}

/-- Scalar a.e. equality against a separating family implies vector a.e. equality on a
common separable supporting subspace. Neither strong measurability nor completeness is
needed: essential separability permits a common exceptional set for countably many tests. -/
theorem ae_eq_of_separating_tests {E : Submodule 𝕜 X} [SeparableSpace E]
    {Y : Set (StrongDual 𝕜 X)} (hsep : ∀ x ∈ E, (∀ x' ∈ Y, x' x = 0) → x = 0)
    {f g : S → X} (hf : ∀ᵐ s ∂μ, f s ∈ E) (hg : ∀ᵐ s ∂μ, g s ∈ E)
    (htest : ∀ x' ∈ Y, (fun s ↦ x' (f s)) =ᵐ[μ] fun s ↦ x' (g s)) :
    f =ᵐ[μ] g := by
  let T := (fun x' : StrongDual 𝕜 X ↦ x'.comp E.subtypeL) '' Y
  have hT : ∀ x : E, (∀ x' ∈ T, x' x = 0) → x = 0 := by
    intro x hx
    apply Submodule.coe_eq_zero.1
    exact hsep x x.property fun x' hx' ↦ hx _ (mem_image_of_mem _ hx')
  obtain ⟨T₀, hT₀T, hT₀c, hT₀⟩ := exists_countable_separating_subset hT
  have : Countable T₀ := hT₀c.to_subtype
  choose y hyY hy using fun z : T₀ ↦ hT₀T z.property
  filter_upwards [hf, hg, ae_all_iff.2
    (fun z : T₀ ↦ htest (y z) (hyY z))] with s hs ht heq
  apply sub_eq_zero.1
  apply (Submodule.coe_eq_zero (x := (⟨f s - g s, E.sub_mem hs ht⟩ : E))).2
  apply hT₀
  intro z hz
  have hz' : (y ⟨z, hz⟩).comp E.subtypeL = z := hy ⟨z, hz⟩
  rw [← hz']
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, map_sub,
    sub_eq_zero] using heq ⟨z, hz⟩

end Uniqueness

section Separating

variable {𝕜 X S : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace 𝕜]
  [SecondCountableTopology 𝕜] [BorelSpace 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [MeasurableSpace S] {μ : Measure S}

/-- **A.e. Pettis measurability with separating tests.** A function essentially valued in a
complete separable subspace is a.e. strongly measurable exactly when each scalar evaluation
from a family separating that subspace is a.e. measurable. -/
theorem aestronglyMeasurable_iff_separating_tests
    {E : Submodule 𝕜 X} [CompleteSpace E] [SeparableSpace E]
    {Y : Set (StrongDual 𝕜 X)} (hsep : ∀ x ∈ E, (∀ x' ∈ Y, x' x = 0) → x = 0)
    {f : S → X} (hf : ∀ᵐ s ∂μ, f s ∈ E) :
    AEStronglyMeasurable f μ ↔ ∀ x' ∈ Y, AEMeasurable (fun s ↦ x' (f s)) μ := by
  classical
  refine ⟨fun h x' _ ↦ (x'.continuous.comp_aestronglyMeasurable h).aemeasurable, ?_⟩
  intro htest
  let g : S → X := fun s ↦ if f s ∈ E then f s else 0
  have hfg : f =ᵐ[μ] g := by
    filter_upwards [hf] with s hs using (ite_eq_left hs).symm
  have hgE : ∀ s, g s ∈ E := fun s ↦ by
    dsimp only [g]
    split_ifs with hs
    · exact hs
    · exact E.zero_mem
  have hg : StronglyMeasurable[inferInstanceAs (MeasurableSpace
      (NullMeasurableSpace S μ))] g := by
    apply (stronglyMeasurable_iff_separating_tests E hsep hgE).2
    intro x' hx'
    exact ((htest x' hx').congr (hfg.fun_comp x')).nullMeasurable
  borelize X
  apply (aestronglyMeasurable_iff_nullMeasurable_separable.2
    ⟨hg.measurable, range g, hg.isSeparable_range,
      Filter.Eventually.of_forall mem_range_self⟩).congr
  exact hfg.symm

end Separating

section RCLike

variable {𝕜 X S : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [MeasurableSpace S] {μ : Measure S}

/-- **A.e. Pettis measurability.** A function is a.e. strongly measurable exactly when it
is essentially valued in a closed separable linear subspace and all continuous linear
scalar evaluations are a.e. measurable. The exceptional null set may depend on the test. -/
theorem aestronglyMeasurable_iff_scalar_tests {f : S → X} :
    AEStronglyMeasurable f μ ↔
      (∃ E : Submodule 𝕜 X, IsClosed (E : Set X) ∧ IsSeparable (E : Set X) ∧
        ∀ᵐ s ∂μ, f s ∈ E) ∧
      ∀ x' : StrongDual 𝕜 X, AEMeasurable (fun s ↦ x' (f s)) μ := by
  classical
  refine ⟨fun hf ↦ ?_, ?_⟩
  · obtain ⟨⟨E, hEc, hEs, hE⟩, -⟩ :=
      (stronglyMeasurable_iff_scalar_tests (𝕜 := 𝕜) _).1 hf.stronglyMeasurable_mk
    refine ⟨⟨E, hEc, hEs, ?_⟩,
      fun x' ↦ (x'.continuous.comp_aestronglyMeasurable hf).aemeasurable⟩
    filter_upwards [hf.ae_eq_mk] with s hs
    rw [hs]
    exact hE s
  rintro ⟨⟨E, hEc, hEs, hfE⟩, htest⟩
  let g : S → X := fun s ↦ if f s ∈ E then f s else 0
  have hfg : f =ᵐ[μ] g := by
    filter_upwards [hfE] with s hs using (ite_eq_left hs).symm
  have hgE : ∀ s, g s ∈ E := fun s ↦ by
    dsimp only [g]
    split_ifs with hs
    · exact hs
    · exact E.zero_mem
  have hg : StronglyMeasurable[inferInstanceAs (MeasurableSpace
      (NullMeasurableSpace S μ))] g := by
    let : MeasurableSpace S := inferInstanceAs (MeasurableSpace (NullMeasurableSpace S μ))
    apply (stronglyMeasurable_iff_scalar_tests (𝕜 := 𝕜) _).2
    exact ⟨⟨E, hEc, hEs, hgE⟩,
      fun x' ↦ ((htest x').congr (hfg.fun_comp x')).nullMeasurable⟩
  borelize X
  apply (aestronglyMeasurable_iff_nullMeasurable_separable.2
    ⟨hg.measurable, range g, hg.isSeparable_range,
      Filter.Eventually.of_forall mem_range_self⟩).congr
  exact hfg.symm

end RCLike

end TauCeti
