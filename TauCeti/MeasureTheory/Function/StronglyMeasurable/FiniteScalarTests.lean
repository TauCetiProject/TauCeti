/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.StronglyMeasurable.FiniteSupport
import TauCeti.MeasureTheory.Function.StronglyMeasurable.ContinuousOn
import TauCeti.MeasureTheory.Function.StronglyMeasurable.FiniteLimit
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.ScalarTests
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Normed.Operator.Norming

/-!
# Finite-support Pettis measurability

A function is a.e. finitely strongly measurable exactly when it has essentially separable
range and every continuous linear functional applied to it is a.e. finitely strongly
measurable. For functions supported in a complete separable subspace, any separating family
of functionals suffices. The exceptional null set may depend on the functional.

The support condition matters for arbitrary measures: on a singleton of infinite measure,
the constant one is strongly measurable but is not a.e. finitely strongly measurable.
Countably many separating tests supply a common measurable sigma-finite support; comparison
of their generated sigma-algebra with the Borel sigma-algebra supplies measurability.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Vol. I,
  Springer, 2016, §1.1.b, Theorem 1.1.20 and Corollaries 1.1.21–1.1.25.

The measurability argument uses the pointwise scalar-test criteria in `ScalarTests` and
Mathlib's `aestronglyMeasurable_iff_nullMeasurable_separable`.
-/

public section

open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

namespace TauCeti

section Field

variable {𝕜 X S : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [MeasurableSpace S] {μ : Measure S}

/-- On a separable normed space, a.e. finite strong measurability of a separating family of
scalar evaluations gives a common measurable sigma-finite support for the original function.
No measurability or completeness assumption on the function or target is needed. -/
theorem exists_set_sigmaFinite_of_separating_tests [SeparableSpace X]
    {T : Set (StrongDual 𝕜 X)} (hsep : ∀ x : X, (∀ x' ∈ T, x' x = 0) → x = 0)
    {f : S → X} (htest : ∀ x' ∈ T, AEFinStronglyMeasurable (fun s ↦ x' (f s)) μ) :
    ∃ t, MeasurableSet t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ SigmaFinite (μ.restrict t) := by
  obtain ⟨T₀, hT₀T, hTc, hsep₀⟩ := exists_countable_separating_subset hsep
  have : Countable T₀ := hTc.to_subtype
  obtain ⟨t, ht, hzero, hσ⟩ := AEFinStronglyMeasurable.exists_set_sigmaFinite_of_countable
    (g := fun (i : T₀) s ↦ i.val (f s)) fun i ↦ htest i (hT₀T i.property)
  refine ⟨t, ht, ?_, hσ⟩
  filter_upwards [ae_all_iff.2 hzero] with s hs
  exact hsep₀ _ fun x' hx' ↦ hs ⟨x', hx'⟩

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- Reconstruct finite strong measurability from tests on an essentially supporting subspace.
This combines the Borel comparison and the common-support argument. -/
private theorem aefinStronglyMeasurable_of_subspace_tests (E : Submodule 𝕜 X)
    [SeparableSpace E] {T : Set (StrongDual 𝕜 X)}
    (hB : evalMeasurableSpace ((fun x' : StrongDual 𝕜 X ↦ x'.comp E.subtypeL) '' T) = borel E)
    (hsep : ∀ x ∈ E, (∀ x' ∈ T, x' x = 0) → x = 0)
    {f : S → X} (hfE : ∀ᵐ s ∂μ, f s ∈ E)
    (htest : ∀ x' ∈ T, AEFinStronglyMeasurable (fun s ↦ x' (f s)) μ) :
    AEFinStronglyMeasurable f μ := by
  classical
  borelize ↥E
  let g (s : S) : E := if hs : f s ∈ E then ⟨f s, hs⟩ else 0
  have hgf : (fun s ↦ (g s : X)) =ᵐ[μ] f := by
    filter_upwards [hfE] with s hs using by simp [g, hs]
  have htestg : ∀ y ∈ (fun x' : StrongDual 𝕜 X ↦ x'.comp E.subtypeL) '' T,
      AEFinStronglyMeasurable (fun s ↦ y (g s)) μ := by
    rintro _ ⟨x', hx', rfl⟩
    obtain ⟨k, hk, hfk⟩ := htest x' hx'
    exact ⟨k, hk, (hgf.fun_comp x').trans hfk⟩
  have hg : AEStronglyMeasurable g μ := by
    refine aestronglyMeasurable_iff_nullMeasurable_separable.2 ⟨?_, univ,
      .of_separableSpace univ, Eventually.of_forall fun _ ↦ mem_univ _⟩
    -- Use the null-measurable sigma-algebra, keeping the domain of `g` as `S`. The scalar tests
    -- enter through `NullMeasurable.measurable'`; the goal `NullMeasurable g μ` unfolds by
    -- definition to measurability for `NullMeasurableSpace S μ`, so `hmeas` closes it.
    have hmeas : @Measurable S E
        (inferInstance : MeasurableSpace (NullMeasurableSpace S μ)) (borel E) g := by
      rw [← hB]
      exact measurable_evalMeasurableSpace_iff.2 fun y hy ↦
        (htestg y hy).aemeasurable.nullMeasurable.measurable'
    exact hmeas
  obtain ⟨t, ht, hzero, hσ⟩ := exists_set_sigmaFinite_of_separating_tests
    (f := g) (T := (fun x' : StrongDual 𝕜 X ↦ x'.comp E.subtypeL) '' T) (fun x hx ↦
      Subtype.ext <| hsep x x.property fun x' hx' ↦ hx _ (mem_image_of_mem _ hx')) htestg
  refine aefinStronglyMeasurable_iff_aestronglyMeasurable_and_exists_set_sigmaFinite.2
    ⟨(E.subtypeL.continuous.comp_aestronglyMeasurable hg).congr hgf, t, ht, ?_, hσ⟩
  filter_upwards [hzero, ae_restrict_of_ae hgf] with s hs hsf
  exact hsf.symm.trans (congrArg Subtype.val hs)

end Field

section RCLike

variable {𝕜 X S : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [MeasurableSpace S] {μ : Measure S}

/-- **Finite-support Pettis measurability.** A function is a.e. finitely strongly measurable
exactly when it is essentially supported in a closed separable subspace and every scalar
evaluation is a.e. finitely strongly measurable. The target need not be complete. -/
theorem aefinStronglyMeasurable_iff_scalar_tests {f : S → X} :
    AEFinStronglyMeasurable f μ ↔
      (∃ E : Submodule 𝕜 X, IsClosed (E : Set X) ∧ IsSeparable (E : Set X) ∧
        ∀ᵐ s ∂μ, f s ∈ E) ∧
      ∀ x' : StrongDual 𝕜 X, AEFinStronglyMeasurable (fun s ↦ x' (f s)) μ := by
  constructor
  · intro hf
    refine ⟨?_, fun x' ↦ x'.continuous.comp_aefinStronglyMeasurable hf (map_zero x')⟩
    obtain ⟨g, hg, hfg⟩ := hf
    obtain ⟨⟨E, hEc, hEs, hgE⟩, -⟩ :=
      (stronglyMeasurable_iff_scalar_tests (𝕜 := 𝕜) g).1 hg.stronglyMeasurable
    exact ⟨E, hEc, hEs, by filter_upwards [hfg] with s hs using hs.symm ▸ hgE s⟩
  · rintro ⟨⟨E, -, hEs, hfE⟩, htest⟩
    have : SeparableSpace E := hEs.separableSpace
    have hsurj : (fun x' : StrongDual 𝕜 X ↦ x'.comp E.subtypeL) '' univ = univ := by
      apply eq_univ_of_forall
      intro y
      obtain ⟨x', hx', -⟩ := exists_extension_norm_eq E y
      exact ⟨x', mem_univ _, ContinuousLinearMap.ext hx'⟩
    refine aefinStronglyMeasurable_of_subspace_tests E
      (T := univ) (by rw [hsurj]; exact evalMeasurableSpace_univ_eq_borel) ?_ hfE
      (fun x' _ ↦ htest x')
    exact fun x _ hzero ↦
      SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun x' ↦ hzero x' (mem_univ _)

end RCLike

section Separating

variable {𝕜 X S : Type*} [NontriviallyNormedField 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  [SecondCountableTopology 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [MeasurableSpace S] {μ : Measure S}

/-- A separating family detects a.e. finite strong measurability on a complete separable
supporting subspace. Each scalar test may have its own exceptional null set. -/
theorem aefinStronglyMeasurable_iff_separating_tests {E : Submodule 𝕜 X}
    [CompleteSpace E] [SeparableSpace E] {T : Set (StrongDual 𝕜 X)}
    (hsep : ∀ x ∈ E, (∀ x' ∈ T, x' x = 0) → x = 0)
    {f : S → X} (hfE : ∀ᵐ s ∂μ, f s ∈ E) :
    AEFinStronglyMeasurable f μ ↔
      ∀ x' ∈ T, AEFinStronglyMeasurable (fun s ↦ x' (f s)) μ := by
  refine ⟨?_, aefinStronglyMeasurable_of_subspace_tests E ?_ hsep hfE⟩
  · exact fun hf x' _ ↦ x'.continuous.comp_aefinStronglyMeasurable hf (map_zero x')
  · apply evalMeasurableSpace_eq_borel_of_separating
    intro x hx
    exact Subtype.ext <| hsep x x.property fun x' hx' ↦ hx _ (mem_image_of_mem _ hx')

end Separating

end TauCeti
