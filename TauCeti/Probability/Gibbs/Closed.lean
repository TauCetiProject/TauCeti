/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Gibbs.Specification
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Cylinder
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Action
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Weak closedness of the Gibbs measures of a quasilocal specification

Let `X` be a subshift of configurations `I → S` over a countable index set and a countable
alphabet `S` with its discrete topology and discrete σ-algebra, so that `X` is a metrisable Borel
space (`TauCeti.Subshift.instPseudoMetrizableSpace`). When `S` is finite, `X` is moreover compact
(`TauCeti.Subshift.instCompactSpace`), and so is the space of probability measures on `X` with
the weak topology.

A specification `γ` on `X` is *quasilocal* (`TauCeti.Specification.IsQuasilocal`) when the mass
`γ_Λ (C | ω)` of every cylinder event `C` is a continuous function of `ω`. For a quasilocal
specification the Gibbs probability measures form a weakly closed set, compact for a finite
alphabet (`TauCeti.Specification.isClosed_setOf_isGibbs`,
`TauCeti.Specification.isCompact_setOf_isGibbs`).
The invariant probability measures on `X` form a weakly closed set, as for every continuous
action on a metrisable Borel space
(`MeasureTheory.ProbabilityMeasure.isClosed_setOf_smulInvariantMeasure`), so the invariant Gibbs
measures do too (`TauCeti.Specification.isClosed_setOf_mem_gibbsInvariant`).

The route: a probability measure `μ` is Gibbs iff `∫ γ_Λ (C | ω) dμ(ω) = μ(C)` for every finite
`Λ` and every cylinder event `C` (`TauCeti.Specification.isGibbs_iff_forall_lintegral_eq`). Both
sides are weakly continuous in `μ`: the left one because `γ_Λ (C | ·)` is a continuous function
with values in `[0, 1]`, the right one because the trace of a cylinder event is clopen.

## References

* S. Sheffield, *Random surfaces*, Astérisque 304 (2005), Lemma 3.2.2.
* H.-O. Georgii, *Gibbs measures and phase transitions*, 2nd ed., de Gruyter (2011),
  Theorem 14.15.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge University Press (2021), Lemma 13.7.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set TauCeti.MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace TauCeti

variable {Γ I S : Type*} [Group Γ] [MulAction Γ I] [TopologicalSpace S] [MeasurableSpace S]

namespace Specification

variable {X : Subshift Γ I S} (γ : Specification X)

/-- A specification is quasilocal when the mass `γ_Λ (C | ω)` of every cylinder event `C` is a
continuous function of the boundary condition `ω`. -/
def IsQuasilocal : Prop :=
  ∀ (Λ s : Finset I) (t : Set (s → S)), MeasurableSet t →
    Continuous fun ω : X => γ.kernel Λ ω ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t)

variable {γ}

theorem isQuasilocal_iff :
    γ.IsQuasilocal ↔ ∀ (Λ s : Finset I) (t : Set (s → S)), MeasurableSet t →
      Continuous fun ω : X => γ.kernel Λ ω ((↑) ⁻¹' cylinder (α := fun _ : I => S) s t) :=
  Iff.rfl

variable [Countable I] [Countable S] [DiscreteTopology S] [DiscreteMeasurableSpace S]

/-- For a quasilocal specification, `μ ↦ ∫ γ_Λ (C | ω) dμ(ω)` is weakly continuous on the
probability measures, for every measurable cylinder `C`. -/
private theorem continuous_lintegral_kernel (hγ : γ.IsQuasilocal) (Λ : Finset I)
    {A : Set (I → S)} (hA : A ∈ measurableCylinders fun _ : I => S) :
    Continuous fun μ : ProbabilityMeasure X => ∫⁻ ω, γ.kernel Λ ω ((↑) ⁻¹' A) ∂(μ : Measure X) := by
  have hc : Continuous fun ω : X => γ.kernel Λ ω ((↑) ⁻¹' A) := by
    obtain ⟨s, t, ht, rfl⟩ := (mem_measurableCylinders A).1 hA
    exact hγ Λ s t ht
  have hle (ω : X) : ((γ.kernel Λ ω ((↑) ⁻¹' A)).toNNReal : ℝ) ≤ 1 :=
    NNReal.coe_le_one.2 <| (ENNReal.toNNReal_mono ENNReal.one_ne_top prob_le_one).trans_eq
      ENNReal.toNNReal_one
  -- `γ_Λ (A | ·)` as a bounded continuous function with values in `[0, 1]`
  let f : X →ᵇ ℝ≥0 := .mkOfBound
    ⟨fun ω => (γ.kernel Λ ω ((↑) ⁻¹' A)).toNNReal,
      ENNReal.continuousOn_toNNReal.comp_continuous hc fun _ => measure_ne_top _ _⟩
    1 fun ω ω' => by
      rw [NNReal.dist_eq]
      exact abs_sub_le_of_nonneg_of_le (by positivity) (hle ω) (by positivity) (hle ω')
  have hf (ω : X) : (f ω : ℝ≥0∞) = γ.kernel Λ ω ((↑) ⁻¹' A) :=
    ENNReal.coe_toNNReal (measure_ne_top _ _)
  simp only [← hf]
  exact continuous_iff_continuousAt.2 fun μ =>
    ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.1 tendsto_id f

/-- **Gibbs measures are weakly closed.** For a quasilocal specification on a subshift over a
countable discrete alphabet, the Gibbs probability measures form a weakly closed set. -/
theorem isClosed_setOf_isGibbs (hγ : γ.IsQuasilocal) :
    IsClosed {μ : ProbabilityMeasure X | γ.IsGibbs (μ : Measure X)} := by
  have key : {μ : ProbabilityMeasure X | γ.IsGibbs (μ : Measure X)} =
      ⋂ (Λ : Finset I) (A ∈ measurableCylinders fun _ : I => S),
        {μ : ProbabilityMeasure X | ∫⁻ ω, γ.kernel Λ ω ((↑) ⁻¹' A) ∂(μ : Measure X) =
          (μ : Measure X) ((↑) ⁻¹' A)} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iInter]
    exact isGibbs_iff_forall_lintegral_eq
  rw [key]
  refine isClosed_iInter fun Λ => isClosed_biInter fun A hA =>
    isClosed_eq (continuous_lintegral_kernel hγ Λ hA) ?_
  obtain ⟨s, t, -, rfl⟩ := (mem_measurableCylinders A).1 hA
  simp_rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  refine ENNReal.continuous_coe.comp ?_
  exact continuous_iff_continuousAt.2 fun μ =>
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto tendsto_id
      (isClopen_preimage_cylinder (X := (X : Set (I → S))) s t)

/-- For a quasilocal specification on a subshift over a finite alphabet, the Gibbs probability
measures form a weakly compact set. -/
theorem isCompact_setOf_isGibbs [Finite S] (hγ : γ.IsQuasilocal) :
    IsCompact {μ : ProbabilityMeasure X | γ.IsGibbs (μ : Measure X)} :=
  (isClosed_setOf_isGibbs hγ).isCompact

/-- For a quasilocal specification on a subshift over a countable discrete alphabet, the invariant
Gibbs measures `𝒢_inv(γ)` form a weakly closed set. -/
theorem isClosed_setOf_mem_gibbsInvariant (hγ : γ.IsQuasilocal) :
    IsClosed {μ : ProbabilityMeasure X | (μ : Measure X) ∈ γ.gibbsInvariant} := by
  have key : {μ : ProbabilityMeasure X | (μ : Measure X) ∈ γ.gibbsInvariant} =
      {μ : ProbabilityMeasure X | SMulInvariantMeasure Γ X μ} ∩
        {μ | γ.IsGibbs (μ : Measure X)} := by
    ext μ
    simp only [mem_gibbsInvariant_iff, mem_invariantMeasuresOfMeasureUnivEq_iff, measure_univ,
      and_true, mem_inter_iff, mem_ofPred_eq]
  rw [key]
  exact ProbabilityMeasure.isClosed_setOf_smulInvariantMeasure.inter (isClosed_setOf_isGibbs hγ)

/-- For a quasilocal specification on a subshift over a finite alphabet, the invariant Gibbs
measures `𝒢_inv(γ)` form a weakly compact set. -/
theorem isCompact_setOf_mem_gibbsInvariant [Finite S] (hγ : γ.IsQuasilocal) :
    IsCompact {μ : ProbabilityMeasure X | (μ : Measure X) ∈ γ.gibbsInvariant} :=
  (isClosed_setOf_mem_gibbsInvariant hγ).isCompact

end Specification

end TauCeti
