/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Probability.MarkovChain.Filtered.Basic

/-!
# Future-path laws relative to a filtration

For a countable-state chain satisfying `IsMarkovChain ℱ X κ μ`, the conditional law
of the entire future `processShift X n`, given `ℱ n`, is the chain started at `X n`.
The future includes the current state as coordinate zero. We give the restricted
pushforward law, an event identity, and conditional-expectation identities for
bounded measurable path tests and indicators.

Unlike a statement about the natural history alone, these results retain the
specified filtration. They therefore apply when its additional information is
compatible with the one-step Markov hypothesis, not to arbitrary enlargements.
The measure on the sample space need only be finite.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §1.1 and §1.4.
-/

public section

open MeasureTheory ProbabilityTheory Filter

namespace TauCeti.Probability.IsMarkovChain

variable {Ω S : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace S]
  [Countable S] [Nonempty S] [MeasurableSingletonClass S]
  {ℱ : Filtration ℕ mΩ} {X : ℕ → Ω → S} {κ : Kernel S S} {μ : Measure Ω}
  [IsFiniteMeasure μ] [IsMarkovKernel κ]

/-- On an event known at time `n`, the future has the Markov-chain law whose initial
measure is the restricted law of the current state. No normalization of that event
is required, so the formula also covers null events. -/
theorem map_processShift_restrict (h : IsMarkovChain ℱ X κ μ) (n : ℕ)
    {A : Set Ω} (hA : MeasurableSet[ℱ n] A) :
    (μ.restrict A).map (processShift X n) =
      markovChainLaw ((μ.restrict A).map (X n)) κ := by
  -- Discrete topology is used only to invoke the natural-filtration characterization.
  let : TopologicalSpace S := ⊥
  let : DiscreteTopology S := ⟨rfl⟩
  let : BorelSpace S := ⟨by
    rw [borel_eq_top_of_discrete]
    exact top_unique fun s _ => s.to_countable.measurableSet⟩
  let Y : ℕ → Ω → S := fun k => X (n + k)
  let 𝒢 : Filtration ℕ mΩ :=
    ⟨fun k => ℱ (n + k), fun _ _ hkl => ℱ.mono (Nat.add_le_add_left hkl n),
      fun k => ℱ.le (n + k)⟩
  have hY : ∀ k, StronglyMeasurable (Y k) :=
    fun k => h.adapted.measurable.stronglyMeasurable
  have hg : IsMarkovChain 𝒢 Y κ (μ.restrict A) := by
    refine ⟨fun k => h.adapted (n + k), fun k f hf hb => ?_⟩
    obtain ⟨C, hC⟩ := hb
    have hi : Integrable (fun ω => f (X (n + k + 1) ω)) μ :=
      ⟨(hf.comp h.adapted.measurable).aestronglyMeasurable,
        .of_bounded (Eventually.of_forall fun ω => hC _)⟩
    have hr := condExp_restrict_ae_eq_restrict (ℱ.le (n + k))
      (ℱ.mono (Nat.le_add_right n k) _ hA) hi
    simpa only [Y, Nat.add_assoc] using
      hr.trans (ae_restrict_of_ae (h.condExp_eq (n + k) f hf ⟨C, hC⟩))
  have hle : Filtration.natural Y hY ≤ 𝒢 := by
    intro k
    exact iSup_le fun j => iSup_le fun hj =>
      ((h.adapted (n + j)).mono (ℱ.mono (Nat.add_le_add_left hj n)) le_rfl).comap_le
  have hlaw := (hasLaw_markovChainLaw_iff_isMarkovChain_natural
    ((μ.restrict A).map (Y 0)) hY).2 ⟨rfl, hg.mono hle
      (Filtration.stronglyAdapted_natural hY).adapted⟩
  have hp : (fun ω k => Y k ω) = processShift X n := by
    ext ω k
    simp only [Y, processShift_apply]
  simpa only [hp, Y, Nat.add_zero] using hlaw.map_eq

/-- The joint event identity for information available at time `n` and a measurable
future-path event. The path-law kernel is evaluated at the current state. -/
theorem measure_inter_processShift_preimage (h : IsMarkovChain ℱ X κ μ) (n : ℕ)
    {A : Set Ω} (hA : MeasurableSet[ℱ n] A)
    {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    μ (A ∩ processShift X n ⁻¹' B) =
      ∫⁻ ω in A, κ.markovChainKernel (X n ω) B ∂μ := by
  have hshift := measurable_processShift (fun _ => h.adapted.measurable) (m := n)
  have heq := congrArg (fun ν : Measure (ℕ → S) => ν B)
    (h.map_processShift_restrict n hA)
  rw [Measure.map_apply hshift hB, Measure.restrict_apply (hshift hB),
    Measure.markovChainLaw_eq_comp, Measure.bind_apply hB κ.markovChainKernel.aemeasurable,
    lintegral_map (Kernel.measurable_coe _ hB) h.adapted.measurable] at heq
  simpa only [Set.inter_comm] using heq

/-- The conditional expectation of a bounded measurable function of the whole
future, relative to the filtration in the Markov hypothesis. -/
theorem condExp_processShift (h : IsMarkovChain ℱ X κ μ) (n : ℕ)
    {f : (ℕ → S) → ℝ} (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ w, ‖f w‖ ≤ C) :
    μ[fun ω => f (processShift X n ω) | ℱ n] =ᵐ[μ]
      fun ω => ∫ w, f w ∂κ.markovChainKernel (X n ω) := by
  obtain ⟨C, hC⟩ := hb
  have hshift := measurable_processShift (fun _ => h.adapted.measurable) (m := n)
  have hi (ν : Measure (ℕ → S)) [IsFiniteMeasure ν] : Integrable f ν :=
    ⟨hf.aestronglyMeasurable, .of_bounded (Eventually.of_forall hC)⟩
  have hg : StronglyMeasurable[ℱ n]
      (fun ω => ∫ w, f w ∂κ.markovChainKernel (X n ω)) :=
    hf.stronglyMeasurable.integral_kernel.comp_measurable (h.adapted n)
  have hgi : Integrable (fun ω => ∫ w, f w ∂κ.markovChainKernel (X n ω)) μ :=
    ⟨(hg.mono (ℱ.le n)).aestronglyMeasurable, .of_bounded
      (Eventually.of_forall fun ω => by
        simpa using norm_integral_le_of_norm_le_const
          (μ := κ.markovChainKernel (X n ω)) (Eventually.of_forall hC))⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le n)
    ⟨(hf.comp hshift).aestronglyMeasurable,
      .of_bounded (Eventually.of_forall fun ω => hC _)⟩
    (fun _ _ _ => hgi.integrableOn) ?_ hg.aestronglyMeasurable).symm
  intro A hA _
  symm
  simp only [Function.comp_def]
  rw [← integral_map hshift.aemeasurable hf.aestronglyMeasurable,
    h.map_processShift_restrict n hA, Measure.markovChainLaw_eq_comp,
    Measure.comp_eq_comp_const_apply, Kernel.integral_comp (hi _), Kernel.const_apply,
    integral_map h.adapted.measurable.aemeasurable
      hf.stronglyMeasurable.integral_kernel.aestronglyMeasurable]

/-- Conditional probabilities of measurable future-path events, relative to the
specified filtration. -/
theorem condExp_indicator_processShift (h : IsMarkovChain ℱ X κ μ) (n : ℕ)
    {B : Set (ℕ → S)} (hB : MeasurableSet B) :
    μ[(processShift X n ⁻¹' B).indicator (fun _ => (1 : ℝ)) | ℱ n] =ᵐ[μ]
      fun ω => (κ.markovChainKernel (X n ω)).real B := by
  have hb : ∃ C : ℝ, ∀ w, ‖B.indicator (fun _ => (1 : ℝ)) w‖ ≤ C :=
    ⟨1, fun w => by by_cases hw : w ∈ B <;> simp [hw]⟩
  simpa only [← Set.indicator_comp_right, Function.comp_def,
    integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one] using
    h.condExp_processShift n (measurable_const.indicator hB) hb

end TauCeti.Probability.IsMarkovChain
