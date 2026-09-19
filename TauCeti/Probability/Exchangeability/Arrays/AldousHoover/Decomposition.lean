/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.ConditionalLaw
public import TauCeti.Probability.Kernel.Randomization

/-!
# Uniform mixtures of dissociated array laws

Every jointly exchangeable probability law on arrays over a standard Borel space is a
measurable mixture of jointly exchangeable, dissociated probability laws. The mixing variable
can be taken to be one uniform variable on the unit interval. This isolates the global noise
in the Aldous--Hoover representation: it remains to represent the resulting measurable family
of dissociated laws by vertex and cell noise.

`JointlyExchangeable.exists_dissociated_kernel` gives the mixture as a Markov kernel from the
unit interval, with its composition against volume equal to the original law.
`JointlyExchangeable.exists_dissociated_coding` realizes that kernel using a second independent
uniform variable. Its sections retain both exchangeability and dissociation, and its joint
pushforward is the original array law. The second variable samples a whole array; it is not
yet resolved into vertex and cell variables.

The construction samples an array from the original law using uniform noise, then takes its
conditional law given the corner tail. Thus it only randomizes a standard Borel array space;
no standard Borel instance for the Giry space of probability measures is needed.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22 (randomization).
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
  {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]

/-- A jointly exchangeable array law is a uniform mixture of jointly exchangeable, dissociated
probability laws. The component laws form a measurable Markov kernel, so the same global
parameter can be retained in subsequent conditional representations. -/
theorem JointlyExchangeable.exists_dissociated_kernel
    (hρ : JointlyExchangeable ρ fun p x => x p) :
    ∃ κ : ProbabilityTheory.Kernel unitInterval (ℕ × ℕ → α), IsMarkovKernel κ ∧
      (∀ᵐ u ∂(volume : Measure unitInterval),
        JointlyExchangeable (κ u) (fun p x => x p) ∧
          JointlyDissociated (κ u) (fun p x => x p)) ∧
      κ ∘ₘ (volume : Measure unitInterval) = ρ := by
  have : Nonempty (ℕ × ℕ → α) := nonempty_of_isProbabilityMeasure ρ
  let P : ProbabilityMeasure (ℕ × ℕ → α) := ⟨ρ, inferInstance⟩
  let f := unitIntervalCoding (ℕ × ℕ → α) P
  have hf : Measurable f := measurable_unitIntervalCoding P
  have hpres : MeasurePreserving f (volume : Measure unitInterval) ρ :=
    ⟨hf, map_volume_unitIntervalCoding P⟩
  have hm := arrayTail_le_ambient (X := fun p (x : ℕ × ℕ → α) => x p) 0
    (fun p _ _ => measurable_pi_apply p)
  let K := condExpKernel ρ (arrayTail (fun p (x : ℕ × ℕ → α) => x p))
  let κ := K.comap f (hf.mono le_rfl hm)
  refine ⟨κ, inferInstance, ?_, ?_⟩
  · have hgood := hρ.ae_jointlyExchangeable_condExpKernel_arrayTail.and
      hρ.ae_jointlyDissociated_condExpKernel_arrayTail
    exact hpres.quasiMeasurePreserving.ae hgood
  · -- Integrating the conditional law uses the tail-trimmed measure; the coding map
    -- samples the ambient law, so pass between them only for tail-measurable integrands.
    rw [← condExpKernel_comp_trim (μ := ρ) hm]
    ext s hs
    rw [Measure.bind_apply hs κ.aemeasurable,
      Measure.bind_apply hs K.aemeasurable]
    simp only [κ, ProbabilityTheory.Kernel.comap_apply]
    rw [lintegral_trim hm (K.measurable_coe hs)]
    exact hpres.lintegral_comp ((K.measurable_coe hs).mono hm le_rfl)

/-- A jointly exchangeable array can be sampled by two independent uniform variables: the first
selects an exchangeable, dissociated component law, and the second samples from that law.
The coding is jointly measurable, and one almost-sure set of first variables works for both
properties of the component law. -/
theorem JointlyExchangeable.exists_dissociated_coding
    (hρ : JointlyExchangeable ρ fun p x => x p) :
    ∃ f : unitInterval → unitInterval → (ℕ × ℕ → α),
      Measurable (Function.uncurry f) ∧
      (∀ᵐ u ∂(volume : Measure unitInterval),
        JointlyExchangeable ((volume : Measure unitInterval).map (f u)) (fun p x => x p) ∧
          JointlyDissociated ((volume : Measure unitInterval).map (f u)) (fun p x => x p)) ∧
      ((volume : Measure unitInterval).prod volume).map (Function.uncurry f) = ρ := by
  have : Nonempty (ℕ × ℕ → α) := nonempty_of_isProbabilityMeasure ρ
  obtain ⟨κ, hκ, hgood, hmix⟩ := hρ.exists_dissociated_kernel
  obtain ⟨f, hf, hmap⟩ := ProbabilityTheory.Kernel.exists_measurable_map_eq_unitInterval κ
  refine ⟨f, hf, ?_, ?_⟩
  · simpa only [hmap] using hgood
  · have hjoint := map_prod_volume_eq_compProd_of_map_volume
      (μ := (volume : Measure unitInterval)) κ f hf hmap
    have hsnd := congrArg Measure.snd hjoint
    rw [Measure.snd_compProd, hmix] at hsnd
    have hpair : Measurable (fun p : unitInterval × unitInterval => (p.1, f p.1 p.2)) :=
      measurable_fst.prodMk hf
    rw [Measure.snd, Measure.map_map measurable_snd hpair] at hsnd
    exact hsnd

end TauCeti.Probability
