/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.ConditionalLaw
public import TauCeti.Probability.Kernel.Randomization

/-!
# Uniform mixtures of jointly dissociated array laws

Every exchangeable probability law on arrays over a standard Borel space is a measurable mixture
of jointly dissociated ones, with the same array symmetry as the original law and with one uniform
variable on the unit interval as the mixing variable. This isolates the global noise in the
Aldous--Hoover representation: it remains to represent the resulting measurable family by vertex
(row and column) and cell noise.

Both array symmetries are covered. `JointlyExchangeable.exists_dissociated_kernel` and
`SeparatelyExchangeable.exists_jointlyDissociated_kernel` give the mixture as a Markov kernel from
the unit interval, with its composition against volume equal to the original law;
`JointlyExchangeable.exists_dissociated_coding` and
`SeparatelyExchangeable.exists_jointlyDissociated_coding` realize that kernel using a second
independent uniform variable. Their sections retain both the symmetry and joint dissociation, and
their joint pushforward is the original array law. The second variable samples a whole array; it is
not yet resolved into vertex (row and column) and cell variables.

The components of a separately exchangeable law are asserted to be *jointly* dissociated, which is
what dropping the global variable of a separate coding asks of them
(`AldousHoover.exists_map_separateArray_snd_eq_of_jointlyDissociated`).

The construction samples an array from the original law using uniform noise, then takes its
conditional law given the corner tail. Thus it only randomizes a standard Borel array space;
no standard Borel instance for the Giry space of probability measures is needed. Nothing in it
mentions a symmetry, so it is carried out once for an arbitrary property of the conditional laws
(`exists_kernel_of_ae_condExpKernel_arrayTail`, `exists_coding_of_ae_condExpKernel_arrayTail`) and
specialized afterwards.

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
  {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ] {P : Measure (ℕ × ℕ → α) → Prop}

/-- **The corner-tail conditional laws of an array law, sampled by a uniform variable.** Drawing
the conditioning variable through the canonical uniform coding presents those conditional laws as a
Markov kernel from the unit interval whose composition with the uniform law is the original law.
Any property holding for almost every conditional law holds for almost every component, so the
kernel carries the symmetry and dissociation of the conditional laws with it. -/
theorem exists_kernel_of_ae_condExpKernel_arrayTail
    (hP : ∀ᵐ x ∂ρ, P (condExpKernel ρ (arrayTail fun p (y : ℕ × ℕ → α) => y p) x)) :
    ∃ κ : ProbabilityTheory.Kernel unitInterval (ℕ × ℕ → α), IsMarkovKernel κ ∧
      (∀ᵐ u ∂(volume : Measure unitInterval), P (κ u)) ∧
      κ ∘ₘ (volume : Measure unitInterval) = ρ := by
  have : Nonempty (ℕ × ℕ → α) := nonempty_of_isProbabilityMeasure ρ
  let Q : ProbabilityMeasure (ℕ × ℕ → α) := ⟨ρ, inferInstance⟩
  let f := unitIntervalCoding (ℕ × ℕ → α) Q
  have hf : Measurable f := measurable_unitIntervalCoding Q
  have hpres : MeasurePreserving f (volume : Measure unitInterval) ρ :=
    ⟨hf, map_volume_unitIntervalCoding Q⟩
  have hm := arrayTail_le_ambient (X := fun p (x : ℕ × ℕ → α) => x p) 0
    (fun p _ _ => measurable_pi_apply p)
  let K := condExpKernel ρ (arrayTail (fun p (x : ℕ × ℕ → α) => x p))
  let κ := K.comap f (hf.mono le_rfl hm)
  refine ⟨κ, inferInstance, hpres.quasiMeasurePreserving.ae hP, ?_⟩
  -- Integrating the conditional law uses the tail-trimmed measure; the coding map
  -- samples the ambient law, so pass between them only for tail-measurable integrands.
  rw [← condExpKernel_comp_trim (μ := ρ) hm]
  ext s hs
  rw [Measure.bind_apply hs κ.aemeasurable,
    Measure.bind_apply hs K.aemeasurable]
  simp only [κ, ProbabilityTheory.Kernel.comap_apply]
  rw [lintegral_trim hm (K.measurable_coe hs)]
  exact hpres.lintegral_comp ((K.measurable_coe hs).mono hm le_rfl)

/-- **An array law is sampled by two independent uniform variables**, the first selecting a
corner-tail conditional law and the second sampling from it. The coding is jointly measurable, and
one almost-sure set of first variables works for the given property `P` of the conditional laws.
Taking `P` to be a conjunction gives one set on which all conjuncts hold. -/
theorem exists_coding_of_ae_condExpKernel_arrayTail
    (hP : ∀ᵐ x ∂ρ, P (condExpKernel ρ (arrayTail fun p (y : ℕ × ℕ → α) => y p) x)) :
    ∃ f : unitInterval → unitInterval → (ℕ × ℕ → α),
      Measurable (Function.uncurry f) ∧
      (∀ᵐ u ∂(volume : Measure unitInterval), P ((volume : Measure unitInterval).map (f u))) ∧
      ((volume : Measure unitInterval).prod volume).map (Function.uncurry f) = ρ := by
  have : Nonempty (ℕ × ℕ → α) := nonempty_of_isProbabilityMeasure ρ
  obtain ⟨κ, hκ, hgood, hmix⟩ := exists_kernel_of_ae_condExpKernel_arrayTail hP
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

/-- A jointly exchangeable array law is a uniform mixture of jointly exchangeable, dissociated
probability laws. The component laws form a measurable Markov kernel, so the same global
parameter can be retained in subsequent conditional representations. -/
theorem JointlyExchangeable.exists_dissociated_kernel
    (hρ : JointlyExchangeable ρ fun p x => x p) :
    ∃ κ : ProbabilityTheory.Kernel unitInterval (ℕ × ℕ → α), IsMarkovKernel κ ∧
      (∀ᵐ u ∂(volume : Measure unitInterval),
        JointlyExchangeable (κ u) (fun p x => x p) ∧
          JointlyDissociated (κ u) (fun p x => x p)) ∧
      κ ∘ₘ (volume : Measure unitInterval) = ρ :=
  exists_kernel_of_ae_condExpKernel_arrayTail
    (P := fun ν => JointlyExchangeable ν (fun p x => x p) ∧ JointlyDissociated ν (fun p x => x p))
    (hρ.ae_jointlyExchangeable_condExpKernel_arrayTail.and
      hρ.ae_jointlyDissociated_condExpKernel_arrayTail)

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
      ((volume : Measure unitInterval).prod volume).map (Function.uncurry f) = ρ :=
  exists_coding_of_ae_condExpKernel_arrayTail
    (P := fun ν => JointlyExchangeable ν (fun p x => x p) ∧ JointlyDissociated ν (fun p x => x p))
    (hρ.ae_jointlyExchangeable_condExpKernel_arrayTail.and
      hρ.ae_jointlyDissociated_condExpKernel_arrayTail)

/-- **A separately exchangeable array law is a uniform mixture of separately exchangeable,
jointly dissociated probability laws.** The components keep the two-axis symmetry of the original
law, so this is the reduction of the separate Aldous--Hoover representation to its ergodic form;
joint dissociation is the hypothesis that the global-variable-free separate coding
(`AldousHoover.exists_map_separateArray_snd_eq_of_jointlyDissociated`) asks of a component. -/
theorem SeparatelyExchangeable.exists_jointlyDissociated_kernel
    (hρ : SeparatelyExchangeable ρ fun p x => x p) :
    ∃ κ : ProbabilityTheory.Kernel unitInterval (ℕ × ℕ → α), IsMarkovKernel κ ∧
      (∀ᵐ u ∂(volume : Measure unitInterval),
        SeparatelyExchangeable (κ u) (fun p x => x p) ∧
          JointlyDissociated (κ u) (fun p x => x p)) ∧
      κ ∘ₘ (volume : Measure unitInterval) = ρ :=
  exists_kernel_of_ae_condExpKernel_arrayTail
    (P := fun ν => SeparatelyExchangeable ν (fun p x => x p) ∧
      JointlyDissociated ν (fun p x => x p))
    (hρ.ae_separatelyExchangeable_condExpKernel_arrayTail.and
      hρ.jointlyExchangeable.ae_jointlyDissociated_condExpKernel_arrayTail)

/-- **A separately exchangeable array can be sampled by two independent uniform variables**: the
first selects a separately exchangeable, jointly dissociated component law, and the second samples
from that law. This is the separate-symmetry counterpart of
`JointlyExchangeable.exists_dissociated_coding`; the second variable samples a whole array and is
not yet resolved into row, column and cell variables. -/
theorem SeparatelyExchangeable.exists_jointlyDissociated_coding
    (hρ : SeparatelyExchangeable ρ fun p x => x p) :
    ∃ f : unitInterval → unitInterval → (ℕ × ℕ → α),
      Measurable (Function.uncurry f) ∧
      (∀ᵐ u ∂(volume : Measure unitInterval),
        SeparatelyExchangeable ((volume : Measure unitInterval).map (f u)) (fun p x => x p) ∧
          JointlyDissociated ((volume : Measure unitInterval).map (f u)) (fun p x => x p)) ∧
      ((volume : Measure unitInterval).prod volume).map (Function.uncurry f) = ρ :=
  exists_coding_of_ae_condExpKernel_arrayTail
    (P := fun ν => SeparatelyExchangeable ν (fun p x => x p) ∧
      JointlyDissociated ν (fun p x => x p))
    (hρ.ae_separatelyExchangeable_condExpKernel_arrayTail.and
      hρ.jointlyExchangeable.ae_jointlyDissociated_condExpKernel_arrayTail)

end TauCeti.Probability
