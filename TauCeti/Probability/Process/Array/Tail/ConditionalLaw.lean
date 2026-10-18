/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Process.Array.Tail.Basic
public import TauCeti.Probability.Kernel.Randomization
public import Mathlib.Probability.Kernel.Condexp

/-!
# Uniform mixtures of array-tail conditional laws

The conditional laws of an array given its corner tail can be parametrized measurably by the unit
interval. More precisely, any almost-sure property of these conditional laws is inherited by
almost every member of a Markov kernel whose mixture is the original array law. Randomizing that
kernel with a second independent uniform variable gives a jointly measurable two-variable coding
of the array law with the same fibrewise property.

These results concern an arbitrary probability law on array path space and an arbitrary property
of measures; they require no exchangeability assumption. Exchangeability-specific decompositions
specialize them in `TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Decomposition`.

## Main results

* `TauCeti.Probability.exists_kernel_of_ae_condExpKernel_arrayTail` parametrizes the corner-tail
  conditional laws by a Markov kernel on the unit interval.
* `TauCeti.Probability.exists_coding_of_ae_condExpKernel_arrayTail` samples the resulting kernel by
  a second independent uniform variable.

## References

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
The supplied property `P`, when it holds for almost every conditional law, holds for almost every
component of the kernel. -/
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
  · have hjoint := κ.map_prod_eq_compProd_of_map
      (μ := (volume : Measure unitInterval)) volume f hf hmap
    have hsnd := congrArg Measure.snd hjoint
    rw [Measure.snd_compProd, hmix] at hsnd
    have hpair : Measurable (fun p : unitInterval × unitInterval => (p.1, f p.1 p.2)) :=
      measurable_fst.prodMk hf
    rw [Measure.snd, Measure.map_map measurable_snd hpair] at hsnd
    exact hsnd

end TauCeti.Probability

end
