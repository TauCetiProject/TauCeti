/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.ExchangeableAtMonotone
public import TauCeti.Probability.PopulationSampling
public import TauCeti.Probability.UniformSampling
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Finite exchangeability as sampling without replacement

This file identifies every shorter marginal of a finite exchangeable process with sampling
without replacement from its observed finite population.

Given a population law `ρ : Measure (κ → α)`, `sampleWithoutReplacement ρ` first draws
`x ∼ ρ`, independently draws a uniform injective selection `k : ι → κ`, and returns `x ∘ k`. It is
the random-population reindexing construction `samplePopulation` along uniform injective
selections; sampling with replacement (`sampleWithReplacement`, in `FiniteDeFinetti.lean`) is the
same construction along all index maps.

The main theorem says that if the first `n` coordinates of a process are exchangeable, then
sampling `m ≤ n` entries without replacement from that random `n`-tuple has exactly the original
`m`-prefix law. This is the representation half of the finite de Finetti argument: the companion
with-replacement law is the product of the empirical measure, and the collision estimate in
`TauCeti.Probability.UniformSampling` then controls their difference.

The proof averages the exchangeable law over all injective selections. Every selection has the
same law by `ExchangeableAt.blockLaw_eq_prefixLaw_of_injective`, so the average has that law too.

## Main declarations

* `sampleWithoutReplacement` — sample a random finite population at uniformly chosen distinct
  indices;
* `ExchangeableAt.sampleWithoutReplacement_eq_prefixLaw` — the finite exchangeable
  without-replacement representation.

## References

* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, “finite de Finetti bounds”.
* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.

No material is adapted from `cameronfreer/exchangeability`; its three de Finetti routes concern
infinite exchangeable sequences rather than quantitative finite approximation.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The law obtained by sampling a random finite population without replacement.

First draw a population `x : κ → α` with law `ρ`; independently and uniformly draw an injective
selection `k : ι → κ`; then return the sample `i ↦ x (k i)`. This is `samplePopulation` along the
uniform law on injective index maps. If no injective selection exists, Mathlib's `uniformOn`
convention makes this the zero measure.

The population index is finite because uniform counting only distributes mass over finitely many
injective selections. -/
def sampleWithoutReplacement {ι κ : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (ρ : Measure (κ → α)) : Measure (ι → α) :=
  samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ

/-- Sampling without replacement is `samplePopulation` along uniform injective selections. -/
theorem sampleWithoutReplacement_def {ι κ : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (ρ : Measure (κ → α)) :
    sampleWithoutReplacement (ι := ι) ρ =
      samplePopulation (uniformOn {k : ι → κ | Function.Injective k}) ρ :=
  (rfl)

/-- Sampling without replacement preserves probability mass whenever an injective selection
exists. -/
theorem isProbabilityMeasure_sampleWithoutReplacement {ι κ : Type*} [Finite κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (ρ : Measure (κ → α))
    [IsProbabilityMeasure ρ] (e : ι ↪ κ) :
    IsProbabilityMeasure
      (sampleWithoutReplacement (ι := ι) (κ := κ) (α := α) ρ) := by
  have : Finite ι := Finite.of_injective e e.injective
  let E : Set (ι → κ) := {k | Function.Injective k}
  let _ : IsProbabilityMeasure (uniformOn E) :=
    isProbabilityMeasure_uniformOn (Set.toFinite E) ⟨e, e.injective⟩
  rw [sampleWithoutReplacement_def]
  infer_instance

/-- **Finite exchangeability is sampling without replacement.** If the first `n` coordinates are
exchangeable, then drawing `m ≤ n` distinct positions uniformly from that random `n`-tuple has
exactly the law of the first `m` coordinates.

This is an equality of measures, not merely an eventwise bound. The later finite de Finetti bound
compares its left-hand side with sampling *with* replacement, using the collision estimate in
`UniformSampling.lean`. -/
theorem ExchangeableAt.sampleWithoutReplacement_eq_prefixLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    sampleWithoutReplacement (ι := Fin m) (prefixLaw μ X n) = prefixLaw μ X m := by
  let E : Set (Fin m → Fin n) := {k | Function.Injective k}
  have hEfin : E.Finite := Set.toFinite E
  have hEne : E.Nonempty :=
    ⟨Fin.castLE hmn, fun _ _ hxy => Fin.castLE_injective hmn hxy⟩
  let _ : IsProbabilityMeasure (uniformOn E) :=
    isProbabilityMeasure_uniformOn hEfin hEne
  have hae : ∀ᵐ k ∂uniformOn E, Function.Injective k := by
    simpa only [uniformOn, E, Set.mem_ofPred_eq] using
      (ae_cond_mem (μ := Measure.count) hEfin.measurableSet)
  have hmap (k : Fin m → Fin n) (hk : Function.Injective k) :
      (prefixLaw μ X n).map (fun x : Fin n → α => fun i : Fin m => x (k i)) =
        prefixLaw μ X m := by
    rw [prefixLaw_def, map_blockLaw_reindex μ (fun i : Fin n => i.val) k hX]
    have heq : (fun i : Fin n => i.val) ∘ k = fun i : Fin m => (k i).val := by
      rfl
    rw [heq]
    exact h.blockLaw_eq_prefixLaw_of_injective k hk hX
  apply Measure.ext fun A hA => ?_
  rw [sampleWithoutReplacement_def, samplePopulation_apply hA]
  calc
    ∫⁻ k, prefixLaw μ X n
          ((fun x : Fin n → α => fun i : Fin m => x (k i)) ⁻¹' A) ∂uniformOn E =
        ∫⁻ _k, prefixLaw μ X m A ∂uniformOn E := by
      apply lintegral_congr_ae
      filter_upwards [hae] with k hk
      rw [← Measure.map_apply
        (Measurable.of_eval fun i : Fin m => measurable_pi_apply (k i)) hA, hmap k hk]
    _ = prefixLaw μ X m A := by simp

end Probability

end TauCeti
