/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Independence.InfinitePi
public import TauCeti.MeasureTheory.Group.ConvolutionPower

/-!
# Laws of finite sums of independent random variables

This file identifies the law of a finite sum of independent random variables with common law
`μ` as the corresponding convolution power of `μ`.

An independent natural-valued count gives the mixture of these convolution powers. This is
the random-sum construction underlying compound Poisson laws; the count may have any law,
and zero counts select the empty sum.
-/

public section

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace ProbabilityTheory

variable {Ω ι α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [AddCommMonoid α]
  [MeasurableAdd₂ α] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure α} [IsProbabilityMeasure μ] {X : ι → Ω → α}

/-- A finite sum of independent random variables with common law `μ` has law the corresponding
convolution power of `μ`. -/
theorem iIndepFun.hasLaw_finset_sum_convolutionPower (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) μ P) (s : Finset ι) :
    HasLaw (∑ i ∈ s, X i) (μ.convolutionPower s.card) P := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.card_empty, Measure.convolutionPower_zero]
      exact hasLaw_dirac_of_ae_eq (Filter.Eventually.of_forall fun _ => by simp)
  | @insert i s hi ih =>
      have hindep' : IndepFun (∑ j ∈ s, X j) (X i) P :=
        hindep.indepFun_finsetSum_of_notMem₀ (fun j => (hX j).aemeasurable) hi
      have hsum := IndepFun.hasLaw_add ih (hX i) hindep'
      simpa [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,
        Measure.convolutionPower_succ, add_comm] using hsum

/-- The sum of a finite independent family with common law `μ` has law the convolution power
indexed by the cardinality of the family. -/
theorem iIndepFun.hasLaw_sum_convolutionPower [Fintype ι] (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) μ P) :
    HasLaw (∑ i, X i) (μ.convolutionPower (Fintype.card ι)) P := by
  simpa using hindep.hasLaw_finset_sum_convolutionPower hX Finset.univ

end ProbabilityTheory

namespace MeasureTheory.Measure

/-- The sum of the coordinates of a finite product law has the corresponding convolution law. -/
theorem hasLaw_sum_pi_convolutionPower {α : Type*} [MeasurableSpace α] [AddCommMonoid α]
    [MeasurableAdd₂ α] (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) :
    ProbabilityTheory.HasLaw (fun x : Fin n → α ↦ ∑ i, x i) (μ.convolutionPower n)
      (Measure.pi fun _ ↦ μ) := by
  simpa only [Finset.sum_fn, id_eq, Fintype.card_fin] using
    (ProbabilityTheory.iIndepFun_pi
      (fun _ : Fin n ↦ measurable_id.aemeasurable)).hasLaw_sum_convolutionPower
        (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).hasLaw)

variable {α : Type*} [MeasurableSpace α] [AddCommMonoid α] [MeasurableAdd₂ α]

/-- Summing the coordinates of a finite product of a probability measure gives its convolution
power indexed by the cardinality of the product. This includes the empty product. -/
theorem map_sum_pi_eq_convolutionPower {ι : Type*} [Fintype ι] (μ : Measure α)
    [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : ι ↦ μ).map (fun x ↦ ∑ i, x i) =
      μ.convolutionPower (Fintype.card ι) := by
  have hindep := ProbabilityTheory.iIndepFun_pi (μ := fun _ : ι ↦ μ)
    (X := fun _ ↦ (id : α → α)) (fun _ ↦ aemeasurable_id)
  simpa only [Finset.sum_fn, id_eq] using
    (hindep.hasLaw_sum_convolutionPower fun i ↦
      (measurePreserving_eval (fun _ : ι ↦ μ) i).hasLaw).map_eq

/-- Summing an independent sequence up to a separately drawn natural-valued count gives the
mixture of convolution powers against the count law. No finiteness assumption on that law
or moment assumption on the jumps is required. -/
theorem map_sum_range_prod_infinitePi (ρ : Measure ℕ) (μ : Measure α)
    [IsProbabilityMeasure μ] :
    (ρ.prod (Measure.infinitePi fun _ : ℕ => μ)).map
        (fun z => ∑ i ∈ Finset.range z.1, z.2 i) = ρ.bind μ.convolutionPower := by
  classical
  have hsum : Measurable (fun z : ℕ × (ℕ → α) => ∑ i ∈ Finset.range z.1, z.2 i) :=
    measurable_from_prod_countable_right fun n =>
      Finset.measurable_sum (Finset.range n) fun i _ => measurable_pi_apply i
  rw [prod_eq_of_sfinite, map_bind Measurable.map_prodMk_left.aemeasurable
    hsum.aemeasurable]
  congr 1
  funext n
  rw [map_map hsum measurable_prodMk_left]
  have hindep := ProbabilityTheory.iIndepFun_infinitePi
    (P := fun _ : ℕ => μ) (X := fun _ => (id : α → α)) (fun _ => measurable_id)
  have hlaw := hindep.hasLaw_finset_sum_convolutionPower
    (fun i => (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) i).hasLaw)
    (Finset.range n)
  simpa only [Finset.card_range, Finset.sum_fn, id_eq, Function.comp_def] using hlaw.map_eq

end MeasureTheory.Measure

namespace ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [AddCommMonoid α]
  [MeasurableAdd₂ α] {P : Measure Ω} {μ : Measure α} {ρ : Measure ℕ}
  {X : ℕ → Ω → α} {N : Ω → ℕ}

/-- A random prefix sum of iid jumps has the mixture of convolution powers as its law when
the count is independent of the entire jump sequence. Almost-everywhere measurability of
the jumps suffices. -/
theorem iIndepFun.hasLaw_sum_range_bind (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) μ P) (hN : HasLaw N ρ P)
    (hNX : IndepFun N (fun ω i => X i ω) P) :
    HasLaw (fun ω => ∑ i ∈ Finset.range (N ω), X i ω) (ρ.bind μ.convolutionPower) P := by
  classical
  have := hindep.isProbabilityMeasure
  have := (hX 0).isProbabilityMeasure_iff.mp ‹IsProbabilityMeasure P›
  have hseq : AEMeasurable (fun ω i => X i ω) P :=
    aemeasurable_pi_iff.2 fun i => (hX i).aemeasurable
  have hpair := hNX.hasLaw_prod hN (hindep.hasLaw_infinitePi hX hseq)
  have hsum : Measurable (fun z : ℕ × (ℕ → α) => ∑ i ∈ Finset.range z.1, z.2 i) :=
    measurable_from_prod_countable_right fun n =>
      Finset.measurable_sum (Finset.range n) fun i _ => measurable_pi_apply i
  have hlaw : HasLaw (fun z : ℕ × (ℕ → α) => ∑ i ∈ Finset.range z.1, z.2 i)
      (ρ.bind μ.convolutionPower) (ρ.prod (Measure.infinitePi fun _ : ℕ => μ)) :=
    ⟨hsum.aemeasurable, Measure.map_sum_range_prod_infinitePi ρ μ⟩
  exact hlaw.fun_comp hpair

end ProbabilityTheory
