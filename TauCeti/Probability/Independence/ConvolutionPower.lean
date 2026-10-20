/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import TauCeti.MeasureTheory.Group.ConvolutionPower

/-!
# Laws of finite sums of independent random variables

This file identifies the law of a finite sum of independent random variables with common law
`μ` as the corresponding convolution power of `μ`.
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

end MeasureTheory.Measure
