/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Probability.Distributions.Poisson.Basic
public import TauCeti.Probability.Distributions.Poisson.Measurability

/-!
# Compound Poisson distributions

This file defines convolution powers of a measure on a measurable additive monoid and uses them
as the jump-count kernel of a compound Poisson distribution.  Thus
`compoundPoissonMeasure r μ` first draws a Poisson count of rate `r`, then sums that many
independent jumps with law `μ`.

The core API records addition of convolution powers, preservation of probability, the Poisson
mixture formula, and the two degenerate cases: rate zero and jumps concentrated at zero.  These
facts are the measure-theoretic foundation for later moment and transform calculations.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat MeasureTheory

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [AddMonoid α]

/-- The `n`-fold additive convolution of a measure.  The zeroth power is the point mass at zero. -/
def convolutionPower (μ : Measure α) : ℕ → Measure α
  | 0 => Measure.dirac 0
  | n + 1 => convolutionPower μ n ∗ μ

/-- The zeroth convolution power is the point mass at zero. -/
@[simp]
theorem convolutionPower_zero (μ : Measure α) : μ.convolutionPower 0 = Measure.dirac 0 := (rfl)

/-- A successor convolution power appends one copy of the measure. -/
@[simp]
theorem convolutionPower_succ (μ : Measure α) (n : ℕ) :
    μ.convolutionPower (n + 1) = μ.convolutionPower n ∗ μ := (rfl)

/-- Convolution powers of an s-finite measure are s-finite. -/
instance sfinite_convolutionPower (μ : Measure α) [SFinite μ] (n : ℕ) :
    SFinite (μ.convolutionPower n) := by
  induction n with
  | zero => simp only [convolutionPower_zero]; infer_instance
  | succ n ih => simp only [convolutionPower_succ]; infer_instance

variable [MeasurableAdd₂ α]

/-- The first convolution power is the original measure. -/
@[simp]
theorem convolutionPower_one (μ : Measure α) [SFinite μ] : μ.convolutionPower 1 = μ := by
  rw [convolutionPower_succ, convolutionPower_zero, dirac_zero_conv]

/-- Convolution powers turn addition of exponents into convolution. -/
theorem convolutionPower_add (μ : Measure α) [SFinite μ] (m n : ℕ) :
    μ.convolutionPower (m + n) = μ.convolutionPower m ∗ μ.convolutionPower n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, convolutionPower_succ, convolutionPower_succ, ih, conv_assoc]

/-- Every convolution power of a probability measure is a probability measure. -/
instance isProbabilityMeasure_convolutionPower (μ : Measure α) [IsProbabilityMeasure μ]
    (n : ℕ) : IsProbabilityMeasure (μ.convolutionPower n) := by
  induction n with
  | zero => simp only [convolutionPower_zero]; infer_instance
  | succ n ih => simp only [convolutionPower_succ]; infer_instance

/-- On probability measures, each fixed convolution power depends measurably on the measure. -/
@[fun_prop]
theorem measurable_convolutionPower (n : ℕ) :
    Measurable fun μ : ProbabilityMeasure α => (μ : Measure α).convolutionPower n := by
  induction n with
  | zero => simpa only [convolutionPower_zero] using
      (measurable_const : Measurable fun _ : ProbabilityMeasure α => Measure.dirac (0 : α))
  | succ n ih =>
      have hpow : Measurable fun μ : ProbabilityMeasure α =>
          (⟨(μ : Measure α).convolutionPower n, inferInstance⟩ : ProbabilityMeasure α) :=
        ih.subtype_mk
      have hprod : Measurable fun μ : ProbabilityMeasure α =>
          ((μ : Measure α).convolutionPower n).prod (μ : Measure α) :=
        ProbabilityMeasure.measurable_fun_prod.comp (hpow.prodMk measurable_id)
      simp only [convolutionPower_succ, Measure.conv]
      convert (Measure.measurable_map _ measurable_add).comp hprod using 1
      rfl

/-- Convolution powers of a point mass add its atom repeatedly. -/
theorem convolutionPower_dirac (x : α) (n : ℕ) :
    (Measure.dirac x).convolutionPower n = Measure.dirac (n • x) := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, succ_nsmul]

/-- Every convolution power of the point mass at zero is again concentrated at zero. -/
@[simp]
theorem convolutionPower_dirac_zero (n : ℕ) :
    (Measure.dirac (0 : α)).convolutionPower n = Measure.dirac 0 := by
  simpa using convolutionPower_dirac (α := α) 0 n

/-- A measurable additive homomorphism transports convolution powers to convolution powers of the
pushforward measure. -/
theorem map_convolutionPower {β : Type*} [MeasurableSpace β] [AddMonoid β]
    [MeasurableAdd₂ β] (μ : Measure α) [SFinite μ] (f : α →+ β) (hf : Measurable f)
    (n : ℕ) :
    (μ.convolutionPower n).map f = (μ.map f).convolutionPower n := by
  induction n with
  | zero => simp [Measure.map_dirac' hf]
  | succ n ih =>
      rw [convolutionPower_succ, convolutionPower_succ,
        map_conv_addMonoidHom f hf, ih]

/-- Integration against a successor convolution power is iterated integration against the
preceding power and one further copy of the measure. -/
theorem lintegral_convolutionPower_succ (μ : Measure α) [SFinite μ] (n : ℕ)
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.convolutionPower (n + 1) =
      ∫⁻ x, ∫⁻ y, f (x + y) ∂μ ∂μ.convolutionPower n := by
  rw [convolutionPower_succ, lintegral_conv hf]

end MeasureTheory.Measure

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
      refine ⟨measurable_zero.aemeasurable, ?_⟩
      change P.map (fun _ => (0 : α)) = Measure.dirac 0
      rw [Measure.map_const, measure_univ, one_smul]
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

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [AddMonoid α]

/-- The compound Poisson law with rate `r` and jump measure `μ`: mix the convolution powers of
`μ` against a Poisson-distributed number of jumps. -/
def compoundPoissonMeasure (r : ℝ≥0) (μ : Measure α) : Measure α :=
  (poissonMeasure r).bind μ.convolutionPower

/-- A compound Poisson law is the Poisson mixture of the convolution powers of its jump law. -/
theorem compoundPoissonMeasure_def (r : ℝ≥0) (μ : Measure α) :
    compoundPoissonMeasure r μ = (poissonMeasure r).bind μ.convolutionPower := (rfl)

/-- At a fixed jump measure, the compound Poisson law depends measurably on its rate. -/
@[fun_prop]
theorem measurable_compoundPoissonMeasure (μ : Measure α) :
    Measurable fun r : ℝ≥0 => compoundPoissonMeasure r μ := by
  exact (Measure.measurable_bind' Measurable.of_discrete).comp measurable_poissonMeasure

/-- The compound Poisson law is the Poisson-weighted sum of the convolution powers of its jump
measure. -/
theorem compoundPoissonMeasure_eq_sum (r : ℝ≥0) (μ : Measure α) :
    compoundPoissonMeasure r μ = Measure.sum fun n =>
      ENNReal.ofReal (exp (-r) * r ^ n / n !) • μ.convolutionPower n := by
  rw [compoundPoissonMeasure_def, poissonMeasure, Measure.bind_sum]
  · congr 1
    funext n
    rw [Measure.bind_smul _ _ Measurable.of_discrete.aemeasurable,
      Measure.dirac_bind Measurable.of_discrete]
  · exact Measurable.of_discrete.aemeasurable

/-- A compound Poisson law with a probability jump measure is a probability measure. -/
instance isProbabilityMeasure_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure α)
    [MeasurableAdd₂ α] [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (compoundPoissonMeasure r μ) := by
  rw [compoundPoissonMeasure_def]
  exact MeasureTheory.isProbabilityMeasure_bind Measurable.of_discrete.aemeasurable
    (ae_of_all _ fun n => inferInstance)

/-- Integration against a compound Poisson law is the Poisson average of integration against its
convolution powers. -/
theorem lintegral_compoundPoissonMeasure (r : ℝ≥0) (μ : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂compoundPoissonMeasure r μ =
      ∫⁻ n, ∫⁻ x, f x ∂μ.convolutionPower n ∂poissonMeasure r := by
  rw [compoundPoissonMeasure_def]
  exact Measure.lintegral_bind Measurable.of_discrete.aemeasurable
    hf.aemeasurable

/-- The mass assigned by a compound Poisson law to a measurable set is the Poisson average of
the masses assigned by its convolution powers. -/
theorem compoundPoissonMeasure_apply (r : ℝ≥0) (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) :
    compoundPoissonMeasure r μ s =
      ∫⁻ n, μ.convolutionPower n s ∂poissonMeasure r := by
  rw [compoundPoissonMeasure_def, Measure.bind_apply hs Measurable.of_discrete.aemeasurable]

/-- The measurable-set formula for a compound Poisson law as a Poisson-weighted series. -/
theorem compoundPoissonMeasure_apply_eq_tsum (r : ℝ≥0) (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) :
    compoundPoissonMeasure r μ s =
      ∑' n, ENNReal.ofReal (exp (-r) * r ^ n / n !) * μ.convolutionPower n s := by
  rw [compoundPoissonMeasure_eq_sum, Measure.sum_apply _ hs]
  simp_rw [Measure.smul_apply, smul_eq_mul]

/-- The compound Poisson law is jointly measurable in its rate and probability jump law. -/
@[fun_prop]
theorem measurable_compoundPoissonMeasure_probability [MeasurableAdd₂ α] :
    Measurable fun p : ℝ≥0 × ProbabilityMeasure α =>
      compoundPoissonMeasure p.1 (p.2 : Measure α) := by
  refine Measure.measurable_measure.2 fun s hs => ?_
  simp_rw [compoundPoissonMeasure_apply_eq_tsum _ _ hs]
  refine Measurable.tsum fun n => ?_
  exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul
    ((Measure.measurable_coe hs).comp
      ((Measure.measurable_convolutionPower n).comp measurable_snd))

/-- At rate zero, no jumps occur and the compound Poisson law is concentrated at zero. -/
@[simp]
theorem compoundPoissonMeasure_zero (μ : Measure α) :
    compoundPoissonMeasure 0 μ = Measure.dirac 0 := by
  rw [compoundPoissonMeasure_def, poissonMeasure_zero,
    Measure.dirac_bind Measurable.of_discrete]
  rfl

/-- If every jump is zero, the compound Poisson sum is zero at every rate. -/
@[simp]
theorem compoundPoissonMeasure_dirac_zero [MeasurableAdd₂ α] (r : ℝ≥0) :
    compoundPoissonMeasure r (Measure.dirac (0 : α)) = Measure.dirac 0 := by
  rw [compoundPoissonMeasure_def]
  rw [Measure.bind_congr_right
    (ae_of_all _ fun n => Measure.convolutionPower_dirac_zero (α := α) n)]
  simp

/-- A compound Poisson law with a Dirac jump law is the pushforward of its Poisson count by
repeated addition of the atom. -/
theorem compoundPoissonMeasure_dirac [MeasurableAdd₂ α] (r : ℝ≥0) (x : α) :
    compoundPoissonMeasure r (Measure.dirac x) =
      (poissonMeasure r).map fun n => n • x := by
  rw [compoundPoissonMeasure_def]
  rw [Measure.bind_congr_right
    (ae_of_all _ fun n => Measure.convolutionPower_dirac x n)]
  exact Measure.bind_dirac_eq_map _ Measurable.of_discrete

end TauCeti.Probability
