/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convolution powers of measures

This file defines the additive convolution powers of a measure on a measurable additive monoid.
It records their algebraic, measure-theoretic, measurability, and integration properties, the
compatibility of mixtures of a convolution-additive family with convolution (`bind_conv_bind`),
and the characteristic function of a convolution power (`charFun_convolutionPower`). It also
shows that convolution distributes over countable sums of measures (`conv_sum`, `sum_conv`), so
that series of convolution powers can be convolved termwise.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

namespace MeasureTheory.Measure

section Sum

variable {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]

/-- Convolution distributes over a countable sum of s-finite measures on the right. -/
@[to_additive /-- Convolution distributes over a countable sum of s-finite measures on the
right. -/]
theorem mconv_sum {ι : Type*} [Countable ι] (μ : Measure M) (ν : ι → Measure M)
    [∀ i, SFinite (ν i)] : μ ∗ₘ Measure.sum ν = Measure.sum fun i ↦ μ ∗ₘ ν i := by
  simp only [mconv, prod_sum_right]
  exact map_sum (by fun_prop)

/-- Convolution distributes over an arbitrary sum of measures on the left. -/
@[to_additive /-- Convolution distributes over an arbitrary sum of measures on the left. -/]
theorem sum_mconv {ι : Type*} (μ : ι → Measure M) (ν : Measure M) [SFinite ν] :
    Measure.sum μ ∗ₘ ν = Measure.sum fun i ↦ μ i ∗ₘ ν := by
  simp only [mconv, prod_sum_left]
  exact map_sum (by fun_prop)

end Sum

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

/-- Convolution powers of a finite measure are finite. -/
instance isFiniteMeasure_convolutionPower (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    IsFiniteMeasure (μ.convolutionPower n) := by
  induction n with
  | zero => simp only [convolutionPower_zero]; infer_instance
  | succ n ih => simp only [convolutionPower_succ]; infer_instance

variable [MeasurableAdd₂ α]

/-- The first convolution power is the original measure. -/
theorem convolutionPower_one (μ : Measure α) [SFinite μ] : μ.convolutionPower 1 = μ := by
  rw [convolutionPower_succ, convolutionPower_zero, dirac_zero_conv]

/-- Every positive convolution power of an absolutely continuous measure is absolutely
continuous with respect to the same left-translation-invariant measure. -/
theorem convolutionPower_succ_absolutelyContinuous {μ ν : Measure α} [SFinite μ]
    [IsAddLeftInvariant ν] (h : μ ≪ ν) (n : ℕ) :
    μ.convolutionPower (n + 1) ≪ ν := by
  rw [convolutionPower_succ]
  exact conv_absolutelyContinuous h

/-- Convolution powers turn addition of exponents into convolution. -/
theorem convolutionPower_add (μ : Measure α) [SFinite μ] (m n : ℕ) :
    μ.convolutionPower (m + n) = μ.convolutionPower m ∗ μ.convolutionPower n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, convolutionPower_succ, convolutionPower_succ, ih, conv_assoc]

/-- Convolution powers also satisfy the recursion `μ^{∗(n + 1)} = μ ∗ μ^{∗n}`. -/
theorem convolutionPower_succ' (μ : Measure α) [SFinite μ] (n : ℕ) :
    μ.convolutionPower (n + 1) = μ ∗ μ.convolutionPower n := by
  rw [Nat.add_comm, convolutionPower_add, convolutionPower_one]

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

/-- Mixing a family of measures indexed by `ℕ` that turns addition into convolution commutes
with convolution: `(ρ.bind K) ∗ (σ.bind K) = (ρ ∗ σ).bind K` when
`K (m + n) = K m ∗ K n`. -/
theorem bind_conv_bind {E : Type*} [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    {K : ℕ → Measure E} [∀ n, SFinite (K n)] (hK : ∀ m n, K (m + n) = K m ∗ K n)
    (ρ σ : Measure ℕ) :
    ρ.bind K ∗ σ.bind K = (ρ ∗ σ).bind K := by
  have hKm : Measurable K := measurable_of_countable K
  have : SFinite (σ.bind K) := by
    rw [← σ.sum_smul_dirac, bind_sum _ _ hKm.aemeasurable]
    simp_rw [bind_smul _ _ hKm.aemeasurable, dirac_bind hKm]
    infer_instance
  refine ext_of_lintegral _ fun f hf => ?_
  have hfx (x : E) : Measurable fun y => f (x + y) := hf.comp (measurable_const_add x)
  have hint : Measurable fun x => ∫⁻ y, f (x + y) ∂σ.bind K :=
    (hf.comp measurable_add).lintegral_prod_right'
  rw [lintegral_conv hf, lintegral_bind hKm.aemeasurable hint.aemeasurable,
    lintegral_bind hKm.aemeasurable hf.aemeasurable, lintegral_conv (by fun_prop)]
  refine lintegral_congr fun m => ?_
  calc ∫⁻ x, ∫⁻ y, f (x + y) ∂σ.bind K ∂K m
      = ∫⁻ x, ∫⁻ n, ∫⁻ y, f (x + y) ∂K n ∂σ ∂K m := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_bind hKm.aemeasurable (hfx x).aemeasurable]
    _ = ∫⁻ n, ∫⁻ x, ∫⁻ y, f (x + y) ∂K n ∂K m ∂σ := by
        refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
        exact measurable_from_prod_countable_left fun n =>
          (hf.comp measurable_add).lintegral_prod_right' (ν := K n)
    _ = ∫⁻ n, ∫⁻ z, f z ∂K (m + n) ∂σ := by
        refine lintegral_congr fun n => ?_
        rw [hK, lintegral_conv hf]

section CharFun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- The characteristic function of the `n`-th convolution power of a finite measure is the
`n`-th power of its characteristic function. -/
@[simp]
theorem charFun_convolutionPower (μ : Measure E) [IsFiniteMeasure μ] (n : ℕ) (t : E) :
    charFun (μ.convolutionPower n) t = charFun μ t ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [convolutionPower_succ, charFun_conv, ih, pow_succ]

end CharFun

end MeasureTheory.Measure
