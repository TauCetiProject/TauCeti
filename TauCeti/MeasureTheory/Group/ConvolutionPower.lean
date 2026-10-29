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
evaluation of a convolution on a measurable set (`conv_apply`), compatibility with countable
sums, half-line mass estimates for convolution and convolution powers on `ℝ≥0`, compatibility of
mixtures of a convolution-additive family with convolution (`bind_conv_bind`), and the
characteristic function of a convolution power (`charFun_convolutionPower`).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal MeasureTheory

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

/-- Evaluation of a convolution on a measurable set: the mass of the translate
`{y | x + y ∈ s}` is integrated against the first measure. -/
theorem conv_apply (μ ν : Measure α) [SFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (μ ∗ ν) s = ∫⁻ x, ν {y | x + y ∈ s} ∂μ := by
  rw [Measure.conv, Measure.map_apply measurable_add hs,
    Measure.prod_apply (hs.preimage measurable_add)]
  -- `prod_apply` leaves the integrand as a double preimage; `Set.preimage_preimage` turns it into
  -- the translate `{y | x + y ∈ s}` of the statement.
  simp only [Set.preimage_preimage]
  rfl

/-- Convolution distributes over countable sums in its second argument:
`μ ∗ ∑ i, ν i = ∑ i, μ ∗ ν i`. -/
theorem conv_sum_right {ι : Type*} [Countable ι] (μ : Measure α) (ν : ι → Measure α)
    [∀ i, SFinite (ν i)] :
    μ ∗ Measure.sum ν = Measure.sum fun i => μ ∗ ν i := by
  simp only [Measure.conv, prod_sum_right, Measure.map_sum measurable_add.aemeasurable]

/-- A convolution charges `[0, t]` at most as much as the product of the masses that its two
factors give to `[0, t]`. -/
theorem conv_Iic_le (μ ν : Measure ℝ≥0) [SFinite ν] (t : ℝ≥0) :
    (μ ∗ ν) (Iic t) ≤ ν (Iic t) * μ (Iic t) := by
  rw [conv_apply μ ν measurableSet_Iic]
  calc ∫⁻ x, ν {y | x + y ∈ Iic t} ∂μ
      ≤ ∫⁻ x, (Iic t).indicator (fun _ => ν (Iic t)) x ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Iic t
        · rw [Set.indicator_of_mem hx]
          refine measure_mono fun y hy => mem_Iic.2 ?_
          exact (le_add_of_nonneg_left zero_le).trans (mem_Iic.1 hy)
        · rw [Set.indicator_of_notMem hx]
          refine le_of_eq (measure_mono_null ?_ (measure_empty (μ := ν)))
          intro y hy
          exact hx (mem_Iic.2 ((le_add_of_nonneg_right zero_le).trans (mem_Iic.1 hy)))
    _ = ν (Iic t) * μ (Iic t) := lintegral_indicator_const measurableSet_Iic _

/-- A convolution charges `[c + d, ∞)` at least as much as the product of the masses that its
two factors give to `[c, ∞)` and `[d, ∞)`. -/
theorem le_conv_Ici (μ ν : Measure ℝ≥0) [SFinite ν] (c d : ℝ≥0) :
    ν (Ici d) * μ (Ici c) ≤ (μ ∗ ν) (Ici (c + d)) := by
  rw [conv_apply μ ν measurableSet_Ici]
  calc ν (Ici d) * μ (Ici c) = ∫⁻ x, (Ici c).indicator (fun _ => ν (Ici d)) x ∂μ :=
        (lintegral_indicator_const measurableSet_Ici _).symm
    _ ≤ ∫⁻ x, ν {y | x + y ∈ Ici (c + d)} ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ Ici c
        · rw [Set.indicator_of_mem hx]
          exact measure_mono fun y hy => mem_Ici.2 (add_le_add hx (mem_Ici.1 hy))
        · rw [Set.indicator_of_notMem hx]
          exact zero_le

/-- If a measure charges the half-line `[a, ∞)`, then its `m`-th convolution power has positive
mass on `[m * a, ∞)`. -/
theorem convolutionPower_Ici_pos {F : Measure ℝ≥0} [SFinite F] {a : ℝ≥0}
    (ha : 0 < F (Ici a)) (m : ℕ) : 0 < F.convolutionPower m (Ici ((m : ℝ≥0) * a)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Measure.convolutionPower_succ, Nat.cast_succ, add_mul, one_mul]
      exact (ENNReal.mul_pos ha.ne' ih.ne').trans_le (le_conv_Ici _ _ _ _)

/-- If a probability measure charges `[a, ∞)` and `m * a > t`, then its `m`-th convolution power
gives `[0, t]` strictly less than full mass. -/
theorem convolutionPower_Iic_lt_one {F : Measure ℝ≥0} [IsProbabilityMeasure F] {a t : ℝ≥0}
    {m : ℕ} (ha : 0 < F (Ici a)) (ht : t < (m : ℝ≥0) * a) :
    F.convolutionPower m (Iic t) < 1 := by
  have hdisj : Disjoint (Iic t) (Ici ((m : ℝ≥0) * a)) :=
    Set.disjoint_left.2 fun x hx hx' => absurd (le_trans hx' (mem_Iic.1 hx)) (not_le.2 ht)
  have hsum : F.convolutionPower m (Iic t) + F.convolutionPower m (Ici ((m : ℝ≥0) * a)) ≤ 1 := by
    rw [← measure_union hdisj measurableSet_Ici, ← measure_univ (μ := F.convolutionPower m)]
    exact measure_mono (subset_univ _)
  have hpos := convolutionPower_Ici_pos ha m
  refine lt_of_lt_of_le (ENNReal.lt_add_right ?_ hpos.ne') hsum
  exact ne_top_of_le_ne_top (by simp) ((le_add_of_nonneg_right zero_le).trans hsum)

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
