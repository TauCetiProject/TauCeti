/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Variance
public import TauCeti.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Bounded centered approximations in mean square

`centeredTruncation X P R` keeps `X` on the closed norm ball of radius `R` and subtracts
the integral of the truncated variable. On a probability space it is bounded by `2R` and,
when `X` is almost everywhere strongly measurable, has every finite absolute moment.
Its integral is zero when `P` is a probability measure, `X` is almost everywhere strongly
measurable, and the target space is complete.
For a centered square-integrable variable on a probability space with values in a complete
real inner product space, its mean-square approximation error is bounded by the second moment
outside that ball, and tends to zero as the radius tends to infinity.
These approximations allow moment arguments for bounded variables to be transferred to
variables having only a second moment.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §2.1.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace TauCeti.Probability

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

section Normed

variable [NormedSpace ℝ E] (X : Ω → E) (P : Measure Ω)

/-- Truncate a variable outside a closed norm ball, then subtract its integral
with respect to `P`. -/
def centeredTruncation (R : ℝ≥0) (ω : Ω) : E :=
  {ω | ‖X ω‖ ≤ R}.indicator X ω - ∫ ω, {ω | ‖X ω‖ ≤ R}.indicator X ω ∂P

/-- The defining formula for the bounded centered approximation. -/
theorem centeredTruncation_def (R : ℝ≥0) :
    centeredTruncation X P R = fun ω ↦
      {ω | ‖X ω‖ ≤ R}.indicator X ω - ∫ ω, {ω | ‖X ω‖ ≤ R}.indicator X ω ∂P := (rfl)

variable {X P}

/-- Truncation at radius zero is the zero variable. -/
@[simp] theorem centeredTruncation_zero_radius : centeredTruncation X P 0 = 0 := by
  have h (ω : Ω) : {ω | ‖X ω‖ ≤ (0 : ℝ)}.indicator X ω = 0 := by
    by_cases hn : ‖X ω‖ ≤ 0
    · rw [indicator_of_mem hn]
      exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    · exact indicator_of_notMem hn _
  ext ω
  simp only [centeredTruncation, NNReal.coe_zero, h, integral_zero, sub_self, Pi.zero_apply]

/-- Centered truncation of a measurable variable is measurable. -/
@[fun_prop] theorem _root_.Measurable.centeredTruncation [MeasurableSpace E] [BorelSpace E]
    (hX : Measurable X) (R : ℝ≥0) :
    Measurable (centeredTruncation X P R) :=
  (hX.indicator_setOf_norm_le R).sub_const _

/-- Centered truncation preserves strong measurability almost everywhere. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.centeredTruncation
    (hX : AEStronglyMeasurable X P) (R : ℝ≥0) :
    AEStronglyMeasurable (centeredTruncation X P R) P :=
  (hX.indicator₀ (nullMeasurableSet_le hX.norm.aemeasurable aemeasurable_const)).sub
    aestronglyMeasurable_const

variable [IsProbabilityMeasure P]

/-- Centered truncation has norm at most twice the cutoff, including cutoff zero. -/
theorem norm_centeredTruncation_le (R : ℝ≥0) (ω : Ω) :
    ‖centeredTruncation X P R ω‖ ≤ 2 * R := by
  exact (norm_sub_le _ _).trans (by
    simpa only [two_mul, probReal_univ, mul_one] using
      add_le_add (norm_indicator_setOf_norm_le_le X R.coe_nonneg ω)
      (norm_integral_le_of_norm_le_const (μ := P) (f := {ω | ‖X ω‖ ≤ R}.indicator X)
        (.of_forall (norm_indicator_setOf_norm_le_le X R.coe_nonneg))))

/-- Every finite absolute moment of a centered truncation exists. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.memLp_centeredTruncation
    (hX : AEStronglyMeasurable X P) (R : ℝ≥0)
    {p : ℝ≥0∞} : MemLp (centeredTruncation X P R) p P :=
  (memLp_const (2 * (R : ℝ))).mono' (hX.centeredTruncation R)
    (.of_forall (norm_centeredTruncation_le R))

variable [CompleteSpace E]

/-- The bounded approximation has expectation zero. -/
@[simp] theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_centeredTruncation
    (hX : AEStronglyMeasurable X P) (R : ℝ≥0) :
    ∫ ω, centeredTruncation X P R ω ∂P = 0 := by
  have hi : Integrable ({ω | ‖X ω‖ ≤ R}.indicator X) P :=
    Integrable.of_bound
      (hX.indicator₀ (nullMeasurableSet_le hX.norm.aemeasurable aemeasurable_const))
      R (.of_forall (norm_indicator_setOf_norm_le_le X R.coe_nonneg))
  rw [centeredTruncation_def, integral_sub hi (integrable_const _)]
  simp

omit [IsProbabilityMeasure P] [CompleteSpace E] in
/-- The error after centering and truncating is the discarded part minus its integral. -/
theorem _root_.MeasureTheory.Integrable.sub_integral_sub_centeredTruncation_eq
    (hX : Integrable X P)
    (R : ℝ≥0) (ω : Ω) :
    X ω - (∫ y, X y ∂P) - centeredTruncation X P R ω =
      {y | (R : ℝ) < ‖X y‖}.indicator X ω -
        ∫ y, {y | (R : ℝ) < ‖X y‖}.indicator X y ∂P := by
  have hS := hX.indicator₀ (nullMeasurableSet_le hX.norm.aemeasurable aemeasurable_const
    (f := fun y ↦ ‖X y‖) (g := fun _ ↦ (R : ℝ)))
  have hsplit (y : Ω) :
      X y - {y | ‖X y‖ ≤ R}.indicator X y = {y | (R : ℝ) < ‖X y‖}.indicator X y := by
    simpa only [Set.compl_ofPred, not_le, Pi.sub_apply] using
      congrFun (Set.indicator_compl {y | ‖X y‖ ≤ R} X) y |>.symm
  rw [← hsplit, ← integral_congr_ae (.of_forall hsplit), integral_sub hX hS,
    centeredTruncation_def]
  exact sub_sub_sub_comm ..

omit [CompleteSpace E] in
/-- The mean absolute error of centered truncation is at most twice the discarded norm
integral. -/
theorem _root_.MeasureTheory.Integrable.integral_norm_sub_integral_sub_centeredTruncation_le
    (hX : Integrable X P) (R : ℝ≥0) :
    (∫ ω, ‖X ω - (∫ y, X y ∂P) - centeredTruncation X P R ω‖ ∂P) ≤
      2 * ∫ ω, {y | (R : ℝ) < ‖X y‖}.indicator (fun y ↦ ‖X y‖) ω ∂P := by
  let T := {y | (R : ℝ) < ‖X y‖}.indicator X
  have hT : Integrable T P := hX.indicator₀
    (nullMeasurableSet_lt aemeasurable_const hX.norm.aemeasurable)
  simp_rw [hX.sub_integral_sub_centeredTruncation_eq R]
  calc
    _ ≤ (∫ ω, ‖T ω‖ ∂P) + ‖∫ y, T y ∂P‖ := by
      have hc : Integrable (fun _ : Ω ↦ ∫ y, T y ∂P) P := integrable_const _
      simpa only [sub_eq_add_neg, Pi.neg_apply, norm_neg, integral_const, probReal_univ,
        one_smul] using hT.integral_norm_add_le hc.neg
    _ ≤ 2 * ∫ ω, {y | (R : ℝ) < ‖X y‖}.indicator (fun y ↦ ‖X y‖) ω ∂P := by
      simp_rw [two_mul, ← norm_indicator_eq_indicator_norm]
      unfold T
      exact add_le_add le_rfl (norm_integral_le_integral_norm T)

end Normed

section Hilbert

variable [InnerProductSpace ℝ E] [CompleteSpace E] {X : Ω → E} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- The mean-square error of centered truncation is bounded by the discarded second moment.
No distributional or independence assumption is needed. -/
theorem _root_.MeasureTheory.MemLp.integral_norm_sub_centeredTruncation_sq_le (hX : MemLp X 2 P)
    (hmean : ∫ ω, X ω ∂P = 0) (R : ℝ≥0) :
    ∫ ω, ‖X ω - centeredTruncation X P R ω‖ ^ 2 ∂P ≤
      ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P := by
  let Y := {ω | (R : ℝ) < ‖X ω‖}.indicator X
  have hY : MemLp Y 2 P := hX.indicator
    (nullMeasurableSet_lt aemeasurable_const hX.aestronglyMeasurable.norm.aemeasurable)
  have heq (ω : Ω) : X ω - centeredTruncation X P R ω = Y ω - ∫ y, Y y ∂P := by
    simpa only [hmean, sub_zero] using
      (hX.integrable one_le_two).sub_integral_sub_centeredTruncation_eq R ω
  simp_rw [heq]
  rw [hY.integral_norm_sub_integral_sq]
  refine (sub_le_self _ (sq_nonneg _)).trans_eq (integral_congr_ae (.of_forall fun ω ↦ ?_))
  by_cases h : (R : ℝ) < ‖X ω‖ <;> simp [Y, Set.indicator, h]

/-- The second moment of a centered truncation is bounded by the cutoff times the original
mean norm. -/
theorem _root_.MeasureTheory.Integrable.integral_norm_centeredTruncation_sq_le_mul
    (hX : Integrable X P) (R : ℝ≥0) :
    (∫ ω, ‖centeredTruncation X P R ω‖ ^ 2 ∂P) ≤ (R : ℝ) * ∫ ω, ‖X ω‖ ∂P := by
  let S := {ω | ‖X ω‖ ≤ R}.indicator X
  have hS : MemLp S 2 P := (memLp_const (R : ℝ)).mono'
    (hX.aestronglyMeasurable.indicator₀
      (nullMeasurableSet_le hX.norm.aemeasurable aemeasurable_const))
    (.of_forall (norm_indicator_setOf_norm_le_le X R.coe_nonneg))
  rw [centeredTruncation_def, hS.integral_norm_sub_integral_sq]
  refine (sub_le_self _ (sq_nonneg _)).trans ?_
  rw [← integral_const_mul]
  apply integral_mono ((memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).1 hS)
    (hX.norm.const_mul _)
  intro ω
  simp only [sq]
  exact mul_le_mul (norm_indicator_setOf_norm_le_le X R.coe_nonneg ω)
    (by simp only [S, norm_indicator_eq_indicator_norm]; exact
      Set.indicator_le_self' (fun _ _ ↦ norm_nonneg _) _) (norm_nonneg _) R.coe_nonneg

/-- Centered truncations approximate a centered square-integrable variable in mean square. -/
theorem _root_.MeasureTheory.MemLp.tendsto_integral_norm_sub_centeredTruncation_sq
    (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0) :
    Tendsto (fun R : ℝ≥0 ↦ ∫ ω, ‖X ω - centeredTruncation X P R ω‖ ^ 2 ∂P)
      atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _)
    (hX.integral_norm_sub_centeredTruncation_sq_le hmean)
    hX.tendsto_integral_indicator_norm_sq

/-- The second absolute moments of bounded centered approximations converge to that of
the original centered variable. In particular, unit variance is recovered in the limit. -/
theorem _root_.MeasureTheory.MemLp.tendsto_integral_norm_centeredTruncation_sq (hX : MemLp X 2 P)
    (hmean : ∫ ω, X ω ∂P = 0) :
    Tendsto (fun R : ℝ≥0 ↦ ∫ ω, ‖centeredTruncation X P R ω‖ ^ 2 ∂P)
      atTop (𝓝 (∫ ω, ‖X ω‖ ^ 2 ∂P)) := by
  let hR (R : ℝ≥0) : MemLp (centeredTruncation X P R) 2 P :=
    hX.aestronglyMeasurable.memLp_centeredTruncation R
  have hs : Tendsto (fun R : ℝ≥0 ↦
      ‖hX.toLp X - (hR R).toLp (centeredTruncation X P R)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [← MemLp.toLp_sub, MemLp.norm_toLp_sq, Pi.sub_apply] using
      hX.tendsto_integral_norm_sub_centeredTruncation_sq hmean
  have hn := (Real.continuous_sqrt.tendsto 0).comp hs
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
  have ht : Tendsto (fun R ↦ (hR R).toLp (centeredTruncation X P R)) atTop
      (𝓝 (hX.toLp X)) :=
    tendsto_iff_dist_tendsto_zero.mpr (by simpa only [dist_eq_norm, norm_sub_rev] using hn)
  simpa only [MemLp.norm_toLp_sq] using ht.norm.pow 2

end Hilbert

/-- A weighted sum of centered truncation residuals is integrable, with mean norm bounded by
twice the sum of discarded norm integrals times the coefficient bound. -/
theorem integral_norm_sum_mul_centeredTruncation_residual_le
    {Ω ι 𝕜 : Type*} [MeasurableSpace Ω] [Fintype ι] [RCLike 𝕜]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ι → Ω → ℝ} (hW : ∀ i, Integrable (W i) P) (a : ι → 𝕜)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) (r : ℝ≥0) :
    let D (i : ι) (ω : Ω) :=
      W i ω - (∫ y, W i y ∂P) - centeredTruncation (W i) P r ω
    Integrable (fun ω ↦ ∑ i, a i * (D i ω : 𝕜)) P ∧
      (∫ ω, ‖∑ i, a i * (D i ω : 𝕜)‖ ∂P) ≤ C * (2 * ∑ i,
        ∫ ω, {ω | (r : ℝ) < ‖W i ω‖}.indicator (fun ω ↦ ‖W i ω‖) ω ∂P) := by
  intro D
  have hD (i : ι) : Integrable (fun ω ↦ a i * (D i ω : 𝕜)) P := by
    have hi : Integrable (D i) P := ((hW i).sub (integrable_const _)).sub
      (((hW i).aestronglyMeasurable.memLp_centeredTruncation r).integrable one_le_two)
    exact ((RCLike.ofRealCLM (K := 𝕜)).integrable_comp hi).const_mul _
  have hsum := integrable_finsetSum Finset.univ fun i _ ↦ hD i
  refine ⟨hsum, (integral_mono hsum.norm
    (integrable_finsetSum Finset.univ fun i _ ↦ (hD i).norm) (fun _ ↦ norm_sum_le _ _)).trans ?_⟩
  rw [integral_finsetSum _ (fun i _ ↦ (hD i).norm), ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  simp only [norm_mul, RCLike.norm_ofReal, ← Real.norm_eq_abs, integral_const_mul]
  rw [mul_assoc]
  exact mul_le_mul (ha i) ((hW i).integral_norm_sub_integral_sub_centeredTruncation_le r)
    (integral_nonneg fun ω ↦ norm_nonneg (D i ω)) hC

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]
  {P : Measure Ω} {Q : Measure Ω'} {X : Ω → E} {Y : Ω' → E}

/-- Equal laws preserve the joint law of a variable and its centered truncation.
In particular, approximation errors are identically distributed. -/
theorem IdentDistrib.prodMk_centeredTruncation (h : IdentDistrib X Y P Q) (R : ℝ≥0) :
    IdentDistrib (fun ω ↦ (X ω, centeredTruncation X P R ω))
      (fun ω ↦ (Y ω, centeredTruncation Y Q R ω)) P Q := by
  let T : E → E := {z | ‖z‖ ≤ R}.indicator id
  simp only [centeredTruncation]
  rw [h.integral_indicator_setOf_norm_le_eq R]
  simpa only [Function.comp_def, T,
    Set.indicator_apply, Set.mem_ofPred_eq, id_eq] using
    h.comp (u := fun z ↦ (z, T z - ∫ ω, {ω | ‖Y ω‖ ≤ R}.indicator Y ω ∂Q))
      (measurable_id.prodMk ((measurable_id.indicator_setOf_norm_le R).sub_const _))

/-- Equal laws preserve the law of the error of centered truncation, even for different
source measures. -/
theorem IdentDistrib.sub_centeredTruncation (h : IdentDistrib X Y P Q) (R : ℝ≥0) :
    IdentDistrib (fun ω ↦ X ω - centeredTruncation X P R ω)
      (fun ω ↦ Y ω - centeredTruncation Y Q R ω) P Q := by
  let T : E → E := {z | ‖z‖ ≤ R}.indicator id
  have hg : Measurable (fun z ↦ z - (T z - ∫ ω, {ω | ‖Y ω‖ ≤ R}.indicator Y ω ∂Q)) := by
    -- The error is a constant translate of the discarded tail.
    have hs : MeasurableSet {z : E | (R : ℝ) < ‖z‖} :=
      measurableSet_lt measurable_const measurable_norm
    convert (measurable_id.indicator hs).add_const
      (∫ ω, {ω | ‖Y ω‖ ≤ R}.indicator Y ω ∂Q) using 1
    ext z
    by_cases hz : ‖z‖ ≤ R <;> simp [T, indicator, hz, not_lt.mpr, not_le.mp]
  simp only [centeredTruncation]
  rw [h.integral_indicator_setOf_norm_le_eq R]
  simpa only [Function.comp_def, T, Set.indicator_apply, Set.mem_ofPred_eq, id_eq] using h.comp hg

private theorem exists_measurable_centeredTruncation_eq_comp
    (X : Ω → E) (P : Measure Ω) (R : ℝ≥0) :
    ∃ g : E → E, Measurable g ∧ centeredTruncation X P R = g ∘ X := by
  let g (z : E) := {z | ‖z‖ ≤ R}.indicator id z -
    ∫ ω, {ω | ‖X ω‖ ≤ R}.indicator X ω ∂P
  refine ⟨g, (measurable_id.indicator_setOf_norm_le R).sub_const _, ?_⟩
  ext ω
  simp only [g, centeredTruncation_def, Function.comp_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, id_eq]

/-- Applying centered truncation separately to two independent variables preserves
independence. The cutoffs may differ. -/
theorem IndepFun.centeredTruncation {V : Ω → E} (h : IndepFun X V P) (R S : ℝ≥0) :
    IndepFun (centeredTruncation X P R) (centeredTruncation V P S) P := by
  obtain ⟨f, hf, he⟩ := exists_measurable_centeredTruncation_eq_comp X P R
  obtain ⟨g, hg, he'⟩ := exists_measurable_centeredTruncation_eq_comp V P S
  rw [he, he']
  exact h.comp hf hg

/-- Applying centered truncation separately to independent coordinates preserves independence.
The cutoffs and coordinate laws may differ. -/
theorem iIndepFun.centeredTruncation {ι : Type*} {X : ι → Ω → E}
    (h : iIndepFun X P) (R : ι → ℝ≥0) :
    iIndepFun (fun i ↦ centeredTruncation (X i) P (R i)) P := by
  choose g hg he using fun i ↦ exists_measurable_centeredTruncation_eq_comp (X i) P (R i)
  simpa only [he] using h.comp g hg

end ProbabilityTheory
