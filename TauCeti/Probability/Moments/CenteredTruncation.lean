/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Variance
public import TauCeti.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

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

end Normed

section TruncationMean

variable [NormedSpace ℝ E] {X : Ω → E} {P : Measure Ω} [IsFiniteMeasure P]

/-- For a centered variable, the norm of its truncated mean is bounded by the absolute
moment of order `k+1` divided by the `k`-th power of the cutoff. -/
theorem _root_.MeasureTheory.MemLp.norm_integral_indicator_norm_le_of_integral_eq_zero
    {k : ℕ} (hX : MemLp X (↑(k + 1 : ℕ)) P) (hmean : ∫ ω, X ω ∂P = 0) {r : ℝ} (hr : 0 < r) :
    ‖∫ ω, {ω' | ‖X ω'‖ ≤ r}.indicator X ω ∂P‖ ≤
      (∫ ω, ‖X ω‖ ^ (k + 1) ∂P) / r ^ k := by
  have hint := hX.integrable (by exact_mod_cast Nat.succ_pos k)
  let S := {ω | r < ‖X ω‖}
  have hS : NullMeasurableSet S P :=
    nullMeasurableSet_lt aemeasurable_const hX.aestronglyMeasurable.norm.aemeasurable
  have hsplit : (∫ ω, Sᶜ.indicator X ω ∂P) = -(∫ ω, S.indicator X ω ∂P) := by
    rw [integral_indicator₀ hS.compl, integral_indicator₀ hS,
      setIntegral_compl₀ hS hint, hmean, zero_sub]
  have hcomp : Sᶜ = {ω | ‖X ω‖ ≤ r} := by ext ω; simp [S]
  rw [← hcomp, hsplit, norm_neg, ← integral_div]
  refine norm_integral_le_of_norm_le
    ((hX.integrable_norm_pow (Nat.succ_ne_zero k)).div_const _) (.of_forall fun ω ↦ ?_)
  by_cases hω : ω ∈ S
  · rw [indicator_of_mem hω, le_div_iff₀ (pow_pos hr _), pow_succ, mul_comm]
    simp only [S, Set.mem_ofPred_eq] at hω
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hω.le _) (norm_nonneg _)
  · rw [indicator_of_notMem hω, norm_zero]
    positivity

/-- The weighted truncated mean tends to zero when the weight divided by the
cutoff to the power `k` tends to zero and the centered variable has moment `k + 1`. -/
theorem _root_.MeasureTheory.MemLp.tendsto_mul_norm_integral_indicator_norm_le_nhds_zero
    {k : ℕ} (hX : MemLp X (↑(k + 1 : ℕ)) P) (hmean : ∫ ω, X ω ∂P = 0)
    {ι : Type*} {l : Filter ι} {R w : ι → ℝ} (hR : ∀ i, 0 < R i) (hw : ∀ i, 0 ≤ w i)
    (hlim : Tendsto (fun i ↦ w i / R i ^ k) l (𝓝 0)) :
    Tendsto (fun i ↦ w i * ‖∫ ω, {ω' | ‖X ω'‖ ≤ R i}.indicator X ω ∂P‖) l (𝓝 0) := by
  let C := ∫ ω, ‖X ω‖ ^ (k + 1) ∂P
  refine squeeze_zero (fun i ↦ mul_nonneg (hw i) (norm_nonneg _)) (fun i ↦ ?_)
    (by simpa only [mul_zero] using hlim.const_mul C)
  calc
    _ ≤ w i * (C / R i ^ k) :=
      mul_le_mul_of_nonneg_left
        (hX.norm_integral_indicator_norm_le_of_integral_eq_zero hmean (hR i)) (hw i)
    _ = C * (w i / R i ^ k) := by rw [mul_div_left_comm, ← mul_div_assoc]

end TruncationMean

section Hilbert

variable [InnerProductSpace ℝ E] [CompleteSpace E] {X : Ω → E} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- The mean-square error of centered truncation is bounded by the discarded second moment.
No distributional or independence assumption is needed. -/
theorem _root_.MeasureTheory.MemLp.integral_norm_sub_centeredTruncation_sq_le (hX : MemLp X 2 P)
    (hmean : ∫ ω, X ω ∂P = 0) (R : ℝ≥0) :
    ∫ ω, ‖X ω - centeredTruncation X P R ω‖ ^ 2 ∂P ≤
      ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P := by
  let T := {ω | ‖X ω‖ ≤ R}.indicator X
  let Y := fun ω ↦ X ω - T ω
  have hT : MemLp T 2 P := hX.indicator
    (nullMeasurableSet_le hX.aestronglyMeasurable.norm.aemeasurable aemeasurable_const)
  have hY : MemLp Y 2 P := hX.sub hT
  have hm : ∫ ω, Y ω ∂P = -(∫ ω, T ω ∂P) := by
    rw [integral_sub (hX.integrable one_le_two) (hT.integrable one_le_two), hmean, zero_sub]
  have heq (ω : Ω) : X ω - centeredTruncation X P R ω =
      Y ω - ∫ ω, Y ω ∂P := by
    simp only [hm, centeredTruncation, Y, T]
    abel
  simp_rw [heq]
  rw [hY.integral_norm_sub_integral_sq]
  calc
    _ ≤ ∫ ω, ‖Y ω‖ ^ 2 ∂P := sub_le_self _ (sq_nonneg _)
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun ω ↦ by
        by_cases h : ‖X ω‖ ≤ R <;> simp [Y, T, indicator, h, not_lt.mpr, not_le.mp]

/-- Centering after norm truncation does not increase the second absolute moment. -/
theorem _root_.MeasureTheory.MemLp.integral_norm_centeredTruncation_sq_le
    (hX : MemLp X 2 P) (R : ℝ≥0) :
    ∫ ω, ‖centeredTruncation X P R ω‖ ^ 2 ∂P ≤ ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  let S := {ω | ‖X ω‖ ≤ R}
  let T := S.indicator X
  have hT : MemLp T 2 P := hX.indicator
    (nullMeasurableSet_le hX.aestronglyMeasurable.norm.aemeasurable aemeasurable_const)
  have hnorm (ω : Ω) : ‖T ω‖ ≤ ‖X ω‖ := norm_indicator_le_norm_self X ω
  rw [centeredTruncation_def, hT.integral_norm_sub_integral_sq]
  refine (sub_le_self _ (sq_nonneg _)).trans ?_
  exact integral_mono (hT.integrable_norm_pow (by decide)) (hX.integrable_norm_pow (by decide))
    fun ω ↦ pow_le_pow_left₀ (norm_nonneg _) (hnorm ω) _

/-- Higher absolute moments of the centered truncation are bounded by the original second
moment times the corresponding power of the uniform bound `2*R`. -/
theorem _root_.MeasureTheory.MemLp.integral_norm_centeredTruncation_pow_le
    (hX : MemLp X 2 P) (R : ℝ≥0) (k : ℕ) :
    ∫ ω, ‖centeredTruncation X P R ω‖ ^ (k + 2) ∂P ≤
      (2 * (R : ℝ)) ^ k * ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  have hR (p : ℕ) : MemLp (centeredTruncation X P R) p P :=
    hX.aestronglyMeasurable.memLp_centeredTruncation R
  calc
    _ ≤ ∫ ω, (2 * (R : ℝ)) ^ k * ‖centeredTruncation X P R ω‖ ^ 2 ∂P := by
      refine integral_mono (hR _).integrable_norm_pow'
        ((hR 2).integrable_norm_pow'.const_mul _) fun ω ↦ ?_
      rw [pow_add]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (norm_centeredTruncation_le R ω) _) (sq_nonneg _)
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hX.integral_norm_centeredTruncation_sq_le R) (by positivity)

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

/-- Applying centered truncation separately to independent coordinates preserves independence.
The cutoffs and coordinate laws may differ. -/
theorem iIndepFun.centeredTruncation {ι : Type*} {X : ι → Ω → E}
    (h : iIndepFun X P) (R : ι → ℝ≥0) :
    iIndepFun (fun i ↦ centeredTruncation (X i) P (R i)) P := by
  let g (i : ι) (z : E) := {z | ‖z‖ ≤ R i}.indicator id z -
    ∫ ω, {ω | ‖X i ω‖ ≤ R i}.indicator (X i) ω ∂P
  have hg (i : ι) : Measurable (g i) :=
    (measurable_id.indicator_setOf_norm_le (R i)).sub_const _
  simpa only [Function.comp_def, g, centeredTruncation_def, Set.indicator_apply,
    Set.mem_ofPred_eq, id_eq]
    using h.comp g hg

end ProbabilityTheory
