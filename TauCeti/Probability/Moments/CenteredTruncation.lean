/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Variance
public import TauCeti.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation

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

/-- Centered truncation is the composition of the original variable with the norm cutoff
and a constant translation on the value space. -/
theorem centeredTruncation_eq_comp (R : ℝ≥0) :
    centeredTruncation X P R =
      (fun z ↦ {z | ‖z‖ ≤ R}.indicator id z - ∫ ω, {ω | ‖X ω‖ ≤ R}.indicator X ω ∂P) ∘ X := by
  funext ω
  rw [centeredTruncation_def, Function.comp_apply,
    ← Set.indicator_comp_right X (g := id), Function.id_comp, Set.preimage_ofPred_eq]

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

/-- On a finite measure space, the error of centered truncation of an `Lᵖ` variable lies in
the same `Lᵖ` space. -/
theorem _root_.MeasureTheory.MemLp.sub_centeredTruncation [IsFiniteMeasure P] {p : ℝ≥0∞}
    (hX : MemLp X p P) (R : ℝ≥0) :
    MemLp (fun ω ↦ X ω - centeredTruncation X P R ω) p P := by
  rw [centeredTruncation_def]
  have hT : MemLp ({ω | ‖X ω‖ ≤ R}.indicator X) p P :=
    hX.indicator (hX.aestronglyMeasurable.norm.nullMeasurableSet_le aestronglyMeasurable_const)
  exact hX.sub (hT.sub (memLp_const _))

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
  refine tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub hX hR ?_
  have he (R : ℝ≥0) : eLpNorm (centeredTruncation X P R - X) 2 P =
      ENNReal.ofReal √(∫ ω, ‖X ω - centeredTruncation X P R ω‖ ^ 2 ∂P) :=
    (eLpNorm_sub_comm _ _ _ _).trans (hX.sub (hR R)).eLpNorm_two_eq_ofReal_sqrt_integral
  simp_rw [he]
  simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] using
    ((ENNReal.continuous_ofReal.comp Real.continuous_sqrt).tendsto 0).comp
      (hX.tendsto_integral_norm_sub_centeredTruncation_sq hmean)

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
  rw [centeredTruncation_eq_comp X P R, centeredTruncation_eq_comp Y Q R,
    h.integral_indicator_setOf_norm_le_eq R]
  exact h.comp (u := fun z ↦ (z, T z - ∫ ω, {ω | ‖Y ω‖ ≤ R}.indicator Y ω ∂Q))
    (measurable_id.prodMk ((measurable_id.indicator_setOf_norm_le R).sub_const _))

/-- Equal laws preserve the law of the error of centered truncation, even for different
source measures. -/
theorem IdentDistrib.sub_centeredTruncation (h : IdentDistrib X Y P Q) (R : ℝ≥0) :
    IdentDistrib (fun ω ↦ X ω - centeredTruncation X P R ω)
      (fun ω ↦ Y ω - centeredTruncation Y Q R ω) P Q := by
  let T : E → E := {z | ‖z‖ ≤ R}.indicator id
  -- Use the discarded tail so that only a constant translation needs to be measurable.
  have htail : Measurable (id - T) := by
    rw [← Set.indicator_compl (s := {z : E | ‖z‖ ≤ R})]
    exact measurable_id.indicator (measurableSet_le measurable_norm measurable_const).compl
  have hg : Measurable (fun z ↦ z - (T z - ∫ ω, {ω | ‖Y ω‖ ≤ R}.indicator Y ω ∂Q)) := by
    simpa only [sub_sub_eq_add_sub, add_sub_right_comm, Pi.sub_apply, id_eq] using htail.add_const
      (∫ ω, {ω | ‖Y ω‖ ≤ R}.indicator Y ω ∂Q)
  rw [centeredTruncation_eq_comp X P R, centeredTruncation_eq_comp Y Q R,
    h.integral_indicator_setOf_norm_le_eq R]
  exact h.comp hg

/-- Applying centered truncation separately to independent coordinates preserves independence.
The cutoffs and coordinate laws may differ. -/
theorem iIndepFun.centeredTruncation {ι : Type*} {X : ι → Ω → E}
    (h : iIndepFun X P) (R : ι → ℝ≥0) :
    iIndepFun (fun i ↦ centeredTruncation (X i) P (R i)) P := by
  let g (i : ι) (z : E) := {z | ‖z‖ ≤ R i}.indicator id z -
    ∫ ω, {ω | ‖X i ω‖ ≤ R i}.indicator (X i) ω ∂P
  have hg (i : ι) : Measurable (g i) :=
    (measurable_id.indicator_setOf_norm_le (R i)).sub_const _
  simp_rw [centeredTruncation_eq_comp]
  exact h.comp g hg

end ProbabilityTheory
