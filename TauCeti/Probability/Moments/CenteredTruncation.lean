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
import TauCeti.Analysis.Normed.Group.Basic

/-!
# Bounded centered approximations in mean square

`centeredTruncation X P R` keeps `X` on the closed norm ball of radius `R` and subtracts
the integral of the truncated variable. On a probability space it is bounded by `2R`. On a
finite measure space, when `X` is almost everywhere strongly measurable, it has every finite
absolute moment.
Its integral is zero when `P` is a probability measure, `X` is almost everywhere strongly
measurable, and the target space is complete.
Let `X` be almost everywhere strongly measurable. On a probability space with values in a real
inner product space, the mean-square error of approximating `X - ∫ X` by the centered truncation
of `X` is bounded by the second moment of `X` outside that ball. On a finite measure space with
values in any real normed space, this mean-square error tends to zero as the radius tends to
infinity. When `X` is moreover square-integrable, the second moments of the approximations
converge to that of `X - ∫ X`.
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

/-- On a finite measure space, every finite absolute moment of a centered truncation exists. -/
theorem _root_.MeasureTheory.AEStronglyMeasurable.memLp_centeredTruncation [IsFiniteMeasure P]
    (hX : AEStronglyMeasurable X P) (R : ℝ≥0)
    {p : ℝ≥0∞} : MemLp (centeredTruncation X P R) p P := by
  rw [centeredTruncation_def]
  exact ((memLp_const (R : ℝ)).mono'
    (hX.indicator₀ (nullMeasurableSet_le hX.norm.aemeasurable aemeasurable_const))
    (.of_forall (norm_indicator_setOf_norm_le_le X R.coe_nonneg))).sub (memLp_const _)

variable [IsProbabilityMeasure P]

/-- Centered truncation has norm at most twice the cutoff, including cutoff zero. -/
theorem norm_centeredTruncation_le (R : ℝ≥0) (ω : Ω) :
    ‖centeredTruncation X P R ω‖ ≤ 2 * R := by
  exact (norm_sub_le _ _).trans (by
    simpa only [two_mul, probReal_univ, mul_one] using
      add_le_add (norm_indicator_setOf_norm_le_le X R.coe_nonneg ω)
      (norm_integral_le_of_norm_le_const (μ := P) (f := {ω | ‖X ω‖ ≤ R}.indicator X)
        (.of_forall (norm_indicator_setOf_norm_le_le X R.coe_nonneg))))

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
/-- Subtracting the centered truncation of `X` from `X - ∫ X` gives the discarded part of
`X` minus its integral, with the cutoff applied to `‖X‖`. -/
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
/-- On a probability space, the mean norm of the difference between `X - ∫ X` and its centered
truncation is at most twice the norm integral over the region where `‖X‖` exceeds the cutoff. -/
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

variable [InnerProductSpace ℝ E] {X : Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]

/-- On a probability space, the second moment of a centered truncation is bounded by the cutoff
times the original mean norm. -/
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

end Hilbert

end TauCeti.Probability

namespace MeasureTheory

open TauCeti.Probability

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {X : Ω → E} {P : Measure Ω}

section FiniteMeasure

variable [NormedSpace ℝ E] [IsFiniteMeasure P]

/-- On a finite measure space, let `X` be almost everywhere strongly measurable but not
square-integrable. Then the mean-square error of its centered truncation, shifted by any constant,
is `0` by convention: the shifted error is not square-integrable either. -/
theorem AEStronglyMeasurable.integral_norm_sub_sub_centeredTruncation_sq_of_not_memLp
    (hX : AEStronglyMeasurable X P) (hL : ¬MemLp X 2 P) (c : E) (R : ℝ≥0) :
    ∫ ω, ‖X ω - c - TauCeti.Probability.centeredTruncation X P R ω‖ ^ 2 ∂P = 0 := by
  refine integral_undef fun hi ↦ hL ?_
  have h := (memLp_two_iff_integrable_sq_norm
    (f := fun ω ↦ X ω - c - TauCeti.Probability.centeredTruncation X P R ω)
    ((hX.sub aestronglyMeasurable_const).sub (hX.centeredTruncation R))).2 hi
  convert (h.add (hX.memLp_centeredTruncation R)).add (memLp_const c) using 1
  ext ω
  simp

/-- On a finite measure space, the centered truncations of an almost everywhere strongly
measurable variable `X` with values in a real normed space approximate `X - ∫ X` in mean square.
When `X` is not square-integrable, every mean-square error is `0` by convention. -/
theorem AEStronglyMeasurable.tendsto_integral_norm_sub_integral_sub_centeredTruncation_sq
    (hX' : AEStronglyMeasurable X P) :
    Tendsto (fun R : ℝ≥0 ↦
      ∫ ω, ‖X ω - (∫ y, X y ∂P) - TauCeti.Probability.centeredTruncation X P R ω‖ ^ 2 ∂P)
      atTop (𝓝 0) := by
  by_cases hX : MemLp X 2 P
  swap
  · exact tendsto_const_nhds.congr fun R ↦
      (hX'.integral_norm_sub_sub_centeredTruncation_sq_of_not_memLp hX _ R).symm
  -- The part of `X` discarded at cutoff `R`, and its norm.
  let Y : ℝ≥0 → Ω → E := fun R ↦ {ω | (R : ℝ) < ‖X ω‖}.indicator X
  let T : ℝ≥0 → Ω → ℝ := fun R ↦ {ω | (R : ℝ) < ‖X ω‖}.indicator fun ω ↦ ‖X ω‖
  have hint (R : ℝ≥0) : Integrable ({ω | (R : ℝ) < ‖X ω‖}.indicator fun ω ↦ ‖X ω‖ ^ 2) P :=
    ((memLp_two_iff_integrable_sq_norm hX').1 hX).indicator₀
      (nullMeasurableSet_lt aestronglyMeasurable_const hX'.norm)
  -- The discarded mean norms tend to zero.
  have hT : Tendsto (fun R ↦ ∫ ω, T R ω ∂P) atTop (𝓝 0) := by
    have h1 : MemLp X 1 P := memLp_one_iff_integrable.2 (hX.integrable one_le_two)
    refine ((h1.tendsto_integral_norm_ite_sub_rpow one_ne_zero ENNReal.one_ne_top).comp
      (NNReal.tendsto_coe_atTop.mpr tendsto_id)).congr
      fun R ↦ integral_congr_ae (.of_forall fun ω ↦ ?_)
    by_cases h : ‖X ω‖ ≤ R <;> simp [T, h, not_lt.mpr, not_le.mp]
  -- Pointwise, the error is `Y - ∫ Y`, so its square is at most `2 (‖Y‖² + (∫ T)²)`.
  have hle (R : ℝ≥0) (ω : Ω) :
      ‖X ω - (∫ y, X y ∂P) - TauCeti.Probability.centeredTruncation X P R ω‖ ^ 2 ≤
      2 * ({ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω + (∫ y, T R y ∂P) ^ 2) := by
    have hY : ‖Y R ω‖ ^ 2 = {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω :=
      (congrFun (indicator_comp_of_zero (g := fun x : E ↦ ‖x‖ ^ 2) (by simp)) ω).symm
    have hm : ‖∫ y, Y R y ∂P‖ ≤ ∫ y, T R y ∂P := (norm_integral_le_integral_norm _).trans_eq
      (integral_congr_ae (.of_forall fun y ↦ norm_indicator_eq_indicator_norm X y))
    calc _ = ‖Y R ω - ∫ y, Y R y ∂P‖ ^ 2 := by
          rw [(hX.integrable one_le_two).sub_integral_sub_centeredTruncation_eq R ω]
      _ ≤ 2 * (‖Y R ω‖ ^ 2 + ‖∫ y, Y R y ∂P‖ ^ 2) := by
          simpa only [sub_zero] using TauCeti.norm_sub_sq_le_two_mul (Y R ω) (∫ y, Y R y ∂P) 0
      _ ≤ _ := by
          rw [hY]
          gcongr
  have hbound (R : ℝ≥0) :
      ∫ ω, ‖X ω - (∫ y, X y ∂P) - TauCeti.Probability.centeredTruncation X P R ω‖ ^ 2 ∂P ≤
      2 * (∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P +
        P.real univ * (∫ y, T R y ∂P) ^ 2) := by
    calc _ ≤ ∫ ω, 2 * ({ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω +
          (∫ y, T R y ∂P) ^ 2) ∂P :=
          integral_mono_of_nonneg (.of_forall fun _ ↦ sq_nonneg _)
            (((hint R).add (integrable_const _)).const_mul 2) (.of_forall (hle R))
      _ = _ := by
          rw [integral_const_mul, integral_add (hint R) (integrable_const _), integral_const,
            smul_eq_mul]
  refine squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ sq_nonneg _) hbound ?_
  simpa using
    (hX.tendsto_integral_indicator_norm_sq.add ((hT.pow 2).const_mul (P.real univ))).const_mul 2

/-- On a finite measure space, the second absolute moments of the bounded centered approximations
of a square-integrable variable `X` with values in a real normed space converge to the second
absolute moment of `X - ∫ X`. -/
theorem MemLp.tendsto_integral_norm_centeredTruncation_sq (hX : MemLp X 2 P) :
    Tendsto (fun R : ℝ≥0 ↦ ∫ ω, ‖centeredTruncation X P R ω‖ ^ 2 ∂P)
      atTop (𝓝 (∫ ω, ‖X ω - ∫ y, X y ∂P‖ ^ 2 ∂P)) := by
  have hc : MemLp (fun ω ↦ X ω - ∫ y, X y ∂P) 2 P := hX.sub (memLp_const _)
  let hR (R : ℝ≥0) : MemLp (centeredTruncation X P R) 2 P :=
    hX.aestronglyMeasurable.memLp_centeredTruncation R
  have hs : Tendsto (fun R : ℝ≥0 ↦
      ‖hc.toLp _ - (hR R).toLp (centeredTruncation X P R)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [← MemLp.toLp_sub, MemLp.norm_toLp_sq, Pi.sub_apply] using
      hX.aestronglyMeasurable.tendsto_integral_norm_sub_integral_sub_centeredTruncation_sq
  have hn := (Real.continuous_sqrt.tendsto 0).comp hs
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
  have ht : Tendsto (fun R ↦ (hR R).toLp (centeredTruncation X P R)) atTop
      (𝓝 (hc.toLp _)) :=
    tendsto_iff_dist_tendsto_zero.mpr (by simpa only [dist_eq_norm, norm_sub_rev] using hn)
  simpa only [MemLp.norm_toLp_sq] using ht.norm.pow 2

end FiniteMeasure

section Hilbert

variable [InnerProductSpace ℝ E] [IsProbabilityMeasure P]

/-- On a probability space, let `X` be almost everywhere strongly measurable with values in a real
inner product space. The mean-square error of approximating `X - ∫ X` by the centered truncation
of `X` is bounded by the discarded second moment. No distributional or independence assumption is
needed. When `X` is not square-integrable, the left side is `0` by convention. -/
theorem AEStronglyMeasurable.integral_norm_sub_integral_sub_centeredTruncation_sq_le
    (hX' : AEStronglyMeasurable X P) (R : ℝ≥0) :
    ∫ ω, ‖X ω - (∫ y, X y ∂P) - TauCeti.Probability.centeredTruncation X P R ω‖ ^ 2 ∂P ≤
      ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P := by
  by_cases hX : MemLp X 2 P
  swap
  · rw [hX'.integral_norm_sub_sub_centeredTruncation_sq_of_not_memLp hX _ R]
    exact integral_nonneg fun ω ↦ indicator_nonneg (fun _ _ ↦ sq_nonneg _) ω
  let Y := {ω | (R : ℝ) < ‖X ω‖}.indicator X
  have hY : MemLp Y 2 P := hX.indicator
    (nullMeasurableSet_lt aestronglyMeasurable_const hX'.norm)
  simp_rw [(hX.integrable one_le_two).sub_integral_sub_centeredTruncation_eq R]
  rw [hY.integral_norm_sub_integral_sq]
  refine (sub_le_self _ (sq_nonneg _)).trans_eq (integral_congr_ae (.of_forall fun ω ↦ ?_))
  exact (congrFun (indicator_comp_of_zero (g := fun x : E ↦ ‖x‖ ^ 2) (by simp)) ω).symm

end Hilbert

end MeasureTheory

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]
  {P : Measure Ω} {Q : Measure Ω'} {X : Ω → E} {Y : Ω' → E}

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Truncate a point outside the closed ball of radius `R` and subtract `m`. With `m` the
integral of the truncated variable, this map composed with the variable is its centered
truncation. -/
private def centeredTruncationMap (R : ℝ≥0) (m : E) (z : E) : E :=
  {z : E | ‖z‖ ≤ R}.indicator id z - m

omit [NormedSpace ℝ E] in
private theorem measurable_centeredTruncationMap (R : ℝ≥0) (m : E) :
    Measurable (centeredTruncationMap R m) :=
  (measurable_id.indicator_setOf_norm_le R).sub_const m

omit [NormedSpace ℝ E] in
/-- The error map is the discarded tail translated by `m`, so it is measurable without
measurability of subtraction on `E`. -/
private theorem measurable_sub_centeredTruncationMap (R : ℝ≥0) (m : E) :
    Measurable fun z ↦ z - centeredTruncationMap R m z := by
  have hs : MeasurableSet {z : E | ‖z‖ ≤ R} := measurableSet_le measurable_norm measurable_const
  have h (z : E) : z - centeredTruncationMap R m z = {z : E | ‖z‖ ≤ R}ᶜ.indicator id z + m := by
    rw [centeredTruncationMap, Set.indicator_compl, Pi.sub_apply, id_eq, sub_sub_eq_add_sub,
      add_sub_right_comm]
  simpa only [h] using (measurable_id.indicator hs.compl).add_const m

omit [MeasurableSpace E] [BorelSpace E] in
private theorem centeredTruncationMap_comp (X : Ω → E) (P : Measure Ω) (R : ℝ≥0) :
    centeredTruncationMap R (∫ ω, {ω | ‖X ω‖ ≤ R}.indicator X ω ∂P) ∘ X =
      centeredTruncation X P R := by
  ext ω
  simp only [centeredTruncationMap, centeredTruncation_def, Function.comp_apply,
    Set.indicator_apply, Set.mem_ofPred_eq, id_eq]

/-- Equal laws preserve the joint law of a variable and its centered truncation.
In particular, approximation errors are identically distributed. -/
theorem IdentDistrib.prodMk_centeredTruncation (h : IdentDistrib X Y P Q) (R : ℝ≥0) :
    IdentDistrib (fun ω ↦ (X ω, centeredTruncation X P R ω))
      (fun ω ↦ (Y ω, centeredTruncation Y Q R ω)) P Q := by
  rw [← centeredTruncationMap_comp X P R, ← centeredTruncationMap_comp Y Q R,
    h.integral_indicator_setOf_norm_le_eq R]
  simpa only [Function.comp_def, id_eq] using
    h.comp (measurable_id.prodMk (measurable_centeredTruncationMap R _))

/-- Equal laws preserve the law of the error of centered truncation, even for different
source measures. -/
theorem IdentDistrib.sub_centeredTruncation (h : IdentDistrib X Y P Q) (R : ℝ≥0) :
    IdentDistrib (fun ω ↦ X ω - centeredTruncation X P R ω)
      (fun ω ↦ Y ω - centeredTruncation Y Q R ω) P Q := by
  rw [← centeredTruncationMap_comp X P R, ← centeredTruncationMap_comp Y Q R,
    h.integral_indicator_setOf_norm_le_eq R]
  simpa only [Function.comp_def] using h.comp (measurable_sub_centeredTruncationMap R _)

/-- Applying centered truncation separately to two independent variables preserves
independence. The cutoffs and target spaces may differ. -/
theorem IndepFun.centeredTruncation {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {V : Ω → F} (h : IndepFun X V P) (R S : ℝ≥0) :
    IndepFun (centeredTruncation X P R) (centeredTruncation V P S) P := by
  rw [← centeredTruncationMap_comp X P R, ← centeredTruncationMap_comp V P S]
  exact h.comp (measurable_centeredTruncationMap R _) (measurable_centeredTruncationMap S _)

/-- Applying centered truncation separately to independent coordinates preserves independence.
The cutoffs, coordinate laws and target spaces may differ. -/
theorem iIndepFun.centeredTruncation {ι : Type*} {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
    [∀ i, BorelSpace (E i)] {X : ∀ i, Ω → E i}
    (h : iIndepFun X P) (R : ι → ℝ≥0) :
    iIndepFun (fun i ↦ centeredTruncation (X i) P (R i)) P := by
  simpa only [centeredTruncationMap_comp] using
    h.comp _ fun i ↦ measurable_centeredTruncationMap (R i)
      (∫ ω, {ω | ‖X i ω‖ ≤ R i}.indicator (X i) ω ∂P)

end ProbabilityTheory
