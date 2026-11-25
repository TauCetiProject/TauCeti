/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Variance
public import TauCeti.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# Bounded centered approximations in mean square

`centeredTruncation X P R` keeps `X` on the closed norm ball of radius `R` and subtracts
the integral of the truncated variable. It is a measurable function of `X`, so it preserves
independence. On a probability space it is bounded by `2R`. On a finite measure space, when `X`
is almost everywhere strongly measurable, it has every finite absolute moment.
Its integral is zero when `P` is a probability measure and `X` is almost everywhere strongly
measurable.
For a square-integrable variable `X` on a probability space with values in a real inner product
space, the mean-square error of approximating `X - ∫ X` by the centered truncation of `X` is
bounded by the second moment of `X` outside that ball. On a finite measure space with values in
any real normed space, the centered truncations of an `Lᵖ` variable (`1 ≤ p ≤ ∞`) converge in
`Lᵖ` to `X - ∫ X`, so for `p = 2` the mean-square error tends to zero and the second moments of
the approximations converge to that of `X - ∫ X`. When `X` is almost everywhere strongly
measurable but not square-integrable, the displayed squared-error Bochner integral equals zero
at every radius by convention, so the error bound and zero-limit statements still hold formally.
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

/-- On a finite measure space, the centered truncation of an almost everywhere strongly
measurable variable belongs to every `MemLp` space, including `L∞`. -/
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

/-- The bounded approximation has expectation zero. -/
@[simp] theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_centeredTruncation
    (hX : AEStronglyMeasurable X P) (R : ℝ≥0) :
    ∫ ω, centeredTruncation X P R ω ∂P = 0 := by
  by_cases hE : CompleteSpace E
  · have hi : Integrable ({ω | ‖X ω‖ ≤ R}.indicator X) P :=
      Integrable.of_bound
        (hX.indicator₀ (nullMeasurableSet_le hX.norm.aemeasurable aemeasurable_const))
        R (.of_forall (norm_indicator_setOf_norm_le_le X R.coe_nonneg))
    rw [centeredTruncation_def, integral_sub hi (integrable_const _)]
    simp
  · exact integral_of_not_completeSpace hE

omit [IsProbabilityMeasure P] in
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

/-- For a square-integrable variable on a probability space with values in a real inner product
space, centering after norm truncation does not increase the second absolute moment. -/
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

/-- For a square-integrable variable on a probability space with values in a real inner product
space, the centered truncation has absolute moment of order `k+2` bounded by the original second
moment times `(2*R)^k`. -/
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
end Hilbert

end TauCeti.Probability

namespace MeasureTheory

open TauCeti.Probability

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] {X : Ω → E} {P : Measure Ω}

section FiniteMeasure

variable [NormedSpace ℝ E] [IsFiniteMeasure P]

/-- On a finite measure space, let `X` be almost everywhere strongly measurable but not
square-integrable. Then for any constant `c`, the error in approximating `X - c` by the centered
truncation of `X` is outside `L²`, so its squared-norm Bochner integral is `0` by convention. -/
theorem AEStronglyMeasurable.integral_norm_sub_sub_centeredTruncation_sq_eq_zero_of_not_memLp
    (hX : AEStronglyMeasurable X P) (hL : ¬MemLp X 2 P) (c : E) (R : ℝ≥0) :
    ∫ ω, ‖X ω - c - TauCeti.Probability.centeredTruncation X P R ω‖ ^ 2 ∂P = 0 := by
  refine integral_undef fun hi ↦ hL ?_
  have h := (memLp_two_iff_integrable_sq_norm
    (f := fun ω ↦ X ω - c - TauCeti.Probability.centeredTruncation X P R ω)
    ((hX.sub aestronglyMeasurable_const).sub (hX.centeredTruncation R))).2 hi
  convert (h.add (hX.memLp_centeredTruncation R)).add (memLp_const c) using 1
  ext ω
  simp

/-- On a finite measure space, the `Lᵖ` classes of the centered truncations of an `Lᵖ` variable `X`
(`1 ≤ p ≤ ∞`) with values in a real normed space converge in `Lᵖ` to `X - ∫ X` as the cutoff
radius tends to infinity. -/
theorem MemLp.tendsto_toLp_centeredTruncation {p : ℝ≥0∞} [Fact (1 ≤ p)] (hX : MemLp X p P) :
    Tendsto
      (fun R : ℝ≥0 ↦ (hX.aestronglyMeasurable.memLp_centeredTruncation R).toLp
        (TauCeti.Probability.centeredTruncation X P R))
      atTop (𝓝 ((hX.sub (memLp_const _)).toLp (fun ω ↦ X ω - ∫ y, X y ∂P))) := by
  by_cases hp : p = ∞
  · subst hp
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (lpNorm X ∞ P).toNNReal] with R hR
    have hcut : {ω | ‖X ω‖ ≤ (R : ℝ)}.indicator X =ᵐ[P] X := by
      filter_upwards [ae_le_lpNorm_exponent_top hX] with ω hω
      exact indicator_of_mem
        (hω.trans ((Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr hR))) X
    have hEq : TauCeti.Probability.centeredTruncation X P R =ᵐ[P] fun ω ↦ X ω - ∫ y, X y ∂P := by
      rw [centeredTruncation_def, integral_congr_ae hcut]
      exact hcut.mono fun ω hω ↦ by simp only [hω]
    exact (MemLp.toLp_congr _ _ hEq).symm
  · let T (R : ℝ≥0) (ω : Ω) := if ‖X ω‖ ≤ (R : ℝ) then X ω else 0
    have hT (R : ℝ≥0) : MemLp (T R) p P := hX.ite_norm_le R
    have hTlim : Tendsto (fun R : ℝ≥0 ↦ (hT R).toLp (T R)) atTop (𝓝 (hX.toLp X)) := by
      refine TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le hp hT hX.coeFn_toLp
        (fun R ↦ .of_forall fun ω ↦ by dsimp only [T]; split_ifs <;> simp)
        (.of_forall fun ω ↦ tendsto_const_nhds.congr' ?_)
      filter_upwards [eventually_ge_atTop ‖X ω‖₊] with R hR
      simp only [T, ← coe_nnNorm, NNReal.coe_le_coe.mpr hR, ↓reduceIte]
    have hm : Tendsto (fun R : ℝ≥0 ↦ ∫ ω, T R ω ∂P) atTop (𝓝 (∫ ω, X ω ∂P)) :=
      (hX.integrable Fact.out).tendsto_integral_ite_norm_le.comp
        (NNReal.tendsto_coe_atTop.mpr tendsto_id)
    have hconst : Tendsto (fun R : ℝ≥0 ↦ Lp.const p P (∫ ω, T R ω ∂P)) atTop
        (𝓝 (Lp.const p P (∫ ω, X ω ∂P))) := by
      simpa only [Function.comp_def, Lp.constL_apply] using
        ((Lp.constL p P ℝ : E →L[ℝ] Lp E p P).continuous.tendsto _).comp hm
    have hlim := hTlim.sub hconst
    have hrhs : hX.toLp X - Lp.const p P (∫ y, X y ∂P) =
        (hX.sub (memLp_const _)).toLp (fun ω ↦ X ω - ∫ y, X y ∂P) := by
      rw [← MemLp.toLp_const, ← MemLp.toLp_sub]
      rfl
    rw [hrhs] at hlim
    refine hlim.congr fun R ↦ ?_
    rw [← MemLp.toLp_const, ← MemLp.toLp_sub]
    refine MemLp.toLp_congr _ _ (.of_forall fun ω ↦ ?_)
    simp only [Pi.sub_apply, T, centeredTruncation_def, indicator_apply, mem_ofPred_eq]

/-- On a finite measure space, the centered truncations of a square-integrable variable `X` with
values in a real normed space approximate `X - ∫ X` in mean square. When `X` is almost everywhere
strongly measurable but not square-integrable, the displayed squared-error Bochner integral is `0`
at every radius by convention, so the limit still equals `0`. -/
theorem AEStronglyMeasurable.tendsto_integral_norm_sub_integral_sub_centeredTruncation_sq
    (hX' : AEStronglyMeasurable X P) :
    Tendsto (fun R : ℝ≥0 ↦
      ∫ ω, ‖X ω - (∫ y, X y ∂P) - TauCeti.Probability.centeredTruncation X P R ω‖ ^ 2 ∂P)
      atTop (𝓝 0) := by
  by_cases hX : MemLp X 2 P
  swap
  · exact tendsto_const_nhds.congr fun R ↦
      (hX'.integral_norm_sub_sub_centeredTruncation_sq_eq_zero_of_not_memLp hX _ R).symm
  have hdiff := ((tendsto_const_nhds
    (x := (hX.sub (memLp_const _)).toLp (fun ω ↦ X ω - ∫ y, X y ∂P))).sub
    (hX.tendsto_toLp_centeredTruncation (p := 2))).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow two_ne_zero] at hdiff
  simpa only [← MemLp.toLp_sub, MemLp.norm_toLp_sq, Pi.sub_apply] using hdiff

/-- On a finite measure space, the second absolute moments of the bounded centered approximations
of a square-integrable variable `X` with values in a real normed space converge to the second
absolute moment of `X - ∫ X`. -/
theorem MemLp.tendsto_integral_norm_centeredTruncation_sq (hX : MemLp X 2 P) :
    Tendsto (fun R : ℝ≥0 ↦ ∫ ω, ‖centeredTruncation X P R ω‖ ^ 2 ∂P)
      atTop (𝓝 (∫ ω, ‖X ω - ∫ y, X y ∂P‖ ^ 2 ∂P)) :=
  tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub (hX.sub (memLp_const _))
    (fun R ↦ hX.aestronglyMeasurable.memLp_centeredTruncation R)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mp
      (hX.tendsto_toLp_centeredTruncation (p := 2)))

end FiniteMeasure

section Hilbert

variable [InnerProductSpace ℝ E] [IsProbabilityMeasure P]

/-- On a probability space, for a square-integrable variable `X` with values in a real inner
product space, the mean-square error of approximating `X - ∫ X` by the centered truncation of `X`
is bounded by the discarded second moment, with no distributional or independence assumption. When
`X` is almost everywhere strongly measurable but not square-integrable, the displayed squared-error
Bochner integral on the left is `0` by convention, so the inequality still holds. -/
theorem AEStronglyMeasurable.integral_norm_sub_integral_sub_centeredTruncation_sq_le
    (hX' : AEStronglyMeasurable X P) (R : ℝ≥0) :
    ∫ ω, ‖X ω - (∫ y, X y ∂P) - TauCeti.Probability.centeredTruncation X P R ω‖ ^ 2 ∂P ≤
      ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P := by
  by_cases hX : MemLp X 2 P
  swap
  · rw [hX'.integral_norm_sub_sub_centeredTruncation_sq_eq_zero_of_not_memLp hX _ R]
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

/-- Centered truncation is a measurable function of the original variable: truncation outside the
closed ball of radius `R`, followed by subtraction of the truncated mean. -/
theorem _root_.TauCeti.Probability.exists_measurable_comp_eq_centeredTruncation (X : Ω → E)
    (P : Measure Ω) (R : ℝ≥0) : ∃ g : E → E, Measurable g ∧ g ∘ X = centeredTruncation X P R :=
  ⟨_, measurable_centeredTruncationMap R _, centeredTruncationMap_comp X P R⟩

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
