/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.Local.FiniteVariation
import TauCeti.Probability.Martingale.Local.Centering
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.InitialMultiplier
import TauCeti.Probability.Process.Progressive
import TauCeti.Probability.Process.Stopping

/-!
# Quadratic variation of continuous real processes on raw filtrations

For a real process `M` on `ℝ≥0`, `A` is a **quadratic variation** (`IsQuadraticVariation ℱ P M A`)
when `A` is strongly progressive for `ℱ`, has a.s. continuous, monotone paths starting at `0`, and
compensates `M² - M₀² - A` as a native local martingale (`ProbabilityTheory.Locally`). Uniqueness up
to indistinguishability (`IsQuadraticVariation.indist`) requires only a finite measure and a.s.
continuity of `M`.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 1999, Ch. IV, Thm. 1.8.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., 1991, §1.5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

/-- `A` is a **quadratic variation** of `M` relative to `(ℱ, P)` if `A` is strongly progressive,
a.s. has continuous, monotone paths starting at `0`, and `M² - M₀² - A` is a local martingale. -/
def IsQuadraticVariation {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (M A : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive ℱ A ∧
    (∀ᵐ ω ∂P, Continuous (fun t ↦ A t ω) ∧ Monotone (fun t ↦ A t ω) ∧ A 0 ω = 0) ∧
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) P

/-- Unfolded characterization of `IsQuadraticVariation`. -/
theorem isQuadraticVariation_def {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {M A : ℝ≥0 → Ω → ℝ} :
    IsQuadraticVariation ℱ P M A ↔ IsStronglyProgressive ℱ A ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ A t ω) ∧ Monotone (fun t ↦ A t ω) ∧ A 0 ω = 0) ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) P :=
  Iff.rfl

namespace IsQuadraticVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {M M' A A' : ℝ≥0 → Ω → ℝ}

/-- Construct `IsQuadraticVariation` from progressivity, path, and martingale hypotheses. -/
theorem mk (hprog : IsStronglyProgressive ℱ A) (hc : ∀ᵐ ω ∂P, Continuous (A · ω))
    (hmono : ∀ᵐ ω ∂P, Monotone (A · ω)) (h0 : A 0 =ᵐ[P] 0)
    (hmart : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) P) : IsQuadraticVariation ℱ P M A := by
  refine ⟨hprog, ?_, hmart⟩
  filter_upwards [hc, hmono, h0] with _ hcω hmonoω h0ω using ⟨hcω, hmonoω, h0ω⟩

/-- The quadratic variation compensator is strongly progressive. -/
theorem isStronglyProgressive (h : IsQuadraticVariation ℱ P M A) : IsStronglyProgressive ℱ A := h.1

/-- The quadratic variation compensator is strongly adapted. -/
theorem stronglyAdapted (h : IsQuadraticVariation ℱ P M A) : StronglyAdapted ℱ A :=
  h.isStronglyProgressive.stronglyAdapted

/-- Almost every sample path of a quadratic variation is continuous. -/
theorem ae_continuous (h : IsQuadraticVariation ℱ P M A) : ∀ᵐ ω ∂P, Continuous (A · ω) :=
  h.2.1.mono fun _ hω ↦ hω.1

/-- Almost every sample path of a quadratic variation is monotone. -/
theorem ae_monotone (h : IsQuadraticVariation ℱ P M A) : ∀ᵐ ω ∂P, Monotone (A · ω) :=
  h.2.1.mono fun _ hω ↦ hω.2.1

/-- A quadratic variation vanishes at time `0` almost everywhere. -/
theorem ae_apply_zero (h : IsQuadraticVariation ℱ P M A) : A 0 =ᵐ[P] 0 :=
  h.2.1.mono fun _ hω ↦ hω.2.2

/-- Almost every sample path of a quadratic variation is nonnegative at all times. -/
theorem ae_nonneg (h : IsQuadraticVariation ℱ P M A) : ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω := by
  filter_upwards [h.2.1] with _ ⟨_, hmono, h0⟩ _ using by simpa only [h0] using hmono zero_le

/-- Almost every sample path of a quadratic variation has locally bounded variation on `univ`. -/
theorem ae_locallyBoundedVariationOn (h : IsQuadraticVariation ℱ P M A) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (A · ω) univ :=
  h.ae_monotone.mono fun _ hmono ↦ (hmono.monotoneOn univ).locallyBoundedVariationOn

/-- The compensated centered square `M² - M₀² - A` is a native local martingale. -/
theorem locally_martingale (h : IsQuadraticVariation ℱ P M A) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) P := h.2.2

/-- **Uniqueness of continuous quadratic variation** under a finite measure. -/
theorem indist [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    (hA' : IsQuadraticVariation ℱ P M A') (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) : A ≡ᵐ[P] A' :=
  hA.locally_martingale.indist_sub_right_of_locallyBoundedVariationOn
    (X := fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2)
    hA'.locally_martingale hA.isStronglyProgressive hA'.isStronglyProgressive
    (hcM.mono fun _ hm ↦ (hm.pow 2).sub continuous_const) hA.ae_continuous hA'.ae_continuous
    hA.ae_locallyBoundedVariationOn hA'.ae_locallyBoundedVariationOn
    (hA.ae_apply_zero.trans hA'.ae_apply_zero.symm)

/-- Replacing the compensator by an indistinguishable strongly progressive process preserves
`IsQuadraticVariation`. -/
theorem congr_right (hA : IsQuadraticVariation ℱ P M A) (hA' : IsStronglyProgressive ℱ A')
    (hAA' : A ≡ᵐ[P] A') : IsQuadraticVariation ℱ P M A' :=
  mk hA' ((hA.ae_continuous.and hAA').mono fun _ h ↦ h.1.congr h.2)
    (by filter_upwards [hA.ae_monotone, hAA'] with _ hm hω s t hst
        simpa only [← hω s, ← hω t] using hm hst)
    ((hAA'.ae_eq_eval 0).symm.trans hA.ae_apply_zero)
    (hA.locally_martingale.martingale_sub_of_indist_right
      (X := fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2) hA.isStronglyProgressive hA' hAA')

/-- Replacing `M` and `A` by indistinguishable strongly progressive processes preserves
`IsQuadraticVariation`. -/
theorem congr (hA : IsQuadraticVariation ℱ P M A) (hM' : IsStronglyProgressive ℱ M')
    (hA' : IsStronglyProgressive ℱ A') (hMM' : M ≡ᵐ[P] M') (hAA' : A ≡ᵐ[P] A') :
    IsQuadraticVariation ℱ P M' A' := by
  have hA₁ := hA.congr_right hA' hAA'
  exact mk hA' hA₁.ae_continuous hA₁.ae_monotone hA₁.ae_apply_zero
    (((hM'.pow 2).sub_initialValue.sub hA').locally_martingale_of_indist hA₁.locally_martingale
      (hMM'.mono fun _ hω t ↦ by simp [hω t, hω 0]))

/-- Deterministic scalar multiplication scales the quadratic variation by `c ^ 2`. -/
theorem const_smul (hA : IsQuadraticVariation ℱ P M A) (c : ℝ) :
    IsQuadraticVariation ℱ P (c • M) (c ^ 2 • A) := by
  refine mk (fun t ↦ (hA.isStronglyProgressive t).const_smul (c ^ 2))
    (hA.ae_continuous.mono fun _ hc ↦ continuous_const.mul hc)
    (hA.ae_monotone.mono fun _ hm _ _ hst ↦ mul_le_mul_of_nonneg_left (hm hst) (sq_nonneg c))
    (hA.ae_apply_zero.mono fun _ h0 ↦ by simp [h0]) ?_
  convert hA.locally_martingale.martingale_smul (c ^ 2) using 1
  ext; simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Negating the process leaves its quadratic variation unchanged. -/
theorem neg (hA : IsQuadraticVariation ℱ P M A) : IsQuadraticVariation ℱ P (-M) A := by
  refine mk hA.isStronglyProgressive hA.ae_continuous hA.ae_monotone hA.ae_apply_zero ?_
  convert hA.locally_martingale using 1; ext; simp

/-- Shifting a strongly progressive, a.s. continuous local martingale by an `ℱ 0`-strongly
measurable random variable leaves its quadratic variation unchanged. -/
theorem add_initial [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    (hMprog : IsStronglyProgressive ℱ M) (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsQuadraticVariation ℱ P (fun t ω ↦ M t ω + ξ ω) A := by
  refine mk hA.isStronglyProgressive hA.ae_continuous hA.ae_monotone hA.ae_apply_zero ?_
  have hYprog : IsStronglyProgressive ℱ (fun t ω ↦ (2 • ξ) ω • (M t ω - M 0 ω)) :=
    ((hξ.const_smul 2).isStronglyProgressive_const).mul hMprog.sub_initialValue
  convert ((hMprog.pow 2).sub_initialValue.sub hA.isStronglyProgressive).locally_martingale_add
    hYprog hA.locally_martingale
    (hM.martingale_sub_initialValue.martingale_smul_initial (hξ.const_smul 2))
    ((hcM.and hA.ae_continuous).mono fun _ h ↦ ((h.1.pow 2).sub continuous_const).sub h.2)
    (hcM.mono fun _ hm ↦ continuous_const.mul (hm.sub continuous_const)) using 1
  ext; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, bot_eq_zero]; ring

/-- Centering a strongly progressive, a.s. continuous local martingale at its initial value leaves
its quadratic variation unchanged. -/
theorem sub_initialValue [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    (hMprog : IsStronglyProgressive ℱ M) (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) : IsQuadraticVariation ℱ P (fun t ω ↦ M t ω - M 0 ω) A := by
  simpa only [Pi.neg_apply, ← sub_eq_add_neg] using
    hA.add_initial hMprog hM hcM (hMprog.stronglyAdapted 0).neg

/-- Stopping at a countable-range stopping time preserves `IsQuadraticVariation`. -/
theorem stoppedProcess_of_countable_range [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (hcτ : (range τ).Countable) :
    IsQuadraticVariation ℱ P (MeasureTheory.stoppedProcess M τ)
      (MeasureTheory.stoppedProcess A τ) := by
  refine mk (hA.isStronglyProgressive.stoppedProcess hτ)
    (hA.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess)
    (hA.ae_monotone.mono fun _ hm ↦ hm.stoppedProcess)
    (hA.ae_apply_zero.mono fun ω h0 ↦ (congr_fun (stoppedProcess_bot A τ) ω).trans h0) ?_
  have hX := hA.locally_martingale
  have hstop : (fun t ω ↦ (MeasureTheory.stoppedProcess M τ t ω) ^ 2 -
      (MeasureTheory.stoppedProcess M τ 0 ω) ^ 2 - MeasureTheory.stoppedProcess A τ t ω) =
      MeasureTheory.stoppedProcess (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) τ := by
    ext; simp [MeasureTheory.stoppedProcess]
  rw [hstop]; refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  convert (hX.stoppedProcess_localSeq n).stoppedProcess_of_countable_range hτ hcτ using 1
  simp only [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess, inf_comm]

/-- Stopping a strongly progressive, a.s. continuous process at a stopping time preserves
`IsQuadraticVariation`. -/
theorem stoppedProcess [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    (hMprog : IsStronglyProgressive ℱ M) (hcM : ∀ᵐ ω ∂P, Continuous (M · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsQuadraticVariation ℱ P (MeasureTheory.stoppedProcess M τ)
      (MeasureTheory.stoppedProcess A τ) := by
  refine mk (hA.isStronglyProgressive.stoppedProcess hτ)
    (hA.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess)
    (hA.ae_monotone.mono fun _ hm ↦ hm.stoppedProcess)
    (hA.ae_apply_zero.mono fun ω h0 ↦ (congr_fun (stoppedProcess_bot A τ) ω).trans h0) ?_
  convert ((hMprog.pow 2).sub_initialValue.sub
    hA.isStronglyProgressive).locally_martingale_stoppedProcess hA.locally_martingale
    ((hcM.and hA.ae_continuous).mono fun _ h ↦
      (((h.1.pow 2).sub continuous_const).sub h.2).isRightContinuous) hτ using 1
  ext; simp [MeasureTheory.stoppedProcess]

end IsQuadraticVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)

/-- Any time-independent process (even non-measurable) has quadratic variation `0`. -/
@[simp] theorem isQuadraticVariation_const (ξ : Ω → ℝ) :
    IsQuadraticVariation ℱ P (fun _ ↦ ξ) 0 := by
  refine IsQuadraticVariation.mk (isStronglyProgressive_const ℱ 0)
    (ae_of_all P fun _ ↦ continuous_const) (ae_of_all P fun _ _ _ _ ↦ le_rfl) .rfl ?_
  convert Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) (martingale_zero ℝ ℱ P) using 1; ext; simp

/-- The zero process has quadratic variation `0`. -/
@[simp] theorem isQuadraticVariation_zero : IsQuadraticVariation ℱ P 0 0 :=
  isQuadraticVariation_const ℱ P 0

/-- Negating the process does not change the `IsQuadraticVariation` predicate. -/
@[simp] theorem isQuadraticVariation_neg {M A : ℝ≥0 → Ω → ℝ} :
    IsQuadraticVariation ℱ P (-M) A ↔ IsQuadraticVariation ℱ P M A :=
  ⟨fun h ↦ neg_neg M ▸ h.neg, IsQuadraticVariation.neg⟩

end TauCeti.Probability
