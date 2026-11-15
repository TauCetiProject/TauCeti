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
import TauCeti.Probability.Process.Stopping
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Quadratic variation of continuous real processes on raw filtrations

For a real-valued process `M` on `ℝ≥0` and a filtration `ℱ` under a measure `P`, a process `A` is a
**quadratic variation** of `M` (`TauCeti.Probability.IsQuadraticVariation ℱ P M A`) when `A` is
strongly progressive for `ℱ`, has almost-surely continuous, monotone paths starting at `0`, and
compensates the centered square of `M` in the native local-martingale sense that
`t ↦ M t ω ^ 2 - M 0 ω ^ 2 - A t ω` satisfies `ProbabilityTheory.Locally (Martingale · ℱ P) ℱ · P`.

Working on an unaugmented filtration without usual conditions dictates two design choices:
* Progressivity is required of the compensator `A`, not of `M`, so replacing `A` by an
  indistinguishable strongly progressive process needs no adaptation hypothesis on `M`.
* Uniqueness up to indistinguishability (`IsQuadraticVariation.indist`) requires only a finite
  measure and almost-sure continuity of `M`: subtracting the two compensated squares exhibits
  `A' - A` as a strongly progressive process equal pathwise to the difference of two almost-surely
  continuous native local martingales, so `IsStronglyProgressive.locally_martingale_of_indist_sub`
  and `ProbabilityTheory.Locally.indist_zero_of_locallyBoundedVariationOn` force `A ≡ᵐ[P] A'`
  without assuming `M` is progressive or a local martingale.

Basic operations cover constants, scalar multiplication, negation, initial shifts, countable-range
stopping (with no regularity or measure assumptions), and arbitrary stopping of strongly progressive
almost-surely continuous processes.

## References

* Daniel Revuz and Marc Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Theorem 1.8.
* Ioannis Karatzas and Steven E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

section Defs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `A` is a **quadratic variation** of `M` relative to `(ℱ, P)` if `A` is strongly progressive,
almost surely has continuous, monotone paths starting at `0`, and `M² - M₀² - A` is a native local
martingale on `ℱ`. Neither completeness nor right continuity of `ℱ`, nor progressivity or locality
of `M` itself, is assumed. -/
def IsQuadraticVariation (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (M A : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive ℱ A ∧
    (∀ᵐ ω ∂P, Continuous (fun t ↦ A t ω) ∧ Monotone (fun t ↦ A t ω) ∧ A 0 ω = 0) ∧
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) P

/-- Unfolded characterization of `IsQuadraticVariation`. -/
theorem isQuadraticVariation_def {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
    {M A : ℝ≥0 → Ω → ℝ} :
    IsQuadraticVariation ℱ P M A ↔
      IsStronglyProgressive ℱ A ∧
        (∀ᵐ ω ∂P, Continuous (fun t ↦ A t ω) ∧ Monotone (fun t ↦ A t ω) ∧ A 0 ω = 0) ∧
        Locally (fun Y ↦ Martingale Y ℱ P) ℱ
          (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) P :=
  Iff.rfl

end Defs

namespace IsQuadraticVariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {M M' A A' : ℝ≥0 → Ω → ℝ}

/-- Construct `IsQuadraticVariation` from separate progressivity, pathwise regularity, initial
vanishing, and local-martingale hypotheses. -/
theorem mk (hprog : IsStronglyProgressive ℱ A)
    (hc : ∀ᵐ ω ∂P, Continuous (A · ω)) (hmono : ∀ᵐ ω ∂P, Monotone (A · ω))
    (h0 : A 0 =ᵐ[P] 0)
    (hmart : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) P) :
    IsQuadraticVariation ℱ P M A := by
  refine ⟨hprog, ?_, hmart⟩
  filter_upwards [hc, hmono, h0] with ω hcω hmonoω h0ω
  exact ⟨hcω, hmonoω, h0ω⟩

/-- The quadratic variation compensator is strongly progressive. -/
theorem isStronglyProgressive (h : IsQuadraticVariation ℱ P M A) :
    IsStronglyProgressive ℱ A :=
  h.1

/-- The quadratic variation compensator is strongly adapted. -/
theorem stronglyAdapted (h : IsQuadraticVariation ℱ P M A) :
    StronglyAdapted ℱ A :=
  h.isStronglyProgressive.stronglyAdapted

/-- Almost every sample path of a quadratic variation is continuous. -/
theorem ae_continuous (h : IsQuadraticVariation ℱ P M A) :
    ∀ᵐ ω ∂P, Continuous (A · ω) :=
  h.2.1.mono fun _ hω ↦ hω.1

/-- Almost every sample path of a quadratic variation is monotone. -/
theorem ae_monotone (h : IsQuadraticVariation ℱ P M A) :
    ∀ᵐ ω ∂P, Monotone (A · ω) :=
  h.2.1.mono fun _ hω ↦ hω.2.1

/-- A quadratic variation vanishes at time `0` almost everywhere. -/
theorem ae_apply_zero (h : IsQuadraticVariation ℱ P M A) :
    A 0 =ᵐ[P] 0 :=
  h.2.1.mono fun _ hω ↦ hω.2.2

/-- Almost every sample path of a quadratic variation is nonnegative at all times. -/
theorem ae_nonneg (h : IsQuadraticVariation ℱ P M A) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ A t ω := by
  filter_upwards [h.2.1] with ω ⟨_, hmono, h0⟩ t
  simpa only [h0] using hmono zero_le

/-- Almost every sample path of a quadratic variation has locally bounded variation on `univ`. -/
theorem ae_locallyBoundedVariationOn (h : IsQuadraticVariation ℱ P M A) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (A · ω) univ :=
  h.ae_monotone.mono fun _ hmono ↦ (hmono.monotoneOn univ).locallyBoundedVariationOn

/-- The compensated centered square `M² - M₀² - A` is a native local martingale. -/
theorem locally_martingale (h : IsQuadraticVariation ℱ P M A) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) P :=
  h.2.2

/-- **Uniqueness of continuous quadratic variation.** Under a finite measure, any two quadratic
variations of an almost-surely continuous process `M` on `(ℱ, P)` are indistinguishable. Neither
progressivity nor a local-martingale assumption on `M` is needed. -/
theorem indist [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    (hA' : IsQuadraticVariation ℱ P M A') (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    A ≡ᵐ[P] A' := by
  let X (t : ℝ≥0) (ω : Ω) := (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω
  let Y (t : ℝ≥0) (ω : Ω) := (M t ω) ^ 2 - (M 0 ω) ^ 2 - A' t ω
  have hcX : ∀ᵐ ω ∂P, Continuous (X · ω) :=
    (hcM.and hA.ae_continuous).mono fun _ ⟨hm, ha⟩ ↦
      ((hm.pow 2).sub continuous_const).sub ha
  have hcY : ∀ᵐ ω ∂P, Continuous (Y · ω) :=
    (hcM.and hA'.ae_continuous).mono fun _ ⟨hm, ha⟩ ↦
      ((hm.pow 2).sub continuous_const).sub ha
  have hdiff_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ (A' - A) P :=
    (hA'.isStronglyProgressive.sub hA.isStronglyProgressive).locally_martingale_of_indist_sub
      hA.locally_martingale hA'.locally_martingale hcX hcY
      (.of_forall fun t ω ↦ by dsimp only [X, Y, Pi.sub_apply]; ring)
  have hzero : A' - A ≡ᵐ[P] 0 := hdiff_loc.indist_zero_of_locallyBoundedVariationOn
    ((hA'.ae_continuous.and hA.ae_continuous).mono fun _ h ↦ h.1.sub h.2)
    ((hA'.ae_locallyBoundedVariationOn.and hA.ae_locallyBoundedVariationOn).mono fun _ h ↦
      h.1.sub h.2)
    (by filter_upwards [hA'.ae_apply_zero, hA.ae_apply_zero] with ω h1 h2; simp [h1, h2])
  filter_upwards [hzero] with ω hω t
  exact (sub_eq_zero.1 (hω t)).symm

/-- Replacing the compensator by an indistinguishable strongly progressive process preserves
`IsQuadraticVariation`, with no measurability, regularity, or measure-finiteness hypothesis on `M`
or `P`. -/
theorem congr_right (hA : IsQuadraticVariation ℱ P M A) (hA' : IsStronglyProgressive ℱ A')
    (hAA' : A ≡ᵐ[P] A') : IsQuadraticVariation ℱ P M A' := by
  refine mk hA' ?_ ?_ ?_ ?_
  · filter_upwards [hA.ae_continuous, hAA'] with _ hc hω
    exact hc.congr hω
  · filter_upwards [hA.ae_monotone, hAA'] with _ hm hω s t hst
    simpa only [← hω s, ← hω t] using hm hst
  · filter_upwards [hA.ae_apply_zero, hAA'] with _ h0 hω
    exact (hω 0).symm.trans h0
  · convert hA.locally_martingale.martingale_add_of_indist_zero
        (hA.isStronglyProgressive.sub hA')
        (hAA'.mono fun _ hω t ↦ sub_eq_zero.2 (hω t)) using 1
    ext t ω
    simp only [Pi.add_apply]
    ring

/-- Replacing both `M` and `A` by indistinguishable strongly progressive processes preserves
`IsQuadraticVariation`. -/
theorem congr (hA : IsQuadraticVariation ℱ P M A) (hM' : IsStronglyProgressive ℱ M')
    (hA' : IsStronglyProgressive ℱ A') (hMM' : M ≡ᵐ[P] M') (hAA' : A ≡ᵐ[P] A') :
    IsQuadraticVariation ℱ P M' A' := by
  have hA₁ := hA.congr_right hA' hAA'
  refine mk hA' hA₁.ae_continuous hA₁.ae_monotone hA₁.ae_apply_zero ?_
  have hprog : IsStronglyProgressive ℱ (fun t ω ↦ (M' t ω) ^ 2 - (M' 0 ω) ^ 2 - A' t ω) := by
    have hM'sq : IsStronglyProgressive ℱ (fun t ω ↦ (M' t ω) ^ 2) := by
      simpa only [sq] using hM'.mul hM'
    have hM'0 : IsStronglyProgressive ℱ (fun _ ω ↦ (M' 0 ω) ^ 2) := fun t ↦
      (((hM'.stronglyAdapted 0).pow 2).mono (ℱ.mono bot_le)).comp_measurable measurable_snd
    exact (hM'sq.sub hM'0).sub hA'
  refine hprog.locally_martingale_of_indist hA₁.locally_martingale ?_
  filter_upwards [hMM'] with ω hω t
  simp [hω t, hω 0]

/-- Deterministic scalar multiplication scales the quadratic variation by `c ^ 2`. -/
theorem const_smul (hA : IsQuadraticVariation ℱ P M A) (c : ℝ) :
    IsQuadraticVariation ℱ P (c • M) (c ^ 2 • A) := by
  refine mk (fun t ↦ (hA.isStronglyProgressive t).const_smul (c ^ 2))
    (hA.ae_continuous.mono fun _ hc ↦ continuous_const.mul hc)
    (hA.ae_monotone.mono fun _ hm _ _ hst ↦ mul_le_mul_of_nonneg_left (hm hst) (sq_nonneg c))
    (hA.ae_apply_zero.mono fun _ h0 ↦ by simp [h0]) ?_
  have heq : (fun t ω ↦ ((c • M) t ω) ^ 2 - ((c • M) 0 ω) ^ 2 - (c ^ 2 • A) t ω) =
      fun t ω ↦ c ^ 2 • ((M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω) := by
    ext t ω
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact hA.locally_martingale.martingale_smul (c ^ 2)

/-- Negating the process leaves its quadratic variation unchanged. -/
theorem neg (hA : IsQuadraticVariation ℱ P M A) :
    IsQuadraticVariation ℱ P (-M) A := by
  refine mk hA.isStronglyProgressive hA.ae_continuous hA.ae_monotone hA.ae_apply_zero ?_
  have heq : (fun t ω ↦ ((-M) t ω) ^ 2 - ((-M) 0 ω) ^ 2 - A t ω) =
      fun t ω ↦ (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω := by
    ext t ω
    simp
  rw [heq]
  exact hA.locally_martingale

/-- Shifting a strongly progressive, almost-surely continuous local martingale by an
`ℱ 0`-strongly measurable random variable leaves its quadratic variation unchanged. -/
theorem add_initial [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    (hMprog : IsStronglyProgressive ℱ M)
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω))
    {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsQuadraticVariation ℱ P (fun t ω ↦ M t ω + ξ ω) A := by
  refine mk hA.isStronglyProgressive hA.ae_continuous hA.ae_monotone hA.ae_apply_zero ?_
  let X (t : ℝ≥0) (ω : Ω) := (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω
  let Y (t : ℝ≥0) (ω : Ω) := (2 • ξ) ω • (M t ω - M 0 ω)
  have hMsq : IsStronglyProgressive ℱ (fun t ω ↦ (M t ω) ^ 2) := by
    simpa only [sq] using hMprog.mul hMprog
  have hM0prog : IsStronglyProgressive ℱ (fun _ ω ↦ M 0 ω) := fun t ↦
    ((hMprog.stronglyAdapted 0).mono (ℱ.mono bot_le)).comp_measurable measurable_snd
  have hM0sq : IsStronglyProgressive ℱ (fun _ ω ↦ (M 0 ω) ^ 2) := by
    simpa only [sq] using hM0prog.mul hM0prog
  have hXprog : IsStronglyProgressive ℱ X := (hMsq.sub hM0sq).sub hA.isStronglyProgressive
  have hξprog : IsStronglyProgressive ℱ (fun _ ω ↦ (2 • ξ) ω) := fun t ↦
    ((hξ.const_smul 2).mono (ℱ.mono bot_le)).comp_measurable measurable_snd
  have hYprog : IsStronglyProgressive ℱ Y := hξprog.mul (hMprog.sub hM0prog)
  have hYloc : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P :=
    hM.martingale_sub_initialValue.martingale_smul_initial (hξ.const_smul 2)
  have hcX : ∀ᵐ ω ∂P, Continuous (X · ω) :=
    (hcM.and hA.ae_continuous).mono fun _ ⟨hm, ha⟩ ↦
      ((hm.pow 2).sub continuous_const).sub ha
  have hcY : ∀ᵐ ω ∂P, Continuous (Y · ω) :=
    hcM.mono fun _ hm ↦ continuous_const.mul (hm.sub continuous_const)
  have heq : (fun t ω ↦ (M t ω + ξ ω) ^ 2 - (M 0 ω + ξ ω) ^ 2 - A t ω) = X + Y := by
    ext t ω
    dsimp only [X, Y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact hXprog.locally_martingale_add hYprog hA.locally_martingale hYloc hcX hcY

/-- Centering a strongly progressive, almost-surely continuous local martingale at its initial
value leaves its quadratic variation unchanged. -/
theorem sub_initialValue [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    (hMprog : IsStronglyProgressive ℱ M)
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    IsQuadraticVariation ℱ P (fun t ω ↦ M t ω - M 0 ω) A := by
  simpa only [Pi.neg_apply, ← sub_eq_add_neg] using
    hA.add_initial hMprog hM hcM (hMprog.stronglyAdapted 0).neg

/-- Stopping at a countable-range stopping time preserves `IsQuadraticVariation` under a finite
measure, with no regularity or progressivity assumption on `M`. -/
theorem stoppedProcess_of_countable_range [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (hcτ : (range τ).Countable) :
    IsQuadraticVariation ℱ P (MeasureTheory.stoppedProcess M τ)
      (MeasureTheory.stoppedProcess A τ) := by
  refine mk (hA.isStronglyProgressive.stoppedProcess hτ)
    (hA.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess)
    (hA.ae_monotone.mono fun _ hm ↦ hm.stoppedProcess)
    (hA.ae_apply_zero.mono fun ω h0 ↦
      (congr_fun (stoppedProcess_bot A τ) ω).trans h0) ?_
  let X (t : ℝ≥0) (ω : Ω) := (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω
  have hX : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := hA.locally_martingale
  have heq : (fun t ω ↦ (MeasureTheory.stoppedProcess M τ t ω) ^ 2 -
      (MeasureTheory.stoppedProcess M τ 0 ω) ^ 2 - MeasureTheory.stoppedProcess A τ t ω) =
      MeasureTheory.stoppedProcess X τ := by
    ext t ω
    simp [X, MeasureTheory.stoppedProcess]
  rw [heq]
  refine ⟨hX.localSeq, hX.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  convert (hX.stoppedProcess_localSeq n).stoppedProcess_of_countable_range hτ hcτ using 1
  simp only [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess, inf_comm]

/-- Stopping a strongly progressive, almost-surely continuous process at an arbitrary stopping time
preserves `IsQuadraticVariation` under a finite measure. -/
theorem stoppedProcess [IsFiniteMeasure P] (hA : IsQuadraticVariation ℱ P M A)
    (hMprog : IsStronglyProgressive ℱ M) (hcM : ∀ᵐ ω ∂P, Continuous (M · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsQuadraticVariation ℱ P (MeasureTheory.stoppedProcess M τ)
      (MeasureTheory.stoppedProcess A τ) := by
  refine mk (hA.isStronglyProgressive.stoppedProcess hτ)
    (hA.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess)
    (hA.ae_monotone.mono fun _ hm ↦ hm.stoppedProcess)
    (hA.ae_apply_zero.mono fun ω h0 ↦
      (congr_fun (stoppedProcess_bot A τ) ω).trans h0) ?_
  let X (t : ℝ≥0) (ω : Ω) := (M t ω) ^ 2 - (M 0 ω) ^ 2 - A t ω
  have hMsq : IsStronglyProgressive ℱ (fun t ω ↦ (M t ω) ^ 2) := by
    simpa only [sq] using hMprog.mul hMprog
  have hM0prog : IsStronglyProgressive ℱ (fun _ ω ↦ (M 0 ω) ^ 2) := fun t ↦
    (((hMprog.stronglyAdapted 0).pow 2).mono (ℱ.mono bot_le)).comp_measurable measurable_snd
  have hXprog : IsStronglyProgressive ℱ X := (hMsq.sub hM0prog).sub hA.isStronglyProgressive
  have hcX : ∀ᵐ ω ∂P, IsRightContinuous (X · ω) :=
    (hcM.and hA.ae_continuous).mono fun _ ⟨hm, ha⟩ ↦
      (((hm.pow 2).sub continuous_const).sub ha).isRightContinuous
  have heq : (fun t ω ↦ (MeasureTheory.stoppedProcess M τ t ω) ^ 2 -
      (MeasureTheory.stoppedProcess M τ 0 ω) ^ 2 - MeasureTheory.stoppedProcess A τ t ω) =
      MeasureTheory.stoppedProcess X τ := by
    ext t ω
    simp [X, MeasureTheory.stoppedProcess]
  rw [heq]
  exact hXprog.locally_martingale_stoppedProcess hA.locally_martingale hcX hτ

end IsQuadraticVariation

section Constructors

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)

/-- Any time-independent process (even non-measurable) has quadratic variation `0`. -/
@[simp]
theorem isQuadraticVariation_const (ξ : Ω → ℝ) :
    IsQuadraticVariation ℱ P (fun _ ↦ ξ) 0 := by
  refine IsQuadraticVariation.mk (isStronglyProgressive_const ℱ 0)
    (ae_of_all P fun _ ↦ continuous_const) (ae_of_all P fun _ _ _ _ ↦ le_rfl) .rfl ?_
  have heq : (fun (t : ℝ≥0) ω ↦ (ξ ω) ^ 2 - (ξ ω) ^ 2 - (0 : ℝ≥0 → Ω → ℝ) t ω) = 0 := by
    ext t ω
    simp
  rw [heq]
  exact Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) (martingale_zero ℝ ℱ P)

/-- The zero process has quadratic variation `0`. -/
@[simp]
theorem isQuadraticVariation_zero :
    IsQuadraticVariation ℱ P 0 0 :=
  isQuadraticVariation_const ℱ P 0

/-- Negating the process does not change the `IsQuadraticVariation` predicate. -/
@[simp]
theorem isQuadraticVariation_neg {M A : ℝ≥0 → Ω → ℝ} :
    IsQuadraticVariation ℱ P (-M) A ↔ IsQuadraticVariation ℱ P M A :=
  ⟨fun h ↦ neg_neg M ▸ h.neg, IsQuadraticVariation.neg⟩

end Constructors

end TauCeti.Probability
