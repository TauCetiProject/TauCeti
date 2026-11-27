/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.QuadraticVariation.Basic
import Mathlib.Analysis.Normed.MulAction
import TauCeti.Probability.Martingale.Local.Centering
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.InitialMultiplier
import TauCeti.Probability.Process.ContinuousAE
import TauCeti.Probability.Process.Progressive
import TauCeti.Probability.Process.Stopping
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Mutual variation (covariation) of continuous real processes on raw filtrations

For real processes `M` and `N` on `ℝ≥0`, `C` is a **covariation** (`IsCovariation ℱ P M N C`) when
`C` is strongly progressive for `ℱ`, has a.s. continuous paths of locally bounded variation starting
at `0`, and compensates `M * N - M₀ * N₀ - C` as a native local martingale. Includes uniqueness
(`IsCovariation.indist`), diagonal correspondence, polarization, bilinearity, stopping, and
orthogonality.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., 1999, Ch. IV, §1.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., 1991, §1.5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

/-- `C` is a **covariation** of `M` and `N` relative to `(ℱ, P)` if `C` is strongly progressive,
a.s. has continuous locally bounded-variation paths starting at `0`, and `M * N - M₀ * N₀ - C` is
a native local martingale. -/
def IsCovariation {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (M N C : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive ℱ C ∧
    (∀ᵐ ω ∂P, Continuous (fun t ↦ C t ω) ∧
      LocallyBoundedVariationOn (fun t ↦ C t ω) univ ∧ C 0 ω = 0) ∧
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) P

/-- Unfolded characterization of `IsCovariation`. -/
theorem isCovariation_def {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} {M N C : ℝ≥0 → Ω → ℝ} :
    IsCovariation ℱ P M N C ↔ IsStronglyProgressive ℱ C ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ C t ω) ∧
        LocallyBoundedVariationOn (fun t ↦ C t ω) univ ∧ C 0 ω = 0) ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ
        (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) P :=
  Iff.rfl

/-- Every quadratic variation of `M` is also a self-covariation `[M, M]`. -/
theorem IsQuadraticVariation.isCovariation_self {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} {M A : ℝ≥0 → Ω → ℝ}
    (hA : IsQuadraticVariation ℱ P M A) : IsCovariation ℱ P M M A := by
  refine ⟨hA.isStronglyProgressive, ?_, ?_⟩
  · filter_upwards [hA.ae_continuous, hA.ae_locallyBoundedVariationOn, hA.ae_apply_zero]
      with _ hc hbv h0 using ⟨hc, hbv, h0⟩
  · convert hA.locally_martingale using 1; ext; ring

private theorem ae_continuous_mul_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M N C : ℝ≥0 → Ω → ℝ} (hcM : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hcN : ∀ᵐ ω ∂P, Continuous (N · ω)) (hcC : ∀ᵐ ω ∂P, Continuous (C · ω)) :
    ∀ᵐ ω ∂P, Continuous (fun t ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) := by
  filter_upwards [hcM, hcN, hcC] with _ hm hn hc using ((hm.mul hn).sub continuous_const).sub hc

namespace IsCovariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {M M₁ M₂ M' N N₁ N₂ N' C C₁ C₂ C' : ℝ≥0 → Ω → ℝ}

/-- Construct `IsCovariation` from separate progressivity, path, and martingale hypotheses. -/
theorem mk (hprog : IsStronglyProgressive ℱ C) (hc : ∀ᵐ ω ∂P, Continuous (C · ω))
    (hbv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (C · ω) univ) (h0 : C 0 =ᵐ[P] 0)
    (hmart : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) P) : IsCovariation ℱ P M N C := by
  refine ⟨hprog, ?_, hmart⟩
  filter_upwards [hc, hbv, h0] with _ hcω hbvω h0ω using ⟨hcω, hbvω, h0ω⟩

/-- The covariation compensator is strongly progressive. -/
theorem isStronglyProgressive (h : IsCovariation ℱ P M N C) : IsStronglyProgressive ℱ C := h.1

/-- The covariation compensator is strongly adapted. -/
theorem stronglyAdapted (h : IsCovariation ℱ P M N C) : StronglyAdapted ℱ C :=
  h.isStronglyProgressive.stronglyAdapted

/-- Almost every sample path of a covariation is continuous. -/
theorem ae_continuous (h : IsCovariation ℱ P M N C) : ∀ᵐ ω ∂P, Continuous (C · ω) :=
  h.2.1.mono fun _ hω ↦ hω.1

/-- Almost every sample path of a covariation has locally bounded variation on `univ`. -/
theorem ae_locallyBoundedVariationOn (h : IsCovariation ℱ P M N C) :
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (C · ω) univ := h.2.1.mono fun _ hω ↦ hω.2.1

/-- A covariation vanishes at time `0` almost everywhere. -/
theorem ae_apply_zero (h : IsCovariation ℱ P M N C) : C 0 =ᵐ[P] 0 := h.2.1.mono fun _ hω ↦ hω.2.2

/-- The compensated centered product `M * N - M₀ * N₀ - C` is a native local martingale. -/
theorem locally_martingale (h : IsCovariation ℱ P M N C) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) P := h.2.2

/-- **Uniqueness of continuous covariation** under a finite measure for a.s. continuous `M, N`. -/
theorem indist [IsFiniteMeasure P] (hC : IsCovariation ℱ P M N C) (hC' : IsCovariation ℱ P M N C')
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω)) : C ≡ᵐ[P] C' :=
  hC.locally_martingale.indist_sub_right_of_locallyBoundedVariationOn
    (X := fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω)
    hC'.locally_martingale hC.isStronglyProgressive hC'.isStronglyProgressive
    ((hcM.and hcN).mono fun _ h ↦ (h.1.mul h.2).sub continuous_const) hC.ae_continuous
    hC'.ae_continuous hC.ae_locallyBoundedVariationOn hC'.ae_locallyBoundedVariationOn
    (hC.ae_apply_zero.trans hC'.ae_apply_zero.symm)

/-- Covariation is symmetric in its two process arguments. -/
theorem symm (h : IsCovariation ℱ P M N C) : IsCovariation ℱ P N M C := by
  refine mk h.isStronglyProgressive h.ae_continuous h.ae_locallyBoundedVariationOn
    h.ae_apply_zero ?_
  convert h.locally_martingale using 1; ext; ring

/-- Replacing the compensator by an indistinguishable strongly progressive process preserves
`IsCovariation`. -/
theorem congr_right (hC : IsCovariation ℱ P M N C) (hC' : IsStronglyProgressive ℱ C')
    (hCC' : C ≡ᵐ[P] C') : IsCovariation ℱ P M N C' :=
  mk hC' ((hC.ae_continuous.and hCC').mono fun _ h ↦ h.1.congr h.2)
    ((hC.ae_locallyBoundedVariationOn.and hCC').mono fun _ h ↦ h.1.congr fun t _ ↦ h.2 t)
    ((hCC'.ae_eq_eval 0).symm.trans hC.ae_apply_zero)
    (hC.locally_martingale.martingale_sub_of_indist_right
      (X := fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω) hC.isStronglyProgressive hC' hCC')

/-- Replacing `M`, `N`, and `C` by indistinguishable strongly progressive processes preserves
`IsCovariation`. -/
theorem congr (hC : IsCovariation ℱ P M N C)
    (hM' : IsStronglyProgressive ℱ M') (hN' : IsStronglyProgressive ℱ N')
    (hC' : IsStronglyProgressive ℱ C') (hMM' : M ≡ᵐ[P] M') (hNN' : N ≡ᵐ[P] N')
    (hCC' : C ≡ᵐ[P] C') : IsCovariation ℱ P M' N' C' := by
  have hC₁ := hC.congr_right hC' hCC'
  refine mk hC' hC₁.ae_continuous hC₁.ae_locallyBoundedVariationOn hC₁.ae_apply_zero
    (((hM'.mul hN').sub_initialValue.sub hC').locally_martingale_of_indist
      hC₁.locally_martingale ?_)
  filter_upwards [hMM', hNN'] with _ hm hn t using by simp [hm t, hm 0, hn t, hn 0]

/-- Every self-covariation `[M, M]` with a.s. monotone paths is a quadratic variation. -/
theorem isQuadraticVariation_of_ae_monotone {A : ℝ≥0 → Ω → ℝ}
    (hC : IsCovariation ℱ P M M A) (hmono : ∀ᵐ ω ∂P, Monotone (A · ω)) :
    IsQuadraticVariation ℱ P M A := by
  refine IsQuadraticVariation.mk hC.isStronglyProgressive hC.ae_continuous hmono hC.ae_apply_zero ?_
  convert hC.locally_martingale using 1; ext; ring

/-- If an a.s. continuous process `M` admits a quadratic variation under a finite measure, then
every self-covariation `[M, M]` is a quadratic variation of `M`. -/
theorem isQuadraticVariation_of_exists [IsFiniteMeasure P] {A : ℝ≥0 → Ω → ℝ}
    (hC : IsCovariation ℱ P M M A) (hcM : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hex : ∃ Q, IsQuadraticVariation ℱ P M Q) : IsQuadraticVariation ℱ P M A :=
  let ⟨_, hQ⟩ := hex
  hQ.congr_right hC.isStronglyProgressive (hQ.isCovariation_self.indist hC hcM hcM)

/-- Left scalar multiplication scales the covariation by `c`. -/
theorem const_smul_left (h : IsCovariation ℱ P M N C) (c : ℝ) :
    IsCovariation ℱ P (c • M) N (c • C) := by
  refine mk (fun t ↦ (h.isStronglyProgressive t).const_smul c)
    (h.ae_continuous.mono fun _ hc ↦ continuous_const.mul hc)
    (h.ae_locallyBoundedVariationOn.mono fun _ ↦
      (lipschitzWith_smul c).comp_locallyBoundedVariationOn)
    (h.ae_apply_zero.mono fun _ h0 ↦ by simp [h0]) ?_
  convert h.locally_martingale.martingale_smul c using 1; ext; simp [smul_eq_mul]; ring

/-- Right scalar multiplication scales the covariation by `c`. -/
theorem const_smul_right (h : IsCovariation ℱ P M N C) (c : ℝ) :
    IsCovariation ℱ P M (c • N) (c • C) := (h.symm.const_smul_left c).symm

/-- Negating the left process negates the covariation. -/
theorem neg_left (h : IsCovariation ℱ P M N C) : IsCovariation ℱ P (-M) N (-C) := by
  simpa only [neg_one_smul] using h.const_smul_left (-1)

/-- Negating the right process negates the covariation. -/
theorem neg_right (h : IsCovariation ℱ P M N C) : IsCovariation ℱ P M (-N) (-C) :=
  h.symm.neg_left.symm

/-- Left additivity of covariation for strongly progressive, a.s. continuous processes. -/
theorem add_left [IsFiniteMeasure P] (h₁ : IsCovariation ℱ P M₁ N C₁)
    (h₂ : IsCovariation ℱ P M₂ N C₂) (hM₁ : IsStronglyProgressive ℱ M₁)
    (hM₂ : IsStronglyProgressive ℱ M₂) (hN : IsStronglyProgressive ℱ N)
    (hcM₁ : ∀ᵐ ω ∂P, Continuous (M₁ · ω)) (hcM₂ : ∀ᵐ ω ∂P, Continuous (M₂ · ω))
    (hcN : ∀ᵐ ω ∂P, Continuous (N · ω)) : IsCovariation ℱ P (M₁ + M₂) N (C₁ + C₂) := by
  refine mk (h₁.isStronglyProgressive.add h₂.isStronglyProgressive)
    ((h₁.ae_continuous.and h₂.ae_continuous).mono fun _ h ↦ h.1.add h.2)
    ((h₁.ae_locallyBoundedVariationOn.and h₂.ae_locallyBoundedVariationOn).mono fun _ h ↦
      h.1.add h.2)
    (by filter_upwards [h₁.ae_apply_zero, h₂.ae_apply_zero] with _ ha hb; simp [ha, hb]) ?_
  convert ((hM₁.mul hN).sub_initialValue.sub h₁.isStronglyProgressive).locally_martingale_add
    ((hM₂.mul hN).sub_initialValue.sub h₂.isStronglyProgressive)
    h₁.locally_martingale h₂.locally_martingale (ae_continuous_mul_sub hcM₁ hcN h₁.ae_continuous)
    (ae_continuous_mul_sub hcM₂ hcN h₂.ae_continuous) using 1
  ext; simp only [Pi.add_apply, bot_eq_zero]; ring

/-- Right additivity of covariation for strongly progressive, a.s. continuous processes. -/
theorem add_right [IsFiniteMeasure P] (h₁ : IsCovariation ℱ P M N₁ C₁)
    (h₂ : IsCovariation ℱ P M N₂ C₂) (hM : IsStronglyProgressive ℱ M)
    (hN₁ : IsStronglyProgressive ℱ N₁) (hN₂ : IsStronglyProgressive ℱ N₂)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN₁ : ∀ᵐ ω ∂P, Continuous (N₁ · ω))
    (hcN₂ : ∀ᵐ ω ∂P, Continuous (N₂ · ω)) : IsCovariation ℱ P M (N₁ + N₂) (C₁ + C₂) :=
  (h₁.symm.add_left h₂.symm hN₁ hN₂ hM hcN₁ hcN₂ hcM).symm

/-- Left subtractivity of covariation. -/
theorem sub_left [IsFiniteMeasure P] (h₁ : IsCovariation ℱ P M₁ N C₁)
    (h₂ : IsCovariation ℱ P M₂ N C₂) (hM₁ : IsStronglyProgressive ℱ M₁)
    (hM₂ : IsStronglyProgressive ℱ M₂) (hN : IsStronglyProgressive ℱ N)
    (hcM₁ : ∀ᵐ ω ∂P, Continuous (M₁ · ω)) (hcM₂ : ∀ᵐ ω ∂P, Continuous (M₂ · ω))
    (hcN : ∀ᵐ ω ∂P, Continuous (N · ω)) : IsCovariation ℱ P (M₁ - M₂) N (C₁ - C₂) := by
  simpa only [sub_eq_add_neg] using
    h₁.add_left h₂.neg_left hM₁ hM₂.neg hN hcM₁ (hcM₂.mono fun _ h ↦ h.neg) hcN

/-- Right subtractivity of covariation. -/
theorem sub_right [IsFiniteMeasure P] (h₁ : IsCovariation ℱ P M N₁ C₁)
    (h₂ : IsCovariation ℱ P M N₂ C₂) (hM : IsStronglyProgressive ℱ M)
    (hN₁ : IsStronglyProgressive ℱ N₁) (hN₂ : IsStronglyProgressive ℱ N₂)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN₁ : ∀ᵐ ω ∂P, Continuous (N₁ · ω))
    (hcN₂ : ∀ᵐ ω ∂P, Continuous (N₂ · ω)) : IsCovariation ℱ P M (N₁ - N₂) (C₁ - C₂) :=
  (h₁.symm.sub_left h₂.symm hN₁ hN₂ hM hcN₁ hcN₂ hcM).symm

/-- Stopping strongly progressive, a.s. continuous processes at a stopping time preserves
`IsCovariation`. -/
theorem stoppedProcess [IsFiniteMeasure P] (hC : IsCovariation ℱ P M N C)
    (hMprog : IsStronglyProgressive ℱ M) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsCovariation ℱ P (MeasureTheory.stoppedProcess M τ) (MeasureTheory.stoppedProcess N τ)
      (MeasureTheory.stoppedProcess C τ) := by
  refine mk (hC.isStronglyProgressive.stoppedProcess hτ)
    (hC.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess)
    (hC.ae_locallyBoundedVariationOn.mono fun _ hbv ↦ hbv.stoppedProcess_univ)
    (hC.ae_apply_zero.mono fun ω h0 ↦ (congr_fun (stoppedProcess_bot C τ) ω).trans h0) ?_
  convert ((hMprog.mul hNprog).sub_initialValue.sub
    hC.isStronglyProgressive).locally_martingale_stoppedProcess hC.locally_martingale
    ((ae_continuous_mul_sub hcM hcN hC.ae_continuous).mono fun _ h ↦ h.isRightContinuous)
    hτ using 1
  ext; simp [MeasureTheory.stoppedProcess]

end IsCovariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- Symmetry of `IsCovariation` as an equivalence. -/
theorem isCovariation_comm {M N C : ℝ≥0 → Ω → ℝ} :
    IsCovariation ℱ P M N C ↔ IsCovariation ℱ P N M C := ⟨IsCovariation.symm, IsCovariation.symm⟩

/-- The zero process has covariation `0` on the left with any process. -/
@[simp] theorem isCovariation_zero_left (N : ℝ≥0 → Ω → ℝ) : IsCovariation ℱ P 0 N 0 := by
  refine IsCovariation.mk (isStronglyProgressive_const ℱ 0) (ae_of_all P fun _ ↦ continuous_const)
    (ae_of_all P fun _ ↦ locallyBoundedVariationOn_const 0 univ) .rfl ?_
  convert Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) (martingale_zero ℝ ℱ P) using 1; ext; simp

/-- The zero process has covariation `0` on the right with any process. -/
@[simp] theorem isCovariation_zero_right (M : ℝ≥0 → Ω → ℝ) : IsCovariation ℱ P M 0 0 :=
  (isCovariation_zero_left M).symm

/-- An `ℱ 0`-strongly measurable constant process has zero covariation with any local martingale. -/
theorem isCovariation_const_left [SigmaFiniteFiltration P ℱ] {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ 0] ξ) {N : ℝ≥0 → Ω → ℝ}
    (hN : Locally (fun Y ↦ Martingale Y ℱ P) ℱ N P) : IsCovariation ℱ P (fun _ ↦ ξ) N 0 := by
  refine IsCovariation.mk (isStronglyProgressive_const ℱ 0) (ae_of_all P fun _ ↦ continuous_const)
    (ae_of_all P fun _ ↦ locallyBoundedVariationOn_const 0 univ) .rfl ?_
  convert hN.martingale_sub_initialValue.martingale_smul_initial hξ using 1
  ext; simp only [Pi.zero_apply, sub_zero, smul_eq_mul, bot_eq_zero]; ring

/-- Any local martingale has zero covariation on the right with an `ℱ 0`-measurable constant. -/
theorem isCovariation_const_right [SigmaFiniteFiltration P ℱ] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsCovariation ℱ P M (fun _ ↦ ξ) 0 := (isCovariation_const_left hξ hM).symm

private theorem mk_smul_sub [IsFiniteMeasure P] {M N Y F G : ℝ≥0 → Ω → ℝ} (c : ℝ)
    (hMprog : IsStronglyProgressive ℱ M) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hF : IsQuadraticVariation ℱ P (M + N) F) (hGprog : IsStronglyProgressive ℱ G)
    (hcG : ∀ᵐ ω ∂P, Continuous (G · ω)) (hbvG : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (G · ω) univ)
    (h0G : G 0 =ᵐ[P] 0) (hmY : Locally (fun U ↦ Martingale U ℱ P) ℱ Y P)
    (hcY : ∀ᵐ ω ∂P, Continuous (Y · ω))
    (halg : ∀ t ω, M t ω * N t ω - M 0 ω * N 0 ω - c * (F t ω - G t ω) =
      c * (((M + N) t ω) ^ 2 - ((M + N) 0 ω) ^ 2 - F t ω) - c * Y t ω) :
    IsCovariation ℱ P M N (c • (F - G)) := by
  have hprog : IsStronglyProgressive ℱ (c • (F - G)) :=
    fun t ↦ ((hF.isStronglyProgressive.sub hGprog) t).const_smul c
  refine IsCovariation.mk hprog
    ((hF.ae_continuous.and hcG).mono fun _ h ↦ continuous_const.mul (h.1.sub h.2))
    ((hF.ae_locallyBoundedVariationOn.and hbvG).mono fun _ h ↦
      (lipschitzWith_smul c).comp_locallyBoundedVariationOn (h.1.sub h.2))
    (by filter_upwards [hF.ae_apply_zero, h0G] with _ ha hb; simp [ha, hb])
    (((hMprog.mul hNprog).sub_initialValue.sub hprog).locally_martingale_of_indist_sub
      (hF.locally_martingale.martingale_smul c) (hmY.martingale_smul c)
      (by filter_upwards [hcM, hcN, hF.ae_continuous] with _ hm hn hf
          exact continuous_const.mul ((((hm.add hn).pow 2).sub continuous_const).sub hf))
      (hcY.mono fun _ h ↦ continuous_const.mul h)
      (.of_forall fun ω t ↦ by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, bot_eq_zero]; exact halg t ω))

/-- **Polarization identity** `4⁻¹ • ([M + N] - [M - N])`. -/
theorem isCovariation_of_isQuadraticVariation_add_sub [IsFiniteMeasure P]
    {M N Apos Aneg : ℝ≥0 → Ω → ℝ}
    (hMprog : IsStronglyProgressive ℱ M) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hadd : IsQuadraticVariation ℱ P (M + N) Apos) (hsub : IsQuadraticVariation ℱ P (M - N) Aneg) :
    IsCovariation ℱ P M N ((4⁻¹ : ℝ) • (Apos - Aneg)) :=
  mk_smul_sub (4⁻¹ : ℝ) hMprog hNprog hcM hcN hadd hsub.isStronglyProgressive hsub.ae_continuous
    hsub.ae_locallyBoundedVariationOn hsub.ae_apply_zero hsub.locally_martingale
    (by filter_upwards [hcM, hcN, hsub.ae_continuous] with _ hm hn ha
        exact (((hm.sub hn).pow 2).sub continuous_const).sub ha)
    fun _ _ ↦ by dsimp only [Pi.add_apply, Pi.sub_apply]; ring

/-- **Polarization identity** `2⁻¹ • ([M + N] - [M] - [N])`. -/
theorem isCovariation_of_isQuadraticVariation_add [IsFiniteMeasure P]
    {M N A B D : ℝ≥0 → Ω → ℝ}
    (hMprog : IsStronglyProgressive ℱ M) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hA : IsQuadraticVariation ℱ P M A) (hB : IsQuadraticVariation ℱ P N B)
    (hD : IsQuadraticVariation ℱ P (M + N) D) :
    IsCovariation ℱ P M N ((2⁻¹ : ℝ) • (D - A - B)) := by
  have hcA := ae_continuous_mul_sub hcM hcM hA.ae_continuous
  have hcB := ae_continuous_mul_sub hcN hcN hB.ae_continuous
  have hbvAB := (hA.ae_locallyBoundedVariationOn.and hB.ae_locallyBoundedVariationOn).mono
    fun _ h ↦ h.1.add h.2
  simpa only [sub_sub] using mk_smul_sub (G := A + B) (2⁻¹ : ℝ) hMprog hNprog hcM hcN hD
    (fun t ↦ (hA.isStronglyProgressive t).add (hB.isStronglyProgressive t))
    ((hA.ae_continuous.and hB.ae_continuous).mono fun _ h ↦ h.1.add h.2) hbvAB
    (by filter_upwards [hA.ae_apply_zero, hB.ae_apply_zero] with _ ha hb; simp [ha, hb])
    (((hMprog.mul hMprog).sub_initialValue.sub hA.isStronglyProgressive).locally_martingale_add
      ((hNprog.mul hNprog).sub_initialValue.sub hB.isStronglyProgressive)
      hA.isCovariation_self.locally_martingale hB.isCovariation_self.locally_martingale hcA hcB)
    ((hcA.and hcB).mono fun _ h ↦ h.1.add h.2) fun _ _ ↦ by
      simp only [Pi.add_apply, bot_eq_zero]; ring

/-- Finite left linearity of covariation. -/
theorem isCovariation_sum_left [IsFiniteMeasure P] {ι : Type*} (s : Finset ι)
    {M C : ι → ℝ≥0 → Ω → ℝ} {N : ℝ≥0 → Ω → ℝ}
    (hMprog : ∀ i ∈ s, IsStronglyProgressive ℱ (M i)) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ i ∈ s, ∀ᵐ ω ∂P, Continuous (M i · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hC : ∀ i ∈ s, IsCovariation ℱ P (M i) N (C i)) :
    IsCovariation ℱ P (fun t ω ↦ ∑ i ∈ s, M i t ω) N (fun t ω ↦ ∑ i ∈ s, C i t ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => convert isCovariation_zero_left N using 1 <;> (ext; simp)
  | insert a s ha ih =>
    convert (hC a (Finset.mem_insert_self a s)).add_left
      (ih (fun i hi ↦ hMprog i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hcM i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hC i (Finset.mem_insert_of_mem hi)))
      (hMprog a (Finset.mem_insert_self a s))
      (IsStronglyProgressive.finsetSum fun i hi ↦ hMprog i (Finset.mem_insert_of_mem hi)) hNprog
      (hcM a (Finset.mem_insert_self a s))
      (s.ae_continuous_sum fun i hi ↦ hcM i (Finset.mem_insert_of_mem hi)) hcN using 1 <;>
      · ext; simp [Finset.sum_insert ha]

/-- Bilinear expansion of covariation over two finite sums. -/
theorem isCovariation_sum [IsFiniteMeasure P] {ι κ : Type*} (s : Finset ι) (r : Finset κ)
    {M : ι → ℝ≥0 → Ω → ℝ} {N : κ → ℝ≥0 → Ω → ℝ} {C : ι → κ → ℝ≥0 → Ω → ℝ}
    (hMprog : ∀ i ∈ s, IsStronglyProgressive ℱ (M i))
    (hNprog : ∀ j ∈ r, IsStronglyProgressive ℱ (N j))
    (hcM : ∀ i ∈ s, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (hcN : ∀ j ∈ r, ∀ᵐ ω ∂P, Continuous (N j · ω))
    (hC : ∀ i ∈ s, ∀ j ∈ r, IsCovariation ℱ P (M i) (N j) (C i j)) :
    IsCovariation ℱ P (fun t ω ↦ ∑ i ∈ s, M i t ω) (fun t ω ↦ ∑ j ∈ r, N j t ω)
      (fun t ω ↦ ∑ i ∈ s, ∑ j ∈ r, C i j t ω) :=
  isCovariation_sum_left s hMprog (IsStronglyProgressive.finsetSum hNprog) hcM
    (r.ae_continuous_sum hcN) fun i hi ↦ (isCovariation_sum_left r hNprog (hMprog i hi)
      hcN (hcM i hi) fun j hj ↦ (hC i hi j hj).symm).symm

/-- **Pythagorean rule** for pairwise-orthogonal strongly progressive continuous processes. -/
theorem isQuadraticVariation_sum_of_isCovariation_zero [IsFiniteMeasure P] {ι : Type*}
    (s : Finset ι) {M A : ι → ℝ≥0 → Ω → ℝ}
    (hMprog : ∀ i ∈ s, IsStronglyProgressive ℱ (M i))
    (hcM : ∀ i ∈ s, ∀ᵐ ω ∂P, Continuous (M i · ω))
    (hA : ∀ i ∈ s, IsQuadraticVariation ℱ P (M i) (A i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCovariation ℱ P (M i) (M j) 0) :
    IsQuadraticVariation ℱ P (fun t ω ↦ ∑ i ∈ s, M i t ω) (fun t ω ↦ ∑ i ∈ s, A i t ω) := by
  classical
  have hcov := isCovariation_sum s s (C := fun i j ↦ if i = j then A i else 0)
    hMprog hMprog hcM hcM fun i hi j hj ↦ by
      split_ifs with hij; exacts [hij ▸ (hA i hi).isCovariation_self, horth i hi j hj hij]
  have hdiag : (fun t ω ↦ ∑ i ∈ s, ∑ j ∈ s, (if i = j then A i else 0) t ω) =
      fun t ω ↦ ∑ i ∈ s, A i t ω := by
    ext t ω; refine Finset.sum_congr rfl fun i hi ↦ ?_; simp [ite_apply, hi]
  rw [hdiag] at hcov
  exact hcov.isQuadraticVariation_of_ae_monotone
    (((ae_ball_iff s.countable_toSet).2 fun i hi ↦ (hA i hi).ae_monotone).mono
      fun _ hω _ _ huv ↦ Finset.sum_le_sum fun i hi ↦ hω i hi huv)

end TauCeti.Probability
