/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.QuadraticVariation.Basic
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Real.Sqrt
import TauCeti.Probability.Martingale.Local.Centering
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.InitialMultiplier
import TauCeti.Probability.Process.Stopping
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Mutual variation (covariation) of continuous real processes on raw filtrations

For real-valued processes `M` and `N` on `ℝ≥0` and a filtration `ℱ` under `P`, `C` is a
**covariation** (mutual variation `[M, N]`, `TauCeti.Probability.IsCovariation ℱ P M N C`) when `C`
is strongly progressive for `ℱ`, has almost-surely continuous paths of locally bounded variation
starting at `0`, and compensates `t ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω` as a native local
martingale.

This file establishes uniqueness up to indistinguishability (`IsCovariation.indist`), the diagonal
dictionary (`IsQuadraticVariation.isCovariation_self`,
`IsCovariation.isQuadraticVariation_of_ae_monotone`), polarization and finite-sum bilinearity,
orthogonality (`isQuadraticVariation_sum_of_isCovariation_zero`), and the Kunita–Watanabe increment
and variation bounds (`IsCovariation.ae_abs_sub_le_sqrt_mul_sqrt`,
`IsCovariation.ae_eVariationOn_Icc_le`).

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer, 1999,
  Chapter IV, Proposition 1.15 and Theorem 1.9.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  Chapter 1, §5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

section Defs

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `C` is a **covariation** (mutual variation) of `M` and `N` relative to `(ℱ, P)` if `C` is
strongly progressive, almost surely has continuous paths of locally bounded variation starting at
`0`, and `M * N - M₀ * N₀ - C` is a native local martingale on `ℱ`. -/
def IsCovariation (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω) (M N C : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive ℱ C ∧
    (∀ᵐ ω ∂P, Continuous (fun t ↦ C t ω) ∧
      LocallyBoundedVariationOn (fun t ↦ C t ω) univ ∧ C 0 ω = 0) ∧
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) P

/-- Unfolded characterization of `IsCovariation`. -/
theorem isCovariation_def {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} {M N C : ℝ≥0 → Ω → ℝ} :
    IsCovariation ℱ P M N C ↔ IsStronglyProgressive ℱ C ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ C t ω) ∧
        LocallyBoundedVariationOn (fun t ↦ C t ω) univ ∧ C 0 ω = 0) ∧
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ
        (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) P :=
  Iff.rfl

end Defs

/-- Every quadratic variation of `M` is also a self-covariation `[M, M]`. -/
theorem IsQuadraticVariation.isCovariation_self {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω} {M A : ℝ≥0 → Ω → ℝ}
    (hA : IsQuadraticVariation ℱ P M A) : IsCovariation ℱ P M M A := by
  refine ⟨hA.isStronglyProgressive, ?_, ?_⟩
  · filter_upwards [hA.ae_continuous, hA.ae_locallyBoundedVariationOn, hA.ae_apply_zero]
      with _ hc hbv h0 using ⟨hc, hbv, h0⟩
  · convert hA.locally_martingale using 1; ext; ring

private theorem isStronglyProgressive_mul_sub {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {M N C : ℝ≥0 → Ω → ℝ}
    (hM : IsStronglyProgressive ℱ M) (hN : IsStronglyProgressive ℱ N)
    (hC : IsStronglyProgressive ℱ C) :
    IsStronglyProgressive ℱ (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) :=
  ((hM.mul hN).sub fun _ ↦ (((hM.stronglyAdapted 0).mul (hN.stronglyAdapted 0)).mono
    (ℱ.mono bot_le)).comp_measurable measurable_snd).sub hC

private theorem ae_continuous_mul_sub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M N C : ℝ≥0 → Ω → ℝ} (hcM : ∀ᵐ ω ∂P, Continuous (M · ω))
    (hcN : ∀ᵐ ω ∂P, Continuous (N · ω)) (hcC : ∀ᵐ ω ∂P, Continuous (C · ω)) :
    ∀ᵐ ω ∂P, Continuous (fun t ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) := by
  filter_upwards [hcM, hcN, hcC] with _ hm hn hc using ((hm.mul hn).sub continuous_const).sub hc

namespace IsCovariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {M M₁ M₂ M' N N₁ N₂ N' C C₁ C₂ C' : ℝ≥0 → Ω → ℝ}

/-- Construct `IsCovariation` from separate progressivity, path regularity, initial vanishing, and
local-martingale hypotheses. -/
theorem mk (hprog : IsStronglyProgressive ℱ C) (hc : ∀ᵐ ω ∂P, Continuous (C · ω))
    (hbv : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (C · ω) univ) (h0 : C 0 =ᵐ[P] 0)
    (hmart : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) P) :
    IsCovariation ℱ P M N C := by
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
    ∀ᵐ ω ∂P, LocallyBoundedVariationOn (C · ω) univ :=
  h.2.1.mono fun _ hω ↦ hω.2.1

/-- A covariation vanishes at time `0` almost everywhere. -/
theorem ae_apply_zero (h : IsCovariation ℱ P M N C) : C 0 =ᵐ[P] 0 :=
  h.2.1.mono fun _ hω ↦ hω.2.2

/-- The compensated centered product `M * N - M₀ * N₀ - C` is a native local martingale. -/
theorem locally_martingale (h : IsCovariation ℱ P M N C) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω * N t ω - M 0 ω * N 0 ω - C t ω) P :=
  h.2.2

/-- **Uniqueness of continuous covariation.** Under a finite measure, any two covariations of
almost-surely continuous processes `M` and `N` on `(ℱ, P)` are indistinguishable. -/
theorem indist [IsFiniteMeasure P] (hC : IsCovariation ℱ P M N C) (hC' : IsCovariation ℱ P M N C')
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω)) : C ≡ᵐ[P] C' := by
  have hdiff_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ (C' - C) P :=
    (hC'.isStronglyProgressive.sub hC.isStronglyProgressive).locally_martingale_of_indist_sub
      hC.locally_martingale hC'.locally_martingale
      (ae_continuous_mul_sub hcM hcN hC.ae_continuous)
      (ae_continuous_mul_sub hcM hcN hC'.ae_continuous)
      (.of_forall fun _ _ ↦ by dsimp only [Pi.sub_apply]; ring)
  exact (hdiff_loc.indist_zero_of_locallyBoundedVariationOn
    ((hC'.ae_continuous.and hC.ae_continuous).mono fun _ h ↦ h.1.sub h.2)
    ((hC'.ae_locallyBoundedVariationOn.and hC.ae_locallyBoundedVariationOn).mono fun _ h ↦
      h.1.sub h.2)
    (by filter_upwards [hC'.ae_apply_zero, hC.ae_apply_zero] with _ h1 h2; simp [h1, h2])).mono
    fun _ hω t ↦ (sub_eq_zero.1 (hω t)).symm

/-- Covariation is symmetric in its two process arguments. -/
theorem symm (h : IsCovariation ℱ P M N C) : IsCovariation ℱ P N M C := by
  refine mk h.isStronglyProgressive h.ae_continuous h.ae_locallyBoundedVariationOn
    h.ae_apply_zero ?_
  convert h.locally_martingale using 1; ext; ring

/-- Replacing the compensator by an indistinguishable strongly progressive process preserves
`IsCovariation`, with no assumptions on `M`, `N`, or `P`. -/
theorem congr_right (hC : IsCovariation ℱ P M N C) (hC' : IsStronglyProgressive ℱ C')
    (hCC' : C ≡ᵐ[P] C') : IsCovariation ℱ P M N C' := by
  refine mk hC'
    (by filter_upwards [hC.ae_continuous, hCC'] with _ hc hω using hc.congr hω)
    (by filter_upwards [hC.ae_locallyBoundedVariationOn, hCC'] with _ hbv hω
        exact hbv.congr fun t _ ↦ hω t)
    (by filter_upwards [hC.ae_apply_zero, hCC'] with _ h0 hω using (hω 0).symm.trans h0) ?_
  convert hC.locally_martingale.martingale_add_of_indist_zero (hC.isStronglyProgressive.sub hC')
    (hCC'.mono fun _ hω t ↦ sub_eq_zero.2 (hω t)) using 1
  ext; simp only [Pi.add_apply]; ring

/-- Replacing `M`, `N`, and `C` by indistinguishable strongly progressive processes preserves
`IsCovariation`. -/
theorem congr (hC : IsCovariation ℱ P M N C)
    (hM' : IsStronglyProgressive ℱ M') (hN' : IsStronglyProgressive ℱ N')
    (hC' : IsStronglyProgressive ℱ C') (hMM' : M ≡ᵐ[P] M') (hNN' : N ≡ᵐ[P] N')
    (hCC' : C ≡ᵐ[P] C') : IsCovariation ℱ P M' N' C' := by
  have hC₁ := hC.congr_right hC' hCC'
  refine mk hC' hC₁.ae_continuous hC₁.ae_locallyBoundedVariationOn hC₁.ae_apply_zero
    ((isStronglyProgressive_mul_sub hM' hN' hC').locally_martingale_of_indist
      hC₁.locally_martingale ?_)
  filter_upwards [hMM', hNN'] with _ hm hn t using by simp [hm t, hm 0, hn t, hn 0]

/-- Every self-covariation `[M, M]` with almost-surely monotone paths is a quadratic variation. -/
theorem isQuadraticVariation_of_ae_monotone {A : ℝ≥0 → Ω → ℝ}
    (hC : IsCovariation ℱ P M M A) (hmono : ∀ᵐ ω ∂P, Monotone (A · ω)) :
    IsQuadraticVariation ℱ P M A := by
  refine IsQuadraticVariation.mk hC.isStronglyProgressive hC.ae_continuous hmono hC.ae_apply_zero ?_
  convert hC.locally_martingale using 1; ext; ring

/-- If an almost-surely continuous process `M` admits some quadratic variation under a finite
measure, then every self-covariation `[M, M]` is automatically a quadratic variation of `M`. -/
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

/-- Left additivity of covariation for strongly progressive, almost-surely continuous processes. -/
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
  convert (isStronglyProgressive_mul_sub hM₁ hN h₁.isStronglyProgressive).locally_martingale_add
    (isStronglyProgressive_mul_sub hM₂ hN h₂.isStronglyProgressive)
    h₁.locally_martingale h₂.locally_martingale (ae_continuous_mul_sub hcM₁ hcN h₁.ae_continuous)
    (ae_continuous_mul_sub hcM₂ hcN h₂.ae_continuous) using 1
  ext; dsimp only [Pi.add_apply]; ring

/-- Right additivity of covariation for strongly progressive, almost-surely continuous processes. -/
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

/-- Stopping strongly progressive, almost-surely continuous processes at an arbitrary stopping time
preserves `IsCovariation` under a finite measure. -/
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
  convert (isStronglyProgressive_mul_sub hMprog hNprog
    hC.isStronglyProgressive).locally_martingale_stoppedProcess hC.locally_martingale
    ((ae_continuous_mul_sub hcM hcN hC.ae_continuous).mono fun _ h ↦ h.isRightContinuous)
    hτ using 1
  ext; simp [MeasureTheory.stoppedProcess]

end IsCovariation

section PolarizationAndSums

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}

/-- Symmetry of `IsCovariation` as an equivalence. -/
theorem isCovariation_comm {M N C : ℝ≥0 → Ω → ℝ} :
    IsCovariation ℱ P M N C ↔ IsCovariation ℱ P N M C :=
  ⟨IsCovariation.symm, IsCovariation.symm⟩

/-- The zero process has covariation `0` on the left with any process. -/
@[simp]
theorem isCovariation_zero_left (N : ℝ≥0 → Ω → ℝ) : IsCovariation ℱ P 0 N 0 := by
  refine IsCovariation.mk (isStronglyProgressive_const ℱ 0) (ae_of_all P fun _ ↦ continuous_const)
    (ae_of_all P fun _ _ _ _ _ ↦ by simp [BoundedVariationOn, eVariationOn]) .rfl ?_
  convert Locally.of_prop (p := fun Y ↦ Martingale Y ℱ P) (martingale_zero ℝ ℱ P) using 1; ext; simp

/-- The zero process has covariation `0` on the right with any process. -/
@[simp]
theorem isCovariation_zero_right (M : ℝ≥0 → Ω → ℝ) : IsCovariation ℱ P M 0 0 :=
  (isCovariation_zero_left M).symm

/-- An `ℱ 0`-strongly measurable time-independent process has zero covariation with any native local
martingale under a sigma-finite filtration. -/
theorem isCovariation_const_left [SigmaFiniteFiltration P ℱ] {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ 0] ξ) {N : ℝ≥0 → Ω → ℝ}
    (hN : Locally (fun Y ↦ Martingale Y ℱ P) ℱ N P) : IsCovariation ℱ P (fun _ ↦ ξ) N 0 := by
  refine IsCovariation.mk (isStronglyProgressive_const ℱ 0) (ae_of_all P fun _ ↦ continuous_const)
    (ae_of_all P fun _ _ _ _ _ ↦ by simp [BoundedVariationOn, eVariationOn]) .rfl ?_
  convert hN.martingale_sub_initialValue.martingale_smul_initial hξ using 1
  ext; simp only [Pi.zero_apply, sub_zero, smul_eq_mul, bot_eq_zero]; ring

/-- Any native local martingale has zero covariation on the right with an `ℱ 0`-strongly measurable
time-independent process under a sigma-finite filtration. -/
theorem isCovariation_const_right [SigmaFiniteFiltration P ℱ] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsCovariation ℱ P M (fun _ ↦ ξ) 0 :=
  (isCovariation_const_left hξ hM).symm

/-- **Polarization identity (`[M + N] - [M - N]`).** Quadratic variations `A⁺` of `M + N` and `A⁻`
of `M - N` determine the covariation `4⁻¹ • (A⁺ - A⁻)` of `M` and `N`. -/
theorem isCovariation_of_isQuadraticVariation_add_sub [IsFiniteMeasure P]
    {M N Apos Aneg : ℝ≥0 → Ω → ℝ}
    (hMprog : IsStronglyProgressive ℱ M) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hadd : IsQuadraticVariation ℱ P (M + N) Apos) (hsub : IsQuadraticVariation ℱ P (M - N) Aneg) :
    IsCovariation ℱ P M N ((4⁻¹ : ℝ) • (Apos - Aneg)) := by
  have hdiff_prog : IsStronglyProgressive ℱ ((4⁻¹ : ℝ) • (Apos - Aneg)) := fun t ↦
    ((hadd.isStronglyProgressive.sub hsub.isStronglyProgressive) t).const_smul (4⁻¹ : ℝ)
  refine IsCovariation.mk hdiff_prog
    ((hadd.ae_continuous.and hsub.ae_continuous).mono fun _ h ↦ continuous_const.mul (h.1.sub h.2))
    ((hadd.ae_locallyBoundedVariationOn.and hsub.ae_locallyBoundedVariationOn).mono
      fun _ h ↦ (lipschitzWith_smul (4⁻¹ : ℝ)).comp_locallyBoundedVariationOn (h.1.sub h.2))
    (by filter_upwards [hadd.ae_apply_zero, hsub.ae_apply_zero] with _ ha hb; simp [ha, hb])
    ((isStronglyProgressive_mul_sub hMprog hNprog hdiff_prog).locally_martingale_of_indist_sub
      (hadd.locally_martingale.martingale_smul (4⁻¹ : ℝ))
      (hsub.locally_martingale.martingale_smul (4⁻¹ : ℝ))
      (by filter_upwards [hcM, hcN, hadd.ae_continuous] with _ hm hn ha
          exact continuous_const.mul ((((hm.add hn).pow 2).sub continuous_const).sub ha))
      (by filter_upwards [hcM, hcN, hsub.ae_continuous] with _ hm hn ha
          exact continuous_const.mul ((((hm.sub hn).pow 2).sub continuous_const).sub ha))
      (.of_forall fun _ _ ↦ by
        dsimp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring))

/-- **Polarization identity (`[M + N] - [M] - [N]`).** Quadratic variations `A`, `B`, and `D` of
`M`, `N`, and `M + N` yield the covariation `2⁻¹ • (D - A - B)` of `M` and `N`. -/
theorem isCovariation_of_isQuadraticVariation_add [IsFiniteMeasure P]
    {M N A B D : ℝ≥0 → Ω → ℝ}
    (hMprog : IsStronglyProgressive ℱ M) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hA : IsQuadraticVariation ℱ P M A) (hB : IsQuadraticVariation ℱ P N B)
    (hD : IsQuadraticVariation ℱ P (M + N) D) :
    IsCovariation ℱ P M N ((2⁻¹ : ℝ) • (D - A - B)) := by
  have hprog : IsStronglyProgressive ℱ ((2⁻¹ : ℝ) • (D - A - B)) := fun t ↦
    (((hD.isStronglyProgressive.sub hA.isStronglyProgressive).sub
      hB.isStronglyProgressive) t).const_smul (2⁻¹ : ℝ)
  have hcA := ae_continuous_mul_sub hcM hcM hA.ae_continuous
  have hcB := ae_continuous_mul_sub hcN hcN hB.ae_continuous
  have hXAB := ((isStronglyProgressive_mul_sub hMprog hMprog
      hA.isStronglyProgressive).locally_martingale_add
    (isStronglyProgressive_mul_sub hNprog hNprog hB.isStronglyProgressive)
    hA.isCovariation_self.locally_martingale hB.isCovariation_self.locally_martingale
    hcA hcB).martingale_smul (2⁻¹ : ℝ)
  refine IsCovariation.mk hprog
    (by filter_upwards [hD.ae_continuous, hA.ae_continuous, hB.ae_continuous] with _ hd ha hb
        exact continuous_const.mul ((hd.sub ha).sub hb))
    (by filter_upwards [hD.ae_locallyBoundedVariationOn, hA.ae_locallyBoundedVariationOn,
          hB.ae_locallyBoundedVariationOn] with _ hd ha hb
        exact (lipschitzWith_smul (2⁻¹ : ℝ)).comp_locallyBoundedVariationOn ((hd.sub ha).sub hb))
    (by filter_upwards [hD.ae_apply_zero, hA.ae_apply_zero, hB.ae_apply_zero] with _ hd ha hb
        simp [hd, ha, hb])
    ((isStronglyProgressive_mul_sub hMprog hNprog hprog).locally_martingale_of_indist_sub
      (hD.locally_martingale.martingale_smul (2⁻¹ : ℝ)) hXAB
      (by filter_upwards [hcM, hcN, hD.ae_continuous] with _ hm hn hd
          exact continuous_const.mul ((((hm.add hn).pow 2).sub continuous_const).sub hd))
      ((hcA.and hcB).mono fun _ h ↦ continuous_const.mul (h.1.add h.2))
      (.of_forall fun _ _ ↦ by
        dsimp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring))

private theorem ae_continuous_sum {ι : Type*} (s : Finset ι) {U : ι → ℝ≥0 → Ω → ℝ}
    (hc : ∀ i ∈ s, ∀ᵐ ω ∂P, Continuous (U i · ω)) :
    ∀ᵐ ω ∂P, Continuous (fun t ↦ ∑ i ∈ s, U i t ω) :=
  ((ae_ball_iff s.countable_toSet).2 hc).mono fun ω hω ↦ by
    have (i : ι) (hi : i ∈ s) : Continuous (U i · ω) := hω i hi; fun_prop

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
      (ae_continuous_sum s fun i hi ↦ hcM i (Finset.mem_insert_of_mem hi)) hcN using 1 <;>
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
    (ae_continuous_sum r hcN) fun i hi ↦ (isCovariation_sum_left r hNprog (hMprog i hi)
      hcN (hcM i hi) fun j hj ↦ (hC i hi j hj).symm).symm

/-- **Pythagorean rule for pairwise orthogonal processes.** If a finite family of strongly
progressive, almost-surely continuous processes has quadratic variations `A i` and vanishing
off-diagonal covariations, then its sum has quadratic variation `∑ i ∈ s, A i`. -/
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
  rw [show (fun t ω ↦ ∑ i ∈ s, ∑ j ∈ s, (if i = j then A i else 0) t ω) =
      fun t ω ↦ ∑ i ∈ s, A i t ω by
    ext t ω; refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hite (j : ι) : (if i = j then A i else 0) t ω = if i = j then A i t ω else 0 := by
      split_ifs <;> rfl
    simp [hite, hi]] at hcov
  exact hcov.isQuadraticVariation_of_ae_monotone
    (((ae_ball_iff s.countable_toSet).2 fun i hi ↦ (hA i hi).ae_monotone).mono
      fun _ hω _ _ huv ↦ Finset.sum_le_sum fun i hi ↦ hω i hi huv)

end PolarizationAndSums

section KunitaWatanabe

private theorem abs_le_sqrt_mul_sqrt_of_quad_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ q : ℚ, 0 ≤ a + 2 * (q : ℝ) * c + (q : ℝ) ^ 2 * b) : |c| ≤ √a * √b := by
  have hreal (r : ℝ) : 0 ≤ a + 2 * r * c + r ^ 2 * b :=
    Rat.denseRange_cast.induction_on r (isClosed_le continuous_const (by fun_prop)) h
  rcases hb.eq_or_lt with rfl | hb_pos
  · by_cases hc : c = 0
    · simp [hc]
    · have hbad := hreal (-(a + 1) / (2 * c))
      have : a + 2 * (-(a + 1) / (2 * c)) * c + (-(a + 1) / (2 * c)) ^ 2 * 0 = -1 := by
        field_simp; ring
      linarith
  · have hmul := mul_nonneg (hreal (-c / b)) hb_pos.le
    have : (a + 2 * (-c / b) * c + (-c / b) ^ 2 * b) * b = a * b - c ^ 2 := by
      field_simp [hb_pos.ne']; ring
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul ha]; exact Real.sqrt_le_sqrt (by linarith)

namespace IsCovariation

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {M N A B C : ℝ≥0 → Ω → ℝ}

/-- **Increment Kunita–Watanabe inequality.** If `M` and `N` are strongly progressive, almost-surely
continuous processes with quadratic variations `A` and `B`, covariation `C`, and every rational
linear combination `M + q • N` admits a quadratic variation, then almost surely for all `s ≤ t`,
`|C t ω - C s ω| ≤ √(A t ω - A s ω) * √(B t ω - B s ω)`. -/
theorem ae_abs_sub_le_sqrt_mul_sqrt [IsFiniteMeasure P] (hC : IsCovariation ℱ P M N C)
    (hA : IsQuadraticVariation ℱ P M A) (hB : IsQuadraticVariation ℱ P N B)
    (hMprog : IsStronglyProgressive ℱ M) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hquad : ∀ q : ℚ, ∃ Q, IsQuadraticVariation ℱ P (M + (q : ℝ) • N) Q) :
    ∀ᵐ ω ∂P, ∀ s t, s ≤ t → |C t ω - C s ω| ≤ √(A t ω - A s ω) * √(B t ω - B s ω) := by
  have hqmono (q : ℚ) : ∀ᵐ ω ∂P,
      Monotone (fun t ↦ ((A + (q : ℝ) • C) + ((q : ℝ) • C + (q : ℝ) ^ 2 • B)) t ω) := by
    have hqprog : IsStronglyProgressive ℱ ((q : ℝ) • N) := fun t ↦ (hNprog t).const_smul (q : ℝ)
    have hcq : ∀ᵐ ω ∂P, Continuous (((q : ℝ) • N) · ω) :=
      hcN.mono fun _ hn ↦ continuous_const.mul hn
    have hcsum : ∀ᵐ ω ∂P, Continuous ((M + (q : ℝ) • N) · ω) :=
      (hcM.and hcq).mono fun _ h ↦ h.1.add h.2
    exact (((hA.isCovariation_self.add_right (hC.const_smul_right (q : ℝ))
        hMprog hMprog hqprog hcM hcM hcq).add_left
      ((hC.symm.const_smul_left (q : ℝ)).add_right (hB.const_smul (q : ℝ)).isCovariation_self
        hqprog hMprog hqprog hcq hcM hcq)
      hMprog hqprog (hMprog.add hqprog) hcM hcq hcsum).isQuadraticVariation_of_exists hcsum
      (hquad q)).ae_monotone
  filter_upwards [ae_all_iff.2 hqmono, hA.ae_monotone, hB.ae_monotone] with ω hq hAm hBm s t hst
  refine abs_le_sqrt_mul_sqrt_of_quad_nonneg (sub_nonneg.2 (hAm hst)) (sub_nonneg.2 (hBm hst))
    fun q ↦ ?_
  have hle := sub_nonneg.2 (hq q hst)
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hle; linarith

/-- **Variation Kunita–Watanabe inequality.** Under the hypotheses of
`IsCovariation.ae_abs_sub_le_sqrt_mul_sqrt`, almost surely for all `s` and `t`, the extended total
variation of `C · ω` on `Icc s t` is bounded by
`ENNReal.ofReal (√(A t ω - A s ω) * √(B t ω - B s ω))`. -/
theorem ae_eVariationOn_Icc_le [IsFiniteMeasure P] (hC : IsCovariation ℱ P M N C)
    (hA : IsQuadraticVariation ℱ P M A) (hB : IsQuadraticVariation ℱ P N B)
    (hMprog : IsStronglyProgressive ℱ M) (hNprog : IsStronglyProgressive ℱ N)
    (hcM : ∀ᵐ ω ∂P, Continuous (M · ω)) (hcN : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hquad : ∀ q : ℚ, ∃ Q, IsQuadraticVariation ℱ P (M + (q : ℝ) • N) Q) :
    ∀ᵐ ω ∂P, ∀ s t,
      eVariationOn (C · ω) (Icc s t) ≤ ENNReal.ofReal (√(A t ω - A s ω) * √(B t ω - B s ω)) := by
  filter_upwards [hC.ae_abs_sub_le_sqrt_mul_sqrt hA hB hMprog hNprog hcM hcN hquad,
    hA.ae_monotone, hB.ae_monotone] with ω hkw hAm hBm s t
  exact eVariationOn.Icc_le_of_dist_le_sqrt_mul_sqrt hAm hBm fun u _ v _ huv ↦ by
    simpa only [Real.dist_eq] using hkw u v huv

end IsCovariation

end KunitaWatanabe

end TauCeti.Probability
