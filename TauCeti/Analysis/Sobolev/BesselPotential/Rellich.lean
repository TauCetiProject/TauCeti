/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
public import TauCeti.Analysis.Sobolev.BesselPotential.Multiplication
import TauCeti.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Convolution
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Function.Lp.Operator.Compact

/-!
# The Rellich theorem for Bessel-potential spaces

Let `E` be a finite-dimensional real inner product space and `F` a finite-dimensional complex
inner product space. For a scalar Schwartz function `φ` and real orders `r < s`, multiplication by
`φ` followed by the inclusion `H^s ⊆ H^r` is a **compact operator**
`H^s(E, F) → H^r(E, F)` between Mathlib's Bessel-potential spaces
(`BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`). This is the Rellich
theorem for a common compact support: if the elements of a bounded subset of `H^s` all satisfy
`φ u = u`, for instance because they are supported in a compact set on a neighbourhood of which
`φ = 1`, the subset has compact closure in `H^r`
(`BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq`). Without such a
localization the inclusion `H^s ⊆ H^r` is not compact, since translates of a fixed bump function
have no convergent subsequence.

## The Fourier argument

Write `⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. The isometries `u ↦ 𝓕 (J^t u)` identify `H^t` with `L²`,
and in these coordinates the operator `u ↦ φ u` from `H^s` to `H^r` becomes the integral operator
with the scalar kernel

`k(ξ, η) = ⟨ξ⟩ ^ r 𝓕 φ (ξ - η) ⟨η⟩ ^ (-s)`,

since `𝓕 (φ u) = 𝓕 φ ⋆ 𝓕 u`. This identity is checked on Schwartz functions, which are dense in
`H^s`. Peetre's inequality bounds `⟨ξ⟩ ^ r ⟨η⟩ ^ (-s)` both by
`2 ^ (|s| / 2) ⟨ξ - η⟩ ^ |s| ⟨ξ⟩ ^ (r - s)` and by `2 ^ (|r| / 2) ⟨ξ - η⟩ ^ |r| ⟨η⟩ ^ (r - s)`. As
`r < s`, outside the square `‖ξ‖, ‖η‖ ≤ R` the kernel is therefore at most
`(1 + R ^ 2) ^ ((r - s) / 2)` times an integrable function of `ξ - η`, so by Schur's test the
corresponding part of the operator has norm tending to `0` as `R → ∞`. On the square the kernel
is continuous, so its integral operator is compact
(`TauCeti.isCompactOperator_integralOperatorLp_of_continuousOn`). A norm limit of compact operators
is compact.

## Main results

* `BesselPotentialSpace.isCompactOperator_inclusion_comp_smulLeftCLM`: `u ↦ φ u` is compact from
  `H^s` to `H^r` for `r < s`.
* `BesselPotentialSpace.isCompact_closure_image_inclusion_of_smulLeftCLM_eq`: a bounded subset of
  `H^s` on which multiplication by `φ` is the identity has compact closure in `H^r`.

## References

* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Princeton University
  Press, 1995, Chapter 6 (Rellich's theorem for Sobolev spaces with a common compact support).
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution Filter Function Set
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace Topology

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

namespace BesselPotentialSpace

/-- The scalar Fourier-side kernel `⟨ξ⟩ ^ r 𝓕 φ (ξ - η) ⟨η⟩ ^ (-s)` of `u ↦ φ u` from `H^s` to
`H^r`, as a multiple of the identity of `F`. -/
private def rellichKernel (φ : 𝓢(E, ℂ)) (r s : ℝ) (ξ η : E) : F →L[ℂ] F :=
  ((((1 + ‖ξ‖ ^ 2) ^ (r / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) * 𝓕 φ (ξ - η)) •
    ContinuousLinearMap.id ℂ F

/-- The integrable function of `ξ - η` dominating the kernel. -/
private def rellichBound (φ : 𝓢(E, ℂ)) (r s : ℝ) (ζ : E) : ℝ :=
  2 ^ (|s| / 2) * ((1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 φ ζ‖) +
    2 ^ (|r| / 2) * ((1 + ‖ζ‖ ^ 2) ^ (|r| / 2) * ‖𝓕 φ ζ‖)

variable {φ : 𝓢(E, ℂ)} {r s : ℝ}

private theorem rellichBound_nonneg (ζ : E) : 0 ≤ rellichBound φ r s ζ := by
  unfold rellichBound
  positivity

private theorem integrable_rellichBound : Integrable (rellichBound φ r s) (volume : Measure E) :=
  (((𝓕 φ).integrable_one_add_norm_sq_rpow_mul_norm (|s| / 2)).const_mul _).add
    (((𝓕 φ).integrable_one_add_norm_sq_rpow_mul_norm (|r| / 2)).const_mul _)

omit [CompleteSpace F] in
private theorem continuous_rellichKernel :
    Continuous (uncurry (rellichKernel (F := F) φ r s)) := by
  have hc : Continuous fun p : E × E ↦
      (((1 + ‖p.1‖ ^ 2) ^ (r / 2) * (1 + ‖p.2‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) * 𝓕 φ (p.1 - p.2) :=
    (Complex.continuous_ofReal.comp (((continuous_const.add (continuous_fst.norm.pow 2)).rpow_const
      fun _ ↦ Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne').mul
      ((continuous_const.add (continuous_snd.norm.pow 2)).rpow_const
      fun _ ↦ Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'))).mul
      ((𝓕 φ).continuous.comp (continuous_fst.sub continuous_snd))
  -- `uncurry (rellichKernel φ r s)` is by definition the product of this coefficient and `id`.
  exact hc.smul (continuous_const (y := ContinuousLinearMap.id ℂ F))

omit [CompleteSpace F] in
/-- The kernel is dominated by `(1 + R ^ 2) ^ ((r - s) / 2)` times the integrable function
`rellichBound` of `ξ - η` as soon as `‖ξ‖ ≥ R` or `‖η‖ ≥ R`. -/
private theorem norm_rellichKernel_le_of_le (h : r ≤ s) {R : ℝ} (hR : 0 ≤ R) {ξ η : E}
    (hξη : R ≤ ‖ξ‖ ∨ R ≤ ‖η‖) :
    ‖rellichKernel (F := F) φ r s ξ η‖ ≤
      (1 + R ^ 2) ^ ((r - s) / 2) * rellichBound φ r s (ξ - η) := by
  have hw : 0 ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) * (1 + ‖η‖ ^ 2) ^ (-s / 2) := by positivity
  rw [rellichKernel]
  refine (norm_smul_le _ (ContinuousLinearMap.id ℂ F)).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  have h₁ := norm_nonneg (𝓕 φ (ξ - η))
  unfold rellichBound
  rcases hξη with hξ | hη
  · calc _ ≤ 2 ^ (|s| / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (|s| / 2) * (1 + R ^ 2) ^ ((r - s) / 2) *
          ‖𝓕 φ (ξ - η)‖ := by
          refine mul_le_mul_of_nonneg_right
            ((TauCeti.one_add_norm_sq_rpow_mul_rpow_le_mul_sub_left r s ξ η).trans ?_) h₁
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
            (by gcongr) (by linarith)) (by positivity)
      _ ≤ _ := by
          rw [mul_add]
          refine le_add_of_le_of_nonneg (le_of_eq (by ring)) ?_
          positivity
  · calc _ ≤ 2 ^ (|r| / 2) * (1 + ‖ξ - η‖ ^ 2) ^ (|r| / 2) * (1 + R ^ 2) ^ ((r - s) / 2) *
          ‖𝓕 φ (ξ - η)‖ := by
          refine mul_le_mul_of_nonneg_right
            ((TauCeti.one_add_norm_sq_rpow_mul_rpow_le_mul_sub_right r s ξ η).trans ?_) h₁
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
            (by gcongr) (by linarith)) (by positivity)
      _ ≤ _ := by
          rw [mul_add]
          refine le_add_of_nonneg_of_le ?_ (le_of_eq (by ring))
          positivity

omit [CompleteSpace F] in
/-- The kernel is dominated by the integrable function `rellichBound` of `ξ - η`. -/
private theorem norm_rellichKernel_le (h : r ≤ s) (ξ η : E) :
    ‖rellichKernel (F := F) φ r s ξ η‖ ≤ rellichBound φ r s (ξ - η) := by
  simpa using norm_rellichKernel_le_of_le (F := F) (φ := φ) h le_rfl (Or.inl (norm_nonneg ξ))

omit [CompleteSpace F] in
/-- Row and column bounds for a kernel dominated by `c` times a function of `ξ - η`. -/
private theorem lintegral_enorm_le_of_norm_le_sub {L : E → E → F →L[ℂ] F} {c : ℝ} (hc : 0 ≤ c)
    (hL : ∀ ξ η, ‖L ξ η‖ ≤ c * rellichBound φ r s (ξ - η)) :
    (∀ ξ, ∫⁻ η, ‖L ξ η‖ₑ ≤ (((c * ∫ ζ, rellichBound φ r s ζ).toNNReal : ℝ≥0) : ℝ≥0∞)) ∧
      ∀ η, ∫⁻ ξ, ‖L ξ η‖ₑ ≤ (((c * ∫ ζ, rellichBound φ r s ζ).toNNReal : ℝ≥0) : ℝ≥0∞) := by
  have hint : ∫⁻ ζ, ENNReal.ofReal (c * rellichBound φ r s ζ) =
      (((c * ∫ ζ, rellichBound φ r s ζ).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal.eq_def, ← integral_const_mul,
      ofReal_integral_eq_lintegral_ofReal (integrable_rellichBound.const_mul c)
        (.of_forall fun ζ ↦ mul_nonneg hc (rellichBound_nonneg ζ))]
  have hle (ξ η : E) : ‖L ξ η‖ₑ ≤ ENNReal.ofReal (c * rellichBound φ r s (ξ - η)) := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hL ξ η)
  refine ⟨fun ξ ↦ ?_, fun η ↦ ?_⟩
  · calc ∫⁻ η, ‖L ξ η‖ₑ ≤ ∫⁻ η, ENNReal.ofReal (c * rellichBound φ r s (ξ - η)) :=
          lintegral_mono (hle ξ)
      _ = _ := by
          rw [lintegral_sub_left_eq_self (fun ζ ↦ ENNReal.ofReal (c * rellichBound φ r s ζ)) ξ,
            hint]
  · calc ∫⁻ ξ, ‖L ξ η‖ₑ ≤ ∫⁻ ξ, ENNReal.ofReal (c * rellichBound φ r s (ξ - η)) :=
          lintegral_mono fun ξ ↦ hle ξ η
      _ = _ := by
          rw [lintegral_sub_right_eq_self (fun ζ ↦ ENNReal.ofReal (c * rellichBound φ r s ζ)) η,
            hint]

/-- The integral operator on `L²` with the kernel `rellichKernel`. -/
private def rellichOperator (φ : 𝓢(E, ℂ)) (h : r ≤ s) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  TauCeti.integralOperatorLp (rellichKernel φ r s) 2
    continuous_rellichKernel.aestronglyMeasurable
    (.of_forall (lintegral_enorm_le_of_norm_le_sub zero_le_one
      fun ξ η ↦ by simpa using norm_rellichKernel_le h ξ η).1)
    (.of_forall (lintegral_enorm_le_of_norm_le_sub zero_le_one
      fun ξ η ↦ by simpa using norm_rellichKernel_le h ξ η).2)

/-- For `r < s` and finite-dimensional `F`, the integral operator with the kernel
`⟨ξ⟩ ^ r 𝓕 φ (ξ - η) ⟨η⟩ ^ (-s)` is compact on `L²`: it is the norm limit of its truncations to
the squares `‖ξ‖, ‖η‖ ≤ R`, whose kernels are continuous on compact sets. -/
private theorem isCompactOperator_rellichOperator [FiniteDimensional ℂ F] (h : r < s) :
    IsCompactOperator (rellichOperator (F := F) φ h.le) := by
  refine isClosed_setOfPred_isCompactOperator.closure_subset (Metric.mem_closure_iff.2
    fun ε hε ↦ ?_)
  set C := ∫ ζ, rellichBound φ r s ζ
  -- Choose `R` with `(1 + R ^ 2) ^ ((r - s) / 2) * C < ε`.
  have hρ : Tendsto (fun R : ℝ ↦ (1 + R ^ 2) ^ ((r - s) / 2) * C) atTop (𝓝 (0 * C)) := by
    refine Tendsto.mul_const C ?_
    have := (tendsto_rpow_neg_atTop (y := (s - r) / 2) (by linarith)).comp
      (tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop two_ne_zero))
    refine this.congr fun R ↦ ?_
    simp only [comp_apply]
    congr 1
    ring
  rw [zero_mul] at hρ
  obtain ⟨R, hRε, hR⟩ := ((hρ.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 0)).exists
  set B : Set (E × E) := Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R
  have hBm : MeasurableSet B :=
    Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet
  -- The kernel truncated to the square `B` and the remaining part.
  set Kin : E → E → F →L[ℂ] F := fun ξ η ↦ B.indicator (uncurry (rellichKernel φ r s)) (ξ, η)
  have hKin_meas : AEStronglyMeasurable (uncurry Kin) (volume.prod volume) :=
    continuous_rellichKernel.aestronglyMeasurable.indicator hBm
  have hKin_le (ξ η : E) : ‖Kin ξ η‖ ≤ 1 * rellichBound φ r s (ξ - η) := by
    simp only [Kin, one_mul]
    by_cases hB : (ξ, η) ∈ B
    · rw [indicator_of_mem hB]
      exact norm_rellichKernel_le h.le ξ η
    · rw [indicator_of_notMem hB, norm_zero]
      exact rellichBound_nonneg _
  have hKout_le (ξ η : E) : ‖rellichKernel φ r s ξ η - Kin ξ η‖ ≤
      (1 + R ^ 2) ^ ((r - s) / 2) * rellichBound φ r s (ξ - η) := by
    simp only [Kin]
    by_cases hB : (ξ, η) ∈ B
    · rw [indicator_of_mem hB, uncurry_apply_pair, sub_self, norm_zero]
      exact mul_nonneg (by positivity) (rellichBound_nonneg _)
    · rw [indicator_of_notMem hB, sub_zero]
      refine norm_rellichKernel_le_of_le h.le hR ?_
      simp only [B, Set.mem_prod, Metric.mem_closedBall, dist_zero_right, not_and_or,
        not_le] at hB
      exact hB.imp le_of_lt le_of_lt
  have hKin_bd := lintegral_enorm_le_of_norm_le_sub zero_le_one hKin_le
  have hKout_bd := lintegral_enorm_le_of_norm_le_sub (by positivity) hKout_le
  refine ⟨TauCeti.integralOperatorLp Kin 2 hKin_meas (.of_forall hKin_bd.1)
    (.of_forall hKin_bd.2), ?_, ?_⟩
  · -- The truncated kernel is continuous on the compact square and vanishes outside it.
    refine TauCeti.isCompactOperator_integralOperatorLp_of_continuousOn
      (isCompact_closedBall 0 R) (isCompact_closedBall 0 R) ?_ fun ξ η hB ↦ ?_
    · exact continuous_rellichKernel.continuousOn.congr fun z hz ↦ indicator_of_mem hz _
    · exact indicator_of_notMem hB _
  · -- Schur's test bounds the remaining part by `(1 + R ^ 2) ^ ((r - s) / 2) * C < ε`.
    rw [dist_eq_norm, rellichOperator, TauCeti.integralOperatorLp_sub
      (hK := continuous_rellichKernel.aestronglyMeasurable.sub hKin_meas)
      (hA := .of_forall hKout_bd.1) (hB := .of_forall hKout_bd.2)]
    refine TauCeti.norm_integralOperatorLp_le_max.trans_lt ?_
    rw [max_self, Real.coe_toNNReal _ (mul_nonneg (by positivity)
      (integral_nonneg rellichBound_nonneg))]
    exact hRε

/-- The isometry `u ↦ 𝓕 (J^t u)` from `H^t` onto `L²`, the weighted Fourier transform. -/
private def fourierWeighted (t : ℝ) : H^{t}(E, F) ≃L[ℂ] Lp F 2 (volume : Measure E) :=
  (toLpₗᵢ E F t 2).toContinuousLinearEquiv.trans (Lp.fourierTransformₗᵢ E F).toContinuousLinearEquiv

private theorem fourierWeighted_apply (t : ℝ) (u : H^{t}(E, F)) :
    fourierWeighted t u = 𝓕 u.toLp := by
  rw [fourierWeighted, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, toLpₗᵢ_apply]
  -- The Fourier transform on `L²` is by definition `Lp.fourierTransformₗᵢ`.
  rfl

/-- On a Schwartz function `u`, the weighted Fourier transform is the function `⟨ξ⟩ ^ t 𝓕 u`. -/
private theorem fourierWeighted_toBesselPotentialSpaceCLM (t : ℝ) (u : 𝓢(E, F)) :
    fourierWeighted t (SchwartzMap.toBesselPotentialSpaceCLM t 2 u) =ᵐ[volume]
      fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (t / 2) : ℝ) : ℂ) • 𝓕 u ξ := by
  have hw : (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have h : fourierWeighted t (SchwartzMap.toBesselPotentialSpaceCLM t 2 u) =
      (SchwartzMap.smulLeftCLM F (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ))
        (𝓕 u)).toLp 2 := by
    rw [fourierWeighted_apply, SchwartzMap.toLp_toBesselPotentialSpaceCLM,
      SchwartzMap.toLp_fourier_eq, SchwartzMap.fourierMultiplierCLM_apply, fourier_fourierInv_eq]
  rw [h]
  filter_upwards [SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM F
    (fun x : E ↦ (((1 + ‖x‖ ^ 2) ^ (t / 2) : ℝ) : ℂ)) (𝓕 u)) 2 volume] with ξ hξ
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply hw]

/-- In weighted Fourier coordinates, `u ↦ φ u` from `H^s` to `H^r` is the integral operator with
the kernel `⟨ξ⟩ ^ r 𝓕 φ (ξ - η) ⟨η⟩ ^ (-s)`: `𝓕 (φ u) = 𝓕 φ ⋆ 𝓕 u`. -/
private theorem fourierWeighted_comp_eq (φ : 𝓢(E, ℂ)) (h : r ≤ s) :
    (fourierWeighted (E := E) (F := F) r : H^{r}(E, F) →L[ℂ] Lp F 2 (volume : Measure E)) ∘L
        (inclusion h ∘L smulLeftCLM s φ) =
      rellichOperator φ h ∘L
        (fourierWeighted (E := E) (F := F) s : H^{s}(E, F) →L[ℂ] Lp F 2 (volume : Measure E)) := by
  refine continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ ?_
  -- On a Schwartz function `u`, `φ u` is the Schwartz function `φ • u`.
  have hφu : inclusion h (smulLeftCLM s φ (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)) =
      SchwartzMap.toBesselPotentialSpaceCLM r 2 (SchwartzMap.smulLeftCLM F (φ : E → ℂ) u) :=
    ext (by simp [smulLeftCLM_toTemperedDistributionCLM_eq φ.hasTemperateGrowth])
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hφu]
  refine (TauCeti.integralOperatorLp_eq_iff.2 ?_).symm
  filter_upwards [fourierWeighted_toBesselPotentialSpaceCLM r (SchwartzMap.smulLeftCLM F
    (φ : E → ℂ) u)] with ξ hξ
  rw [hξ, SchwartzMap.fourier_smulLeftCLM_apply, ← integral_sub_left_eq_self
    (fun t ↦ 𝓕 φ t • 𝓕 u (ξ - t)) volume ξ, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [fourierWeighted_toBesselPotentialSpaceCLM s u] with η hη
  -- The weights `⟨η⟩ ^ (-s)` and `⟨η⟩ ^ s` cancel.
  have hcancel : (((1 + ‖η‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) * (((1 + ‖η‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) =
      1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity), neg_div, neg_add_cancel,
      Real.rpow_zero, Complex.ofReal_one]
  rw [hη, rellichKernel, sub_sub_cancel, smul_apply,
    ContinuousLinearMap.id_apply, smul_smul, smul_smul]
  congr 1
  push_cast
  linear_combination (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) * 𝓕 φ (ξ - η) * hcancel

/-- **Rellich's theorem for Bessel-potential spaces.** For a finite-dimensional complex inner
product space `F`, a scalar Schwartz function `φ` and real orders `r < s`, the operator
`u ↦ φ u` from `H^s(E, F)` to `H^r(E, F)` is compact. -/
theorem isCompactOperator_inclusion_comp_smulLeftCLM [FiniteDimensional ℂ F] (φ : 𝓢(E, ℂ))
    (h : r < s) :
    IsCompactOperator (inclusion h.le ∘L smulLeftCLM s φ : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) := by
  have heq : (inclusion h.le ∘L smulLeftCLM s φ : H^{s}(E, F) →L[ℂ] H^{r}(E, F)) =
      ((fourierWeighted (E := E) (F := F) r).symm :
          Lp F 2 (volume : Measure E) →L[ℂ] H^{r}(E, F)) ∘L rellichOperator φ h.le ∘L
        (fourierWeighted (E := E) (F := F) s : H^{s}(E, F) →L[ℂ] Lp F 2 (volume : Measure E)) := by
    rw [← fourierWeighted_comp_eq φ h.le, ← ContinuousLinearMap.comp_assoc]
    ext u
    simp
  rw [heq]
  exact ((isCompactOperator_rellichOperator (F := F) (φ := φ) h).comp_clm
    (fourierWeighted (E := E) (F := F) s : H^{s}(E, F) →L[ℂ] Lp F 2 (volume : Measure E))).clm_comp
    ((fourierWeighted (E := E) (F := F) r).symm : Lp F 2 (volume : Measure E) →L[ℂ] H^{r}(E, F))

/-- **Rellich's theorem for a common compact support.** For a finite-dimensional complex inner
product space `F`, a scalar Schwartz function `φ` and real orders `r < s`, a bounded subset `S` of
`H^s(E, F)` on which multiplication by `φ` is the identity has compact closure in `H^r(E, F)`.
For instance, `φ u = u` when `u` is supported in a compact set on a neighbourhood of which
`φ = 1`. -/
theorem isCompact_closure_image_inclusion_of_smulLeftCLM_eq [FiniteDimensional ℂ F]
    {φ : 𝓢(E, ℂ)} (h : r < s) {S : Set H^{s}(E, F)} (hS : Bornology.IsBounded S)
    (hφ : ∀ u ∈ S, smulLeftCLM s φ u = u) :
    IsCompact (closure (inclusion h.le '' S : Set H^{r}(E, F))) := by
  have himage : inclusion h.le '' S = (inclusion h.le ∘L smulLeftCLM s φ) '' S :=
    image_congr fun u hu ↦ by rw [ContinuousLinearMap.comp_apply, hφ u hu]
  rw [himage]
  exact (isCompactOperator_inclusion_comp_smulLeftCLM (F := F) φ h)
    |>.isCompact_closure_image_of_bounded hS

end BesselPotentialSpace
