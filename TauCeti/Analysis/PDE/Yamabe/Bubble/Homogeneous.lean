/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Energy
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Analysis.Sobolev.SmoothCutoff

/-!
# Bubbles in the homogeneous Sobolev space

Aubin–Talenti bubbles belong to the native homogeneous space `D1p0 μ ⊤ 2` for every
additive Haar measure `μ` in every real dimension greater than two. Expanding compactly
supported cutoffs converge in the
Dirichlet norm, including in dimensions three and four where the bubble itself need not
belong to `L²`. The Sobolev embedding of the resulting element is the original bubble.
This identifies the explicit extremal profiles with elements of the domain of the sharp
Sobolev inequality, rather than merely functions with finite formal energy.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., §§8.2–8.3.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, §3.
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open Filter MeasureTheory Module Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem finrank_sub_two_pos (hn : 2 < finrank ℝ E) :
    0 < (finrank ℝ E : ℝ) - 2 :=
  sub_pos.mpr (by exact_mod_cast hn)

private theorem bubble_fderiv_bound_nonneg (hn : 2 < finrank ℝ E) (t : ℝ) :
    0 ≤ (t ^ 2 + 1) / ((finrank ℝ E : ℝ) - 2) :=
  div_nonneg (by positivity) (finrank_sub_two_pos hn).le

/-- Outside the unit ball, a bubble is controlled by radius times its differential. -/
private theorem bubble_le_norm_mul_norm_fderiv (hn : 2 < finrank ℝ E)
    {t : ℝ} (ht : 0 < t) (b : E) {x : E} (hx : 1 ≤ ‖x - b‖) :
    bubble t b x ≤ (t ^ 2 + 1) / ((finrank ℝ E : ℝ) - 2) *
      ‖x - b‖ * ‖fderiv ℝ (bubble t b) x‖ := by
  have hd := finrank_sub_two_pos hn
  have hr : 1 ≤ ‖x - b‖ ^ 2 := one_le_pow₀ hx
  have hden : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  rw [norm_fderiv_bubble ht, abs_of_pos hd]
  have heq : (t ^ 2 + 1) / ((finrank ℝ E : ℝ) - 2) * ‖x - b‖ *
      (((finrank ℝ E : ℝ) - 2) * bubble t b x * ‖x - b‖ /
        (t ^ 2 + ‖x - b‖ ^ 2)) =
      bubble t b x * ((t ^ 2 + 1) * ‖x - b‖ ^ 2) / (t ^ 2 + ‖x - b‖ ^ 2) := by
    field_simp
  rw [heq, le_div_iff₀ hden]
  have hrad : t ^ 2 + ‖x - b‖ ^ 2 ≤ (t ^ 2 + 1) * ‖x - b‖ ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hr)]
  exact mul_le_mul_of_nonneg_left hrad (bubble_pos ht b x).le

private def bubbleCutoff : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

private def cutoffBubble (t : ℝ) (b : E) (n : ℕ) (x : E) : ℝ :=
  bubbleCutoff (E := E) (((n : ℝ) + 1)⁻¹ • (x - b)) * bubble t b x

private theorem cutoffBubble_eq (t : ℝ) (b : E) (n : ℕ) :
    cutoffBubble t b n = fun x ↦
      bubbleCutoff (E := E) (((n : ℝ) + 1)⁻¹ • (x - b)) * bubble t b x := rfl

private theorem cutoffBubble_apply (t : ℝ) (b : E) (n : ℕ) (x : E) :
    cutoffBubble t b n x =
      bubbleCutoff (E := E) (((n : ℝ) + 1)⁻¹ • (x - b)) * bubble t b x := rfl

variable [FiniteDimensional ℝ E]

private theorem rescaled_bubbleCutoff_eventuallyEq_one (r : ℝ) (b x : E)
    (hx : r⁻¹ • (x - b) ∈ Metric.ball (0 : E) 1) :
    (fun y ↦ bubbleCutoff (E := E) (r⁻¹ • (y - b))) =ᶠ[𝓝 x] 1 := by
  exact ((continuous_const_smul r⁻¹).comp
    (continuous_id.sub continuous_const)).continuousAt.eventually
      ((bubbleCutoff (E := E)).eventuallyEq_one_of_mem_ball hx)

private theorem cutoffBubble_eventuallyEq (t : ℝ) (b x : E) :
    ∀ᶠ n : ℕ in atTop, cutoffBubble t b n =ᶠ[𝓝 x] bubble t b := by
  have hlim : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ • (x - b)) atTop (𝓝 0) := by
    simpa only [one_div, zero_smul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (x - b)
  filter_upwards [hlim.eventually (Metric.ball_mem_nhds (0 : E) one_pos)] with n hn
  filter_upwards [rescaled_bubbleCutoff_eventuallyEq_one ((n : ℝ) + 1) b x hn] with y hy
  simp only [Pi.one_apply] at hy
  rw [cutoffBubble_apply, hy, one_mul]

private theorem cutoffBubble_smooth_compact {t : ℝ} (ht : 0 < t) (b : E) (n : ℕ) :
    ContDiff ℝ ∞ (cutoffBubble t b n) ∧ HasCompactSupport (cutoffBubble t b n) := by
  rw [cutoffBubble_eq]
  let χ : ContDiffBump (0 : E) := bubbleCutoff
  exact ⟨(χ.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)).mul
      (contDiff_bubble ht.ne' b),
    ((χ.hasCompactSupport.comp_smul (by positivity : ((n : ℝ) + 1)⁻¹ ≠ 0)).comp_homeomorph
      (Homeomorph.subRight b)).mul_right⟩

private theorem fderiv_rescaled_bubbleCutoff (r : ℝ) (b x : E) :
    fderiv ℝ (fun y ↦ bubbleCutoff (E := E) (r⁻¹ • (y - b))) x =
      r⁻¹ • fderiv ℝ (bubbleCutoff (E := E) : E → ℝ) (r⁻¹ • (x - b)) := by
  have hc := fderiv_comp x
    (((bubbleCutoff (E := E)).contDiff : ContDiff ℝ ∞ _).differentiable (by simp) _)
    (((differentiable_id.sub_const b).const_smul r⁻¹).differentiableAt)
  rw [fderiv_const_smul ((differentiable_id.sub_const b) x),
    fderiv_sub_const, fderiv_id] at hc
  simpa only [Function.comp_def, Pi.smul_apply, id_eq,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using hc

/-- The differentiated cutoff term is controlled by the bubble's radial derivative. -/
private theorem norm_fderiv_rescaled_bubbleCutoff_mul_bubble_le
    (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) {C : ℝ}
    (hC : ∀ y : E, ‖y‖ * ‖fderiv ℝ (bubbleCutoff (E := E) : E → ℝ) y‖ ≤ C)
    {r : ℝ} (hr : 1 ≤ r) (x : E) :
    ‖fderiv ℝ (fun y ↦ bubbleCutoff (E := E) (r⁻¹ • (y - b))) x‖ * bubble t b x ≤
      C * ((t ^ 2 + 1) / ((finrank ℝ E : ℝ) - 2)) * ‖fderiv ℝ (bubble t b) x‖ := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  let A : ℝ := (t ^ 2 + 1) / ((finrank ℝ E : ℝ) - 2)
  have hA : 0 ≤ A := bubble_fderiv_bound_nonneg hn t
  by_cases hx : 1 ≤ ‖x - b‖
  · have hs : ‖fderiv ℝ (fun y ↦ bubbleCutoff (E := E) (r⁻¹ • (y - b))) x‖ *
        ‖x - b‖ ≤ C := by
      rw [fderiv_rescaled_bubbleCutoff, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
      simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le),
        mul_assoc, mul_comm ‖x - b‖] using hC (r⁻¹ • (x - b))
    calc
      _ ≤ ‖fderiv ℝ (fun y ↦ bubbleCutoff (E := E) (r⁻¹ • (y - b))) x‖ *
          (A * ‖x - b‖ * ‖fderiv ℝ (bubble t b) x‖) :=
        mul_le_mul_of_nonneg_left (bubble_le_norm_mul_norm_fderiv hn ht b hx) (norm_nonneg _)
      _ = (‖fderiv ℝ (fun y ↦ bubbleCutoff (E := E) (r⁻¹ • (y - b))) x‖ * ‖x - b‖) *
          A * ‖fderiv ℝ (bubble t b) x‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hA) (norm_nonneg _)
  · have hball : r⁻¹ • (x - b) ∈ Metric.ball (0 : E) 1 := by
      simp only [Metric.mem_ball, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
      exact (inv_mul_lt_one₀ hr0).mpr ((lt_of_not_ge hx).trans_le hr)
    have hz : fderiv ℝ (fun y ↦ bubbleCutoff (E := E) (r⁻¹ • (y - b))) x = 0 := by
      simpa using (rescaled_bubbleCutoff_eventuallyEq_one r b x hball).fderiv_eq (𝕜 := ℝ)
    rw [hz, norm_zero, zero_mul]
    have hC0 : 0 ≤ C := by simpa using hC 0
    exact mul_nonneg (mul_nonneg hC0 hA) (norm_nonneg _)

private theorem exists_bound_fderiv_cutoffBubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (x : E),
      ‖fderiv ℝ (cutoffBubble t b n) x - fderiv ℝ (bubble t b) x‖ ≤
        B * ‖fderiv ℝ (bubble t b) x‖ := by
  -- Compact support bounds radius times the cutoff derivative, uniformly under dilation.
  let χ : ContDiffBump (0 : E) := bubbleCutoff
  have hχd : Continuous (fun y : E ↦ ‖y‖ * ‖fderiv ℝ χ y‖) :=
    continuous_norm.mul ((χ.contDiff : ContDiff ℝ ∞ χ).continuous_fderiv (by simp)).norm
  have hχc : HasCompactSupport (fun y : E ↦ ‖y‖ * ‖fderiv ℝ χ y‖) :=
    (χ.hasCompactSupport.fderiv ℝ).norm.mul_left
  obtain ⟨C, hC⟩ := hχd.bounded_above_of_compact_support hχc
  have hC0 : 0 ≤ C := by simpa using hC 0
  let A : ℝ := (t ^ 2 + 1) / ((finrank ℝ E : ℝ) - 2)
  have hA : 0 ≤ A := bubble_fderiv_bound_nonneg hn t
  have hbound (n : ℕ) (x : E) :
      ‖fderiv ℝ (cutoffBubble t b n) x - fderiv ℝ (bubble t b) x‖ ≤
        (C * A + 2) * ‖fderiv ℝ (bubble t b) x‖ := by
    let r : ℝ := (n : ℝ) + 1
    have hr : 1 ≤ r := by dsimp [r]; linarith [Nat.cast_nonneg (α := ℝ) n]
    let ψ : E → ℝ := fun y ↦ χ (r⁻¹ • (y - b))
    have hψ : ContDiff ℝ ∞ ψ :=
      χ.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)
    have hψbound : ‖fderiv ℝ ψ x‖ * bubble t b x ≤
        C * A * ‖fderiv ℝ (bubble t b) x‖ :=
      norm_fderiv_rescaled_bubbleCutoff_mul_bubble_le hn ht b
        (fun y ↦ (Real.le_norm_self _).trans (hC y)) hr x
    -- The product rule now dominates the full derivative error by the bubble's derivative.
    have hψval : |ψ x| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith [χ.nonneg (x := r⁻¹ • (x - b))], χ.le_one⟩
    have hdprod : fderiv ℝ (cutoffBubble t b n) x =
        ψ x • fderiv ℝ (bubble t b) x + bubble t b x • fderiv ℝ ψ x := by
      rw [cutoffBubble_eq]
      exact fderiv_mul (hψ.differentiable (by simp) x)
        ((contDiff_bubble ht.ne' b : ContDiff ℝ ∞ _).differentiable (by simp) x)
    rw [hdprod]
    calc
      _ ≤ ‖ψ x • fderiv ℝ (bubble t b) x + bubble t b x • fderiv ℝ ψ x‖ +
          ‖fderiv ℝ (bubble t b) x‖ := norm_sub_le _ _
      _ ≤ ‖ψ x • fderiv ℝ (bubble t b) x‖ + ‖bubble t b x • fderiv ℝ ψ x‖ +
          ‖fderiv ℝ (bubble t b) x‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (bubble_pos ht b x)]
        nlinarith [mul_le_mul_of_nonneg_right hψval (norm_nonneg (fderiv ℝ (bubble t b) x))]
  exact ⟨C * A + 2, by positivity, hbound⟩

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- Expanding cutoffs converge in gradient norm without requiring an `L²` norm of the bubble. -/
private theorem tendsto_fderiv_cutoffBubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    Tendsto (fun n : ℕ ↦ eLpNorm (fderiv ℝ (cutoffBubble t b n) -
      fderiv ℝ (bubble t b)) 2 μ) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_fderiv_cutoffBubble hn ht b
  apply tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num) (by norm_num)
    (Eventually.of_forall fun n ↦
      ((cutoffBubble_smooth_compact ht b n).1.continuous_fderiv (by simp)).aestronglyMeasurable)
    ((contDiff_bubble ht.ne' b : ContDiff ℝ ∞ _).continuous_fderiv (by simp)).aestronglyMeasurable
    ((memLp_fderiv_bubble μ hn ht b).norm.const_smul B)
  · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun x ↦ by
      simpa only [ENNReal.coe_one, one_mul, Pi.smul_apply, smul_eq_mul, Real.enorm_of_nonneg
        (mul_nonneg hB (norm_nonneg _)), ← ofReal_norm] using
          ENNReal.ofReal_le_ofReal (hbound n x)
  · exact Eventually.of_forall fun x ↦ (tendsto_congr'
      ((cutoffBubble_eventuallyEq t b x).mono fun n hn ↦ hn.fderiv_eq)).mpr tendsto_const_nhds

private theorem tendsto_cutoffBubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    Tendsto (fun n : ℕ ↦ eLpNorm (cutoffBubble t b n - bubble t b)
      (ENNReal.ofReal (criticalExponent (finrank ℝ E))) μ) atTop (𝓝 0) := by
  -- Apply the general cutoff theorem at the origin, then translate the same sequence by `b`.
  let χ : ContDiffBump (0 : E) := bubbleCutoff
  have hmem (i : ℕ) (hi : i ≤ 0) :
      MemLp (iteratedFDeriv ℝ i (bubble t (0 : E)))
        (ENNReal.ofReal (criticalExponent (finrank ℝ E))) μ := by
    obtain rfl : i = 0 := by omega
    exact (memLp_congr_norm
      (((contDiff_bubble ht.ne' (0 : E) : ContDiff ℝ ∞ _).continuous_iteratedFDeriv
        (by simp)).aestronglyMeasurable)
      (memLp_bubble μ hn ht 0).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ norm_iteratedFDeriv_zero)).mpr (memLp_bubble μ hn ht 0)
  have h := tendsto_eLpNorm_iteratedFDeriv_cutoff_sub
    (ENNReal.ofReal_pos.mpr (criticalExponent_pos hn)).ne' ENNReal.ofReal_ne_top
    (χ.contDiff : ContDiff ℝ 0 (χ : E → ℝ)) χ.eventuallyEq_one
    (B := fun _ ↦ 1) (fun i hi x ↦ by
      obtain rfl : i = 0 := by omega
      simpa only [norm_iteratedFDeriv_zero, Real.norm_of_nonneg χ.nonneg] using χ.le_one)
    ((contDiff_bubble ht.ne' 0 : ContDiff ℝ ∞ _).of_le (by simp)) hmem
  have heq (n : ℕ) : eLpNorm (cutoffBubble t b n - bubble t b)
      (ENNReal.ofReal (criticalExponent (finrank ℝ E))) μ =
      eLpNorm (iteratedFDeriv ℝ 0 (fun x ↦ χ (((n : ℝ) + 1)⁻¹ • x) •
        bubble t (0 : E) x) - iteratedFDeriv ℝ 0 (bubble t (0 : E)))
        (ENNReal.ofReal (criticalExponent (finrank ℝ E))) μ := by
    trans eLpNorm (cutoffBubble t 0 n - bubble t 0)
      (ENNReal.ofReal (criticalExponent (finrank ℝ E))) μ
    · rw [← eLpNorm_comp_measurePreserving
        (((cutoffBubble_smooth_compact ht 0 n).1.continuous.sub
          (contDiff_bubble ht.ne' 0 : ContDiff ℝ ∞ _).continuous).aestronglyMeasurable)
        (measurePreserving_sub_right μ b)]
      congr 1
      funext x
      simp only [Pi.sub_apply, Function.comp_apply, cutoffBubble_apply, sub_zero,
        bubble_zero_sub]
    apply eLpNorm_congr_norm_ae
      (((cutoffBubble_smooth_compact ht 0 n).1.continuous.sub
        (contDiff_bubble ht.ne' 0 : ContDiff ℝ ∞ _).continuous).aestronglyMeasurable)
      ((((χ.contDiff.comp (contDiff_const_smul _)).smul
        (contDiff_bubble ht.ne' 0 : ContDiff ℝ ∞ _)).continuous_iteratedFDeriv (by simp)
        |>.sub ((contDiff_bubble ht.ne' 0 : ContDiff ℝ ∞ _).continuous_iteratedFDeriv
          (by simp))).aestronglyMeasurable)
    exact Eventually.of_forall fun x ↦ by
      simp only [χ, Pi.sub_apply, Pi.mul_apply, Function.comp_apply, cutoffBubble_apply,
        sub_zero, iteratedFDeriv_zero_eq_comp, ← map_sub,
        LinearIsometryEquiv.norm_map, smul_eq_mul]
  simpa only [← heq] using h

/-- A bubble admits smooth compactly supported approximations converging simultaneously in
critical `Lᵖ` and in the Dirichlet seminorm for every additive Haar measure, in every
dimension greater than two. -/
theorem exists_testFunction_approximation_bubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    ∃ φ : ℕ → 𝓓((⊤ : Opens E), ℝ),
      Tendsto (fun n ↦ eLpNorm ((φ n : E → ℝ) - bubble t b)
        (ENNReal.ofReal (criticalExponent (finrank ℝ E))) μ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fderiv ℝ (φ n : E → ℝ) -
        fderiv ℝ (bubble t b)) 2 μ) atTop (𝓝 0) := by
  let φ (n : ℕ) : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨cutoffBubble t b n, (cutoffBubble_smooth_compact ht b n).1,
      (cutoffBubble_smooth_compact ht b n).2, subset_univ _⟩
  refine ⟨φ, ?_, ?_⟩
  · simpa only [φ, TestFunction.coe_mk] using tendsto_cutoffBubble μ hn ht b
  · simpa only [φ, TestFunction.coe_mk] using tendsto_fderiv_cutoffBubble μ hn ht b

/-- Every bubble is represented by an element of the native homogeneous Sobolev space, and
the recorded gradient is its classical gradient, for every additive Haar measure. In particular
this includes dimensions three and four, without any `L²` hypothesis on the bubble. -/
theorem exists_sobolevEmbeddingL_ae_eq_bubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    ∃ u : D1p0 μ (⊤ : Opens E) 2,
      (D1p0.sobolevEmbeddingL (inv_ofReal_criticalExponent_add_inv_eq_inv hn) u : E → ℝ)
        =ᵐ[μ] bubble t b ∧
      (u : Lp E 2 (μ.restrict (⊤ : Opens E))) =ᵐ[μ] ∇ (bubble t b) := by
  obtain ⟨φ, hfun, hderiv⟩ := exists_testFunction_approximation_bubble μ hn ht b
  have hcontGrad : Continuous (∇ (bubble t b)) :=
    ((contDiff_bubble ht.ne' b : ContDiff ℝ ∞ _).gradient_right (m := 0) (by simp)).continuous
  have hgrad : MemLp (∇ (bubble t b)) 2 μ := by
    refine (memLp_fderiv_bubble μ hn ht b).norm.mono'
      hcontGrad.aestronglyMeasurable ?_
    exact Eventually.of_forall fun x ↦ (norm_gradient_eq_norm_fderiv (bubble t b) x).le
  have hgradient : Tendsto (fun n ↦ eLpNorm (∇ (φ n : E → ℝ) - ∇ (bubble t b)) 2 μ)
      atTop (𝓝 0) := by
    -- The Riesz isometry preserves the norm of the difference, not just individual norms.
    convert hderiv using 1
    funext n
    apply eLpNorm_congr_norm_ae
      (((continuous_gradient_testFunction (φ n)).sub hcontGrad).aestronglyMeasurable)
      (((φ n).contDiff.continuous_fderiv (by simp)).sub
        ((contDiff_bubble ht.ne' b : ContDiff ℝ ∞ _).continuous_fderiv (by simp))
          |>.aestronglyMeasurable)
    exact Eventually.of_forall fun x ↦
      norm_gradient_sub_gradient_eq_norm_fderiv_sub (φ n : E → ℝ) (bubble t b) x
  have hmem := memLp_bubble μ hn ht b
  simpa only [Opens.coe_top, Measure.restrict_univ] using
    (D1p0.exists_sobolevEmbeddingL_ae_eq_of_tendsto (mu := μ) (Omega := (⊤ : Opens E))
      ENNReal.ofReal_ne_top (inv_ofReal_criticalExponent_add_inv_eq_inv hn)
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hmem)
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hgrad) φ
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hfun)
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hgradient))

end TauCeti.Yamabe
