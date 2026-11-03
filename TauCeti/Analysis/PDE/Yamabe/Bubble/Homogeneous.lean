/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Energy
public import TauCeti.Analysis.Sobolev.D1p0.Basic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Bubbles in the homogeneous Sobolev space

Aubin–Talenti bubbles belong to the native homogeneous space `D1p0 volume ⊤ 2` in every
real dimension greater than two. Expanding compactly supported cutoffs converge in the
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

/-- Outside the unit ball, a bubble is controlled by radius times its differential. -/
private theorem bubble_le_norm_mul_norm_fderiv (hn : 2 < finrank ℝ E)
    {t : ℝ} (ht : 0 < t) (b : E) {x : E} (hx : 1 ≤ ‖x - b‖) :
    bubble t b x ≤ (t ^ 2 + 1) / ((finrank ℝ E : ℝ) - 2) *
      ‖x - b‖ * ‖fderiv ℝ (bubble t b) x‖ := by
  have hd : 0 < (finrank ℝ E : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast hn)
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

private def cutoffBubble (t : ℝ) (b : E) (n : ℕ) (x : E) : ℝ :=
  (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : E))
    (((n : ℝ) + 1)⁻¹ • (x - b)) * bubble t b x

variable [FiniteDimensional ℝ E]

private theorem cutoffBubble_eventuallyEq (t : ℝ) (b x : E) :
    ∀ᶠ n : ℕ in atTop, cutoffBubble t b n =ᶠ[𝓝 x] bubble t b := by
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hlim : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ • (x - b)) atTop (𝓝 0) := by
    simpa only [one_div, zero_smul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (x - b)
  filter_upwards [hlim.eventually (eventually_eventually_nhds.2 χ.eventuallyEq_one)] with n hn
  have hnear := ((continuous_const_smul ((n : ℝ) + 1)⁻¹).comp
    (continuous_id.sub continuous_const)).continuousAt.eventually hn
  filter_upwards [hnear] with y hy
  have hy' : χ (((n : ℝ) + 1)⁻¹ • (y - b)) = 1 := hy
  simpa only [cutoffBubble] using (congrArg (· * bubble t b y) hy').trans (one_mul _)

private theorem cutoffBubble_smooth_compact {t : ℝ} (ht : 0 < t) (b : E) (n : ℕ) :
    ContDiff ℝ ∞ (cutoffBubble t b n) ∧ HasCompactSupport (cutoffBubble t b n) := by
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨(χ.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)).mul
      (contDiff_bubble ht.ne' b),
    ((χ.hasCompactSupport.comp_smul (by positivity : ((n : ℝ) + 1)⁻¹ ≠ 0)).comp_homeomorph
      (Homeomorph.subRight b)).mul_right⟩

variable [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
private theorem exists_bound_fderiv_cutoffBubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (x : E),
      ‖fderiv ℝ (cutoffBubble t b n) x - fderiv ℝ (bubble t b) x‖ ≤
        B * ‖fderiv ℝ (bubble t b) x‖ := by
  -- Compact support bounds radius times the cutoff derivative, uniformly under dilation.
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχd : Continuous (fun y : E ↦ ‖y‖ * ‖fderiv ℝ χ y‖) :=
    continuous_norm.mul ((χ.contDiff : ContDiff ℝ ∞ χ).continuous_fderiv (by simp)).norm
  have hχc : HasCompactSupport (fun y : E ↦ ‖y‖ * ‖fderiv ℝ χ y‖) :=
    (χ.hasCompactSupport.fderiv ℝ).norm.mul_left
  obtain ⟨C, hC⟩ := hχd.bounded_above_of_compact_support hχc
  have hC0 : 0 ≤ C := by simpa using hC 0
  let A : ℝ := (t ^ 2 + 1) / ((finrank ℝ E : ℝ) - 2)
  have hA : 0 ≤ A := by
    have hd : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
    dsimp [A]
    positivity
  have hbound (n : ℕ) (x : E) :
      ‖fderiv ℝ (cutoffBubble t b n) x - fderiv ℝ (bubble t b) x‖ ≤
        (C * A + 2) * ‖fderiv ℝ (bubble t b) x‖ := by
    let r : ℝ := (n : ℝ) + 1
    have hr : 1 ≤ r := by dsimp [r]; linarith [Nat.cast_nonneg (α := ℝ) n]
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    let ψ : E → ℝ := fun y ↦ χ (r⁻¹ • (y - b))
    have hψ : ContDiff ℝ ∞ ψ :=
      χ.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _)
    have hψd : fderiv ℝ ψ x = r⁻¹ • fderiv ℝ χ (r⁻¹ • (x - b)) := by
      have hc := fderiv_comp x ((χ.contDiff : ContDiff ℝ ∞ χ).differentiable (by simp) _)
        (((differentiable_id.sub_const b).const_smul r⁻¹).differentiableAt)
      rw [fderiv_const_smul ((differentiable_id.sub_const b) x),
        fderiv_sub_const, fderiv_id] at hc
      simpa only [Function.comp_def, Pi.smul_apply, id_eq,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using hc
    -- Away from the centre use the bubble's radial derivative; near it the cutoff is one.
    have hψbound : ‖fderiv ℝ ψ x‖ * bubble t b x ≤
        C * A * ‖fderiv ℝ (bubble t b) x‖ := by
      by_cases hx : 1 ≤ ‖x - b‖
      · have hs : ‖fderiv ℝ ψ x‖ * ‖x - b‖ ≤ C := by
          rw [hψd, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
          have hc := hC (r⁻¹ • (x - b))
          have hc' := (Real.le_norm_self _).trans hc
          simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le),
            mul_assoc, mul_comm ‖x - b‖] using hc'
        calc
          _ ≤ ‖fderiv ℝ ψ x‖ * (A * ‖x - b‖ * ‖fderiv ℝ (bubble t b) x‖) :=
            mul_le_mul_of_nonneg_left (bubble_le_norm_mul_norm_fderiv hn ht b hx) (norm_nonneg _)
          _ = (‖fderiv ℝ ψ x‖ * ‖x - b‖) * A * ‖fderiv ℝ (bubble t b) x‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs hA) (norm_nonneg _)
      · have heq : ψ =ᶠ[𝓝 x] 1 := by
          have hball : r⁻¹ • (x - b) ∈ Metric.ball (0 : E) χ.rIn := by
            simp only [Metric.mem_ball, dist_zero_right, norm_smul,
              Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
            exact (inv_mul_lt_one₀ hr0).mpr ((lt_of_not_ge hx).trans_le hr)
          exact ((continuous_const_smul r⁻¹).comp
            (continuous_id.sub continuous_const)).continuousAt.eventually
              (χ.eventuallyEq_one_of_mem_ball hball)
        have hz : fderiv ℝ ψ x = 0 := by simpa using heq.fderiv_eq
        rw [hz, norm_zero, zero_mul]
        positivity
    -- The product rule now dominates the full derivative error by the bubble's derivative.
    have hψval : |ψ x| ≤ 1 := by
      exact abs_le.mpr ⟨by linarith [χ.nonneg (x := r⁻¹ • (x - b))], χ.le_one⟩
    have hdprod : fderiv ℝ (cutoffBubble t b n) x =
        ψ x • fderiv ℝ (bubble t b) x + bubble t b x • fderiv ℝ ψ x :=
      fderiv_mul (hψ.differentiable (by simp) x)
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

/-- Expanding cutoffs converge in gradient norm without requiring an `L²` norm of the bubble. -/
private theorem tendsto_fderiv_cutoffBubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    Tendsto (fun n : ℕ ↦ eLpNorm (fderiv ℝ (cutoffBubble t b n) -
      fderiv ℝ (bubble t b)) 2 volume) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_bound_fderiv_cutoffBubble hn ht b
  apply tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num) (by norm_num)
    (Eventually.of_forall fun n ↦
      ((cutoffBubble_smooth_compact ht b n).1.continuous_fderiv (by simp)).aestronglyMeasurable)
    ((contDiff_bubble ht.ne' b : ContDiff ℝ ∞ _).continuous_fderiv (by simp)).aestronglyMeasurable
    ((memLp_fderiv_bubble volume hn ht b).norm.const_smul B)
  · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun x ↦ by
      simpa only [ENNReal.coe_one, one_mul, Pi.smul_apply, smul_eq_mul, Real.enorm_of_nonneg
        (mul_nonneg hB (norm_nonneg _)), ← ofReal_norm] using
          ENNReal.ofReal_le_ofReal (hbound n x)
  · exact Eventually.of_forall fun x ↦ (tendsto_congr'
      ((cutoffBubble_eventuallyEq t b x).mono fun n hn ↦ hn.fderiv_eq)).mpr tendsto_const_nhds

/-- A bubble admits smooth compactly supported approximations converging simultaneously in
critical `Lᵖ` and in the Dirichlet seminorm, in every dimension greater than two. -/
theorem exists_testFunction_approximation_bubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    ∃ φ : ℕ → 𝓓((⊤ : Opens E), ℝ),
      Tendsto (fun n ↦ eLpNorm ((φ n : E → ℝ) - bubble t b)
        (ENNReal.ofReal (criticalExponent (finrank ℝ E))) volume) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ eLpNorm (fderiv ℝ (φ n : E → ℝ) -
        fderiv ℝ (bubble t b)) 2 volume) atTop (𝓝 0) := by
  let φ (n : ℕ) : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨cutoffBubble t b n, (cutoffBubble_smooth_compact ht b n).1,
      (cutoffBubble_smooth_compact ht b n).2, subset_univ _⟩
  refine ⟨φ, ?_, tendsto_fderiv_cutoffBubble hn ht b⟩
  have hmem := memLp_bubble volume hn ht b
  apply tendsto_eLpNorm_sub_of_ae_tendsto (C := 1)
    (ENNReal.ofReal_pos.mpr (criticalExponent_pos hn)).ne' ENNReal.ofReal_ne_top
    (Eventually.of_forall fun n ↦ (φ n).contDiff.continuous.aestronglyMeasurable)
    hmem.aestronglyMeasurable hmem
  · exact Eventually.of_forall fun n ↦ Eventually.of_forall fun x ↦ by
      let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
      have hχ : |χ (((n : ℝ) + 1)⁻¹ • (x - b)) - 1| ≤ 1 :=
        abs_le.mpr ⟨by linarith [χ.nonneg (x := ((n : ℝ) + 1)⁻¹ • (x - b))],
          by linarith [χ.le_one (x := ((n : ℝ) + 1)⁻¹ • (x - b))]⟩
      have herr : ‖(φ n : E → ℝ) x - bubble t b x‖ ≤ ‖bubble t b x‖ := by
        have hval : (φ n : E → ℝ) x =
            χ (((n : ℝ) + 1)⁻¹ • (x - b)) * bubble t b x := by
          -- Evaluation of the test function is the cutoff profile used to construct it.
          rfl
        rw [hval, ← sub_one_mul, norm_mul]
        exact (mul_le_mul_of_nonneg_right hχ (norm_nonneg (bubble t b x))).trans_eq
          (one_mul _)
      simpa only [ENNReal.coe_one, one_mul, ← ofReal_norm] using
        ENNReal.ofReal_le_ofReal herr
  · exact Eventually.of_forall fun x ↦ (tendsto_congr'
      ((cutoffBubble_eventuallyEq t b x).mono fun n hn ↦ hn.eq_of_nhds)).mpr tendsto_const_nhds

/-- Every bubble is represented by an element of the native homogeneous Sobolev space, and
the recorded gradient is its classical gradient. In particular this includes dimensions three
and four, without any `L²` hypothesis on the bubble. -/
theorem exists_sobolevEmbeddingL_ae_eq_bubble (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    ∃ u : D1p0 volume (⊤ : Opens E) 2,
      (D1p0.sobolevEmbeddingL (ofReal_criticalExponent_inv_add_inv hn) u : E → ℝ)
        =ᵐ[volume] bubble t b ∧
      (u : Lp E 2 (volume.restrict (⊤ : Opens E))) =ᵐ[volume] ∇ (bubble t b) := by
  obtain ⟨φ, hfun, hderiv⟩ := exists_testFunction_approximation_bubble hn ht b
  have hcontGrad : Continuous (∇ (bubble t b)) :=
    ((contDiff_bubble ht.ne' b : ContDiff ℝ ∞ _).gradient_right (m := 0) (by simp)).continuous
  have hgrad : MemLp (∇ (bubble t b)) 2 volume := by
    refine (memLp_fderiv_bubble volume hn ht b).norm.mono'
      hcontGrad.aestronglyMeasurable ?_
    exact Eventually.of_forall fun x ↦ (norm_gradient_eq_norm_fderiv (bubble t b) x).le
  have hgrad' : MemLp (∇ (bubble t b)) 2 (volume.restrict (⊤ : Opens E)) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hgrad
  let G := hgrad'.toLp (∇ (bubble t b))
  -- Riesz isometry converts convergence of differentials to convergence of gradients.
  have hseq : Tendsto (fun n ↦ gradientTestFunctionLp (mu := volume) 2 (φ n))
      atTop (𝓝 G) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hgrad').mpr
    convert hderiv using 1
    funext n
    rw [eLpNorm_congr_ae (by
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 (φ n)] with x hx
      exact congrArg (· - ∇ (bubble t b) x) hx)]
    simp only [Opens.coe_top, Measure.restrict_univ]
    apply eLpNorm_congr_norm_ae
      (((continuous_gradient_testFunction (φ n)).sub hcontGrad).aestronglyMeasurable)
      (((φ n).contDiff.continuous_fderiv (by simp)).sub
        ((contDiff_bubble ht.ne' b : ContDiff ℝ ∞ _).continuous_fderiv (by simp))
          |>.aestronglyMeasurable)
    exact Eventually.of_forall fun x ↦ by
      simp only [gradient, ← map_sub, LinearIsometryEquiv.norm_map, Pi.sub_apply]
  -- The limiting gradient lies in the closed space generated by test-function gradients.
  have hG : G ∈ (d1p0Submodule volume (⊤ : Opens E) 2 : Set _) := by
    rw [coe_d1p0Submodule]
    exact isClosed_closure.mem_of_tendsto hseq
      (Eventually.of_forall fun n ↦ subset_closure ⟨φ n, rfl⟩)
  let u : D1p0 volume (⊤ : Opens E) 2 := ⟨G, hG⟩
  refine ⟨u, ?_, by simpa only [Opens.coe_top, Measure.restrict_univ] using hgrad'.coeFn_toLp⟩
  -- Continuity of the Sobolev embedding identifies its image with the critical-Lp limit.
  have huseq : Tendsto (fun n ↦ D1p0.ofTestFunctionₗ volume (⊤ : Opens E) 2 (φ n))
      atTop (𝓝 u) := by
    apply tendsto_subtype_rng.mpr
    simpa only [D1p0.coe_ofTestFunctionₗ] using hseq
  let p := ENNReal.ofReal (criticalExponent (finrank ℝ E))
  let _ : Fact (1 ≤ p) := ⟨one_le_of_inv_add_eq_inv (ofReal_criticalExponent_inv_add_inv hn)⟩
  have hmem : MemLp (bubble t b) p (volume.restrict (⊤ : Opens E)) := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using memLp_bubble volume hn ht b
  have hfseq : Tendsto (fun n ↦ testFunctionLp (mu := volume) p (φ n))
      atTop (𝓝 (hmem.toLp (bubble t b))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hmem).mpr
    convert hfun using 1
    funext n
    rw [eLpNorm_congr_ae (by
      filter_upwards [testFunctionLp_apply_ae (mu := volume) p (φ n)] with x hx
      exact congrArg (· - bubble t b x) hx)]
    simp only [Opens.coe_top, Measure.restrict_univ]
    -- `p` is the critical exponent, and function subtraction is pointwise.
    rfl
  have hemb := ((D1p0.sobolevEmbeddingL (mu := volume) (Omega := (⊤ : Opens E))
    (ofReal_criticalExponent_inv_add_inv hn)).continuous.tendsto u).comp huseq
  simp only [Function.comp_def,
    D1p0.sobolevEmbeddingL_ofTestFunctionₗ ENNReal.ofReal_ne_top] at hemb
  have heq := tendsto_nhds_unique hemb hfseq
  rw [heq]
  simpa only [Opens.coe_top, Measure.restrict_univ] using hmem.coeFn_toLp

end TauCeti.Yamabe
