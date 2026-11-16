/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Calculus.ContDiff.Scaling
import TauCeti.Analysis.Sobolev.SmoothCutoff
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.Probability.Moments.Variance

/-!
# Compactly supported tests for Poincaré and logarithmic Sobolev inequalities

For a finite measure on a finite-dimensional real normed space, it is enough to check either the
smooth-test Poincaré inequality or the smooth-test logarithmic Sobolev inequality on compactly
supported smooth functions. Expanding smooth bump cutoffs `χ ((n + 1)⁻¹ • x) * f x` converge to `f`
in `L²` together with their first derivatives, while `0 ≤ χ ≤ 1` dominates `(χ_n f)²` by `f²` and
`|(χ_n f)² log (χ_n f)²|` by `1 + |f² log f²|`. The measure may be singular, and both criteria hold
for every real constant `C`.

This permits Poincaré and logarithmic Sobolev estimates proved for bounded functions with bounded
derivatives to apply to the full canonical smooth test classes.

## Main results

* `MeasureTheory.Measure.poincareInequality_iff_forall_hasCompactSupport`: compactly supported
  smooth tests suffice for `PoincareInequality`.
* `MeasureTheory.Measure.logSobolevInequality_iff_forall_hasCompactSupport`: compactly supported
  smooth tests suffice for `LogSobolevInequality`.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, §2.3.
* D. Bakry, I. Gentil and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*,
  Springer (2014), Proposition 5.1.3.
* The Poincaré cutoff argument is adapted from the KLS formalization,
  `FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean`, at
  https://github.com/human-ai-mathematics/kls-lean/tree/65810c73f9dd7945fc646ab484cb19d673f5291d.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ContDiff Topology

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {C : ℝ}

/-- On a finite measure space, the smooth-test Poincaré inequality can be checked on compactly
supported smooth functions. -/
theorem poincareInequality_iff_forall_hasCompactSupport :
    PoincareInequality μ C ↔
      ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        variance f μ ≤ C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  constructor
  · intro h f hf hc
    exact h.apply f hf (hf.continuous.memLp_of_hasCompactSupport hc)
      ((hf.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport (hc.fderiv ℝ).norm)
  · intro h
    rw [PoincareInequality_def]
    intro f hf hfL hdf
    -- The existing Sobolev approximation controls values and first derivatives in L².
    have hmem : ∀ i ≤ 1, MemLp (iteratedFDeriv ℝ i f) 2 μ := by
      intro i hi
      interval_cases i
      · exact hfL.congr_norm
          (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
          (.of_forall fun x ↦ norm_iteratedFDeriv_zero.symm)
      · exact hdf.congr_norm
          (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
          (.of_forall fun x ↦ by simp only [norm_norm, norm_iteratedFDeriv_one])
    obtain ⟨g, hg, hgL, hlim⟩ := TauCeti.exists_contDiff_hasCompactSupport_approximation
      (μ := μ) ENNReal.ofNat_ne_top (m := ⊤) hf 1 le_top hmem
    have hvalue : Tendsto (fun n ↦ eLpNorm (g n - f) 2 μ) atTop (𝓝 0) :=
      (hlim 0 zero_le_one).congr fun n ↦ eLpNorm_congr_norm_ae
        (((hg n).1.continuous_iteratedFDeriv (by simp)).sub
          (hf.continuous_iteratedFDeriv (by simp))).aestronglyMeasurable
        ((hg n).1.continuous.sub hf.continuous).aestronglyMeasurable
        (.of_forall fun x ↦ by
          simp only [iteratedFDeriv_zero_eq_comp, Pi.sub_apply, Function.comp_apply,
            ← map_sub, LinearIsometryEquiv.norm_map])
    have hgL₂ (n : ℕ) : MemLp (g n) 2 μ :=
      (hgL n 0 zero_le_one).congr_norm (hg n).1.continuous.aestronglyMeasurable
        (.of_forall fun x ↦ norm_iteratedFDeriv_zero)
    -- L² continuity supplies both limits, without a sign restriction on C.
    have hvar := tendsto_variance_of_tendsto_eLpNorm_sub hfL hgL₂ hvalue
    have henergy := tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub (hmem 1 le_rfl)
      (fun n ↦ hgL n 1 le_rfl) (hlim 1 le_rfl)
    simp only [norm_iteratedFDeriv_one] at henergy
    exact le_of_tendsto_of_tendsto' hvar (henergy.const_mul C)
      fun n ↦ h (g n) (hg n).1 (hg n).2

/-- On a finite measure space, the smooth-test logarithmic Sobolev inequality can be checked on
compactly supported smooth functions. -/
theorem logSobolevInequality_iff_forall_hasCompactSupport :
    LogSobolevInequality μ C ↔
      ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        entropy μ (fun x ↦ f x ^ 2) ≤ 2 * C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  constructor
  · intro h f hf hc
    have hdf : MemLp (fun x ↦ ‖fderiv ℝ f x‖) 2 μ :=
      (hf.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport (hc.fderiv ℝ).norm
    have hc2 : HasCompactSupport (fun x ↦ f x ^ 2) := hc.comp_left (zero_pow two_ne_zero)
    have hf2 : Integrable (fun x ↦ f x ^ 2) μ :=
      memLp_one_iff_integrable.1 <| (hf.continuous.pow 2).memLp_of_hasCompactSupport hc2
    have hf2log : Integrable (fun x ↦ f x ^ 2 * Real.log (f x ^ 2)) μ :=
      memLp_one_iff_integrable.1 <|
        (Real.continuous_mul_log.comp (hf.continuous.pow 2)).memLp_of_hasCompactSupport
          (hc2.comp_left (g := fun t : ℝ ↦ t * Real.log t) (zero_mul _))
    exact h.apply f hf hdf hf2 hf2log
  · intro h
    rw [LogSobolevInequality_def]
    intro f hf hdf hf2 hf2log
    have hfL : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).2 hf2
    have hmem : ∀ i ≤ 1, MemLp (iteratedFDeriv ℝ i f) 2 μ := by
      intro i hi
      interval_cases i
      · exact hfL.congr_norm
          (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
          (.of_forall fun x ↦ norm_iteratedFDeriv_zero.symm)
      · exact hdf.congr_norm
          (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
          (.of_forall fun x ↦ by simp only [norm_norm, norm_iteratedFDeriv_one])
    -- Expanding `[0, 1]`-valued smooth cutoffs dominate `(g n)²` by `f²` and converge in `H¹`.
    let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
    let g : ℕ → E → ℝ := fun n x ↦ χ (((n : ℝ) + 1)⁻¹ • x) • f x
    have hbdd (i : ℕ) : ∃ B, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B :=
      (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
        (χ.hasCompactSupport.iteratedFDeriv i)
    choose B hB using hbdd
    have hscaled (n i : ℕ) (x : E) :
        ‖iteratedFDeriv ℝ i (fun y ↦ χ (((n : ℝ) + 1)⁻¹ • y)) x‖ ≤ B i := by
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [iteratedFDeriv_comp_const_smul _ (χ.contDiff.of_le (mod_cast le_top)),
        norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg hn.le]
      have hpow : (((n : ℝ) + 1)⁻¹) ^ i ≤ 1 :=
        pow_le_one₀ (by positivity)
          (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
      simpa only [one_mul] using mul_le_mul hpow (hB i _) (norm_nonneg _) zero_le_one
    have hgs (n : ℕ) : ContDiff ℝ ∞ (g n) :=
      (χ.contDiff.comp (contDiff_const_smul _)).smul hf
    have hgc (n : ℕ) : HasCompactSupport (g n) :=
      (χ.hasCompactSupport.comp_smul (by positivity : ((n : ℝ) + 1)⁻¹ ≠ 0)).smul_right
    have hg1L (n : ℕ) : MemLp (iteratedFDeriv ℝ 1 (g n)) 2 μ :=
      TauCeti.memLp_iteratedFDeriv_smul_of_bounded
        ((χ.contDiff.comp (contDiff_const_smul _)).of_le (mod_cast le_top))
        (fun j _ x ↦ hscaled n j x) (hf.of_le (by simp)) hmem
    have hlim1 : Tendsto (fun n ↦
        eLpNorm (iteratedFDeriv ℝ 1 (g n) - iteratedFDeriv ℝ 1 f) 2 μ) atTop (𝓝 0) :=
      TauCeti.tendsto_eLpNorm_iteratedFDeriv_cutoff_sub ENNReal.ofNat_ne_top
        (r := fun n : ℕ ↦ (n : ℝ) + 1)
        (tendsto_atTop_mono (fun n : ℕ ↦ by linarith) tendsto_natCast_atTop_atTop)
        (χ.contDiff.of_le (mod_cast le_top)) χ.eventuallyEq_one
        (fun j _ x ↦ hB j x) (hf.of_le (by simp)) hmem
    have henergy := tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub (hmem 1 le_rfl) hg1L hlim1
    simp only [norm_iteratedFDeriv_one] at henergy
    -- Pointwise convergence and monotone domination of `(g n)²` and `(g n)² log ((g n)²)`.
    have hgsq_le (n : ℕ) (x : E) : g n x ^ 2 ≤ f x ^ 2 := by
      have habs : |g n x| ≤ |f x| := by
        simp only [g, smul_eq_mul, abs_mul, abs_of_nonneg χ.nonneg]
        exact mul_le_of_le_one_left (abs_nonneg _) χ.le_one
      exact (sq_le_sq.2 habs)
    have hgpt (x : E) : Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
      have ht : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x
        rw [zero_smul] at h0
        simpa only [one_div] using h0
      refine (tendsto_congr' ?_).2 tendsto_const_nhds
      filter_upwards [ht.eventually χ.eventuallyEq_one] with n hn
      simp [g, hn]
    have hlim_sq : Tendsto (fun n ↦ ∫ x, g n x ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun x ↦ f x ^ 2)
        (fun n ↦ ((hgs n).continuous.pow 2).aestronglyMeasurable) hf2
        (fun n ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ (hgpt x).pow 2)
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hgsq_le n x
    have hlim_mul_log : Tendsto (fun n ↦ ∫ x, g n x ^ 2 * Real.log (g n x ^ 2) ∂μ) atTop
        (𝓝 (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun x ↦ 1 + ‖f x ^ 2 * Real.log (f x ^ 2)‖)
        (fun n ↦ (Real.continuous_mul_log.comp
          ((hgs n).continuous.pow 2)).aestronglyMeasurable)
        ((integrable_const 1).add hf2log.norm) (fun n ↦ .of_forall fun x ↦ ?_)
        (.of_forall fun x ↦ Real.continuous_mul_log.continuousAt.tendsto.comp ((hgpt x).pow 2))
      simpa only [Real.norm_eq_abs] using
        TauCeti.abs_mul_log_le_one_add_abs_mul_log (sq_nonneg _) (hgsq_le n x)
    have hent : Tendsto (fun n ↦ entropy μ (fun x ↦ g n x ^ 2)) atTop
        (𝓝 (entropy μ (fun x ↦ f x ^ 2))) := by
      simp_rw [entropy_def]
      exact hlim_mul_log.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hlim_sq)
    exact le_of_tendsto_of_tendsto' hent (henergy.const_mul (2 * C))
      fun n ↦ h (g n) (hgs n) (hgc n)

end MeasureTheory.Measure
