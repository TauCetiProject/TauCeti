/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.Analysis.Sobolev.SmoothCutoff
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

omit [IsFiniteMeasure μ] in
/-- Construct `[0, 1]`-valued expanding bump cutoffs `g n = χ ((n + 1)⁻¹ • ·) • f` that are smooth
and compactly supported, satisfy `(g n x)² ≤ (f x)²`, converge pointwise to `f`, and have gradient
energies converging to `∫ ‖∇f‖² dμ`. -/
private theorem exists_contDiff_hasCompactSupport_sq_le_tendsto {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf2 : Integrable (fun x ↦ f x ^ 2) μ)
    (hdf : MemLp (fun x ↦ ‖fderiv ℝ f x‖) 2 μ) :
    ∃ g : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (g n) ∧ HasCompactSupport (g n)) ∧
      (∀ n x, g n x ^ 2 ≤ f x ^ 2) ∧
      (∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (f x))) ∧
      Tendsto (fun n ↦ ∫ x, ‖fderiv ℝ (g n) x‖ ^ 2 ∂μ) atTop
        (𝓝 (∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ)) := by
  have hmem : ∀ i ≤ 1, MemLp (iteratedFDeriv ℝ i f) 2 μ := fun i hi ↦ by
    interval_cases i
    · exact ((memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).2 hf2).congr_norm
        (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
        (.of_forall fun _ ↦ norm_iteratedFDeriv_zero.symm)
    · exact hdf.congr_norm (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
        (.of_forall fun _ ↦ by simp only [norm_norm, norm_iteratedFDeriv_one])
  -- Rescale a `[0, 1]`-valued smooth bump `χ` equal to `1` near `0`; rescaling by `(n + 1)⁻¹ ≤ 1`
  -- keeps all derivatives uniformly bounded.
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  let g : ℕ → E → ℝ := fun n x ↦ χ (((n : ℝ) + 1)⁻¹ • x) • f x
  choose B hB using fun i : ℕ ↦
    (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (χ.hasCompactSupport.iteratedFDeriv i)
  have hscaled (n i : ℕ) (x : E) :
      ‖iteratedFDeriv ℝ i (fun y ↦ χ (((n : ℝ) + 1)⁻¹ • y)) x‖ ≤ B i := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [iteratedFDeriv_comp_const_smul _ (χ.contDiff.of_le (mod_cast le_top)),
      norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg hn.le]
    have hpow : (((n : ℝ) + 1)⁻¹) ^ i ≤ 1 := pow_le_one₀ (by positivity)
      (inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    simpa only [one_mul] using mul_le_mul hpow (hB i _) (norm_nonneg _) zero_le_one
  have henergy := tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub (hmem 1 le_rfl)
    (fun n ↦ TauCeti.memLp_iteratedFDeriv_smul_of_bounded
      ((χ.contDiff.comp (contDiff_const_smul _)).of_le (mod_cast le_top))
      (fun j _ x ↦ hscaled n j x) (hf.of_le (by simp)) hmem)
    (TauCeti.tendsto_eLpNorm_iteratedFDeriv_cutoff_sub ENNReal.ofNat_ne_top
      (r := fun n : ℕ ↦ (n : ℝ) + 1)
      (tendsto_atTop_mono (fun n ↦ by linarith) tendsto_natCast_atTop_atTop)
      (χ.contDiff.of_le (mod_cast le_top)) χ.eventuallyEq_one
      (fun j _ x ↦ hB j x) (hf.of_le (by simp)) hmem)
  simp only [norm_iteratedFDeriv_one] at henergy
  refine ⟨g, fun n ↦ ⟨(χ.contDiff.comp (contDiff_const_smul _)).smul hf,
      (χ.hasCompactSupport.comp_smul (by positivity : ((n : ℝ) + 1)⁻¹ ≠ 0)).smul_right⟩,
    fun n x ↦ sq_le_sq.2 ?_, fun x ↦ ?_, henergy⟩
  · simp only [g, smul_eq_mul, abs_mul, abs_of_nonneg χ.nonneg]
    exact mul_le_of_le_one_left (abs_nonneg _) χ.le_one
  · have ht : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 0) := by
      simpa only [one_div, zero_smul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const x
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [ht.eventually χ.eventuallyEq_one] with n hn using by simp [g, hn]

/-- On a finite measure space, the smooth-test logarithmic Sobolev inequality can be checked on
compactly supported smooth functions. -/
theorem logSobolevInequality_iff_forall_hasCompactSupport :
    LogSobolevInequality μ C ↔
      ∀ f : E → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        entropy μ (fun x ↦ f x ^ 2) ≤ 2 * C * ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  refine ⟨fun h f hf hc ↦ ?_, fun h ↦ (LogSobolevInequality_def _ _).2 fun f hf hdf hf2 hf2log ↦ ?_⟩
  · -- Compactly supported smooth functions automatically satisfy the `L²` and `L log L` bounds.
    have hc2 : HasCompactSupport (fun x ↦ f x ^ 2) := hc.comp_left (zero_pow two_ne_zero)
    exact h.apply f hf
      ((hf.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport (hc.fderiv ℝ).norm)
      (memLp_one_iff_integrable.1 <| (hf.continuous.pow 2).memLp_of_hasCompactSupport hc2)
      (memLp_one_iff_integrable.1 <|
        (Real.continuous_mul_log.comp (hf.continuous.pow 2)).memLp_of_hasCompactSupport
          (hc2.comp_left (g := fun t : ℝ ↦ t * Real.log t) (zero_mul _)))
  · -- Approximate `f` by `[0, 1]`-valued smooth cutoffs `g n` and pass to the limit in both
    -- `Ent_μ((g n)²)` (by dominated convergence) and `∫ ‖∇(g n)‖² dμ`.
    obtain ⟨g, hg, hgsq_le, hgpt, henergy⟩ :=
      exists_contDiff_hasCompactSupport_sq_le_tendsto hf hf2 hdf
    have hent : Tendsto (fun n ↦ entropy μ (fun x ↦ g n x ^ 2)) atTop
        (𝓝 (entropy μ (fun x ↦ f x ^ 2))) :=
      tendsto_entropy_of_dominated (fun x ↦ f x ^ 2)
        (.of_forall fun n ↦ ((hg n).1.continuous.pow 2).aestronglyMeasurable)
        (.of_forall fun _ ↦ .of_forall fun _ ↦ sq_nonneg _)
        (.of_forall fun n ↦ .of_forall (hgsq_le n))
        hf2 hf2log (.of_forall fun x ↦ (hgpt x).pow 2)
    exact le_of_tendsto_of_tendsto' hent (henergy.const_mul (2 * C))
      fun n ↦ h (g n) (hg n).1 (hg n).2

end MeasureTheory.Measure
