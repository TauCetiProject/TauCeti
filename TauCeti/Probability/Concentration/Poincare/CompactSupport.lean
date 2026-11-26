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
    obtain ⟨g, hg, hgL, hlim, -, -⟩ := TauCeti.exists_contDiff_hasCompactSupport_approximation
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
  refine ⟨fun h f hf hc ↦ ?_, fun h ↦ (LogSobolevInequality_def _ _).2 fun f hf hdf hf2 hf2log ↦ ?_⟩
  · -- Compactly supported smooth functions automatically satisfy the `L²` and `L log L` bounds.
    have hc2 : HasCompactSupport (fun x ↦ f x ^ 2) := hc.comp_left (zero_pow two_ne_zero)
    exact h.apply f hf
      ((hf.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport (hc.fderiv ℝ).norm)
      (memLp_one_iff_integrable.1 <| (hf.continuous.pow 2).memLp_of_hasCompactSupport hc2)
      (memLp_one_iff_integrable.1 <|
        (Real.continuous_mul_log.comp (hf.continuous.pow 2)).memLp_of_hasCompactSupport
          (hc2.comp_left (g := fun t : ℝ ↦ t * Real.log t) (zero_mul _)))
  · -- Approximate `f` by `[0, 1]`-valued smooth cutoffs `g n` from the Sobolev cutoff lemma and
    -- pass to the limit in both `Ent_μ((g n)²)` (by dominated convergence) and `∫ ‖∇(g n)‖² dμ`.
    have hmem : ∀ i ≤ 1, MemLp (iteratedFDeriv ℝ i f) 2 μ := fun i hi ↦ by
      interval_cases i
      · exact ((memLp_two_iff_integrable_sq hf.continuous.aestronglyMeasurable).2 hf2).congr_norm
          (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
          (.of_forall fun _ ↦ norm_iteratedFDeriv_zero.symm)
      · exact hdf.congr_norm (hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
          (.of_forall fun _ ↦ by simp only [norm_norm, norm_iteratedFDeriv_one])
    obtain ⟨g, hg, hgL, hlim, hgnorm, hgpt⟩ :=
      TauCeti.exists_contDiff_hasCompactSupport_approximation
        (μ := μ) ENNReal.ofNat_ne_top (m := ⊤) hf 1 le_top hmem
    have henergy := tendsto_integral_norm_sq_of_tendsto_eLpNorm_sub (hmem 1 le_rfl)
      (fun n ↦ hgL n 1 le_rfl) (hlim 1 le_rfl)
    simp only [norm_iteratedFDeriv_one] at henergy
    have hent : Tendsto (fun n ↦ entropy μ (fun x ↦ g n x ^ 2)) atTop
        (𝓝 (entropy μ (fun x ↦ f x ^ 2))) :=
      tendsto_entropy_of_dominated (fun x ↦ f x ^ 2)
        (.of_forall fun n ↦ ((hg n).1.continuous.pow 2).aestronglyMeasurable)
        (.of_forall fun _ ↦ .of_forall fun _ ↦ sq_nonneg _)
        (.of_forall fun n ↦ .of_forall fun x ↦
          sq_le_sq.2 (by simpa only [Real.norm_eq_abs] using hgnorm n x))
        hf2 hf2log (.of_forall fun x ↦ (hgpt x).pow 2)
    exact le_of_tendsto_of_tendsto' hent (henergy.const_mul (2 * C))
      fun n ↦ h (g n) (hg n).1 (hg n).2

end MeasureTheory.Measure
