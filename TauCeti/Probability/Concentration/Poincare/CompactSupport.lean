/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Poincare.LogSobolev
import TauCeti.Analysis.Sobolev.SmoothCutoff
import TauCeti.Probability.Moments.Variance

/-!
# Compactly supported tests for the Poincaré inequality

For a finite measure on a finite-dimensional real normed space, it is enough to check
the smooth-test Poincaré inequality on compactly supported smooth functions. The existing
Sobolev cutoff approximation converges in both variance and derivative energy. The measure may be
singular, and the criterion holds for every real constant. As in the canonical inequality,
variance is centered by the unnormalized integral.

This permits a Poincaré estimate proved for bounded functions with bounded derivatives to
apply to the canonical square-integrable, finite-energy test class.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, §2.3.
* The cutoff argument is adapted from the KLS formalization,
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

end MeasureTheory.Measure
