/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import TauCeti.Analysis.SpecialFunctions.Gaussian.LatticeSum

/-!
# Periodizing the real Gaussian density

Summing the Gaussian density with mean `m` and variance `v ≠ 0` over the translates `x + k • T`
of a point by a nonzero period `T` gives a rescaled Gaussian lattice sum:

`∑ k : ℤ, gaussianPDFReal m v (x + k • T) = (√(2 * π * v))⁻¹ * Z((m - x) / T, √v / T)`,

where `Z` is `Real.gaussianLatticeSum`. At variance zero every term vanishes and both sides are
zero, so the periodized density is summable at every variance. The direct density series converges
locally uniformly in `x`, so it can be integrated term by term on compact intervals when computing
wrapped Gaussian probabilities.
-/

public section

open ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

/-- A translated density term in the coordinates used by the Gaussian lattice sum. -/
private theorem gaussianPDFReal_add_zsmul_eq (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0)
    {T : ℝ} (hT : T ≠ 0) (x : ℝ) (k : ℤ) :
    gaussianPDFReal m v (x + k • T) =
      (√(2 * π * v))⁻¹ * rexp (-((k : ℝ) - (m - x) / T) ^ 2 / (2 * (√(v : ℝ) / T) ^ 2)) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [gaussianPDFReal]
  congr 2
  rw [div_pow, sq_sqrt hv'.le, zsmul_eq_mul]
  field_simp
  ring

/-- The direct periodized Gaussian density series converges locally uniformly to the rescaled
Gaussian lattice sum. This includes variance zero, when every density term vanishes. -/
theorem hasSumLocallyUniformly_gaussianPDFReal_add_zsmul (m : ℝ) (v : ℝ≥0)
    {T : ℝ} (hT : T ≠ 0) :
    HasSumLocallyUniformly
      (fun k : ℤ => fun x : ℝ => gaussianPDFReal m v (x + k • T))
      (fun x => (√(2 * π * v))⁻¹ * gaussianLatticeSum ((m - x) / T) (√(v : ℝ) / T)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp only [gaussianPDFReal_zero_var, NNReal.coe_zero, mul_zero, sqrt_zero, inv_zero,
      zero_mul]
    apply hasSumLocallyUniformly_of_forall_compact
    intro K _
    simpa using HasSumUniformlyOn.of_norm_le_summable
      (f := fun (_ : ℤ) (_ : ℝ) => (0 : ℝ)) summable_zero (s := K) (by simp)
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : √(v : ℝ) / T ≠ 0 := div_ne_zero (sqrt_ne_zero'.mpr hv') hT
  have h := hasSumLocallyUniformly_gaussianLatticeSum hs
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly] at h ⊢
  have hc : Continuous (fun x : ℝ => (m - x) / T) := by fun_prop
  have hl := Real.uniformContinuous_const_mul
    (x := (√(2 * π * v))⁻¹) |>.comp_tendstoLocallyUniformly
      (h.comp (fun x : ℝ => (m - x) / T) hc)
  simp only [Function.comp_def] at hl
  convert hl using 1
  funext K x
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => gaussianPDFReal_add_zsmul_eq m hv hT x k

/-- Periodizing a Gaussian density gives a rescaled Gaussian lattice sum. At variance zero both
sides vanish. -/
theorem hasSum_gaussianPDFReal_add_zsmul (m : ℝ) (v : ℝ≥0) {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasSum (fun k : ℤ ↦ gaussianPDFReal m v (x + k • T))
      ((√(2 * π * v))⁻¹ * gaussianLatticeSum ((m - x) / T) (√(v : ℝ) / T)) :=
  (hasSumLocallyUniformly_gaussianPDFReal_add_zsmul m v hT).tendstoLocallyUniformlyOn.tendsto_at
    (Set.mem_univ x)

/-- The translates of a point by the multiples of a nonzero period give a summable family of
Gaussian densities, at every variance. -/
theorem summable_gaussianPDFReal_add_zsmul (m : ℝ) (v : ℝ≥0) {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    Summable fun k : ℤ ↦ gaussianPDFReal m v (x + k • T) :=
  (hasSum_gaussianPDFReal_add_zsmul m v hT x).summable

end TauCeti.Probability
