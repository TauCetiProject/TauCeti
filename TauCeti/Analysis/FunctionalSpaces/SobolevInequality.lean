/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Analysis.Sobolev.SmoothCutoff

/-!
# The Gagliardo–Nirenberg–Sobolev inequality for integrable functions

Mathlib's Gagliardo–Nirenberg–Sobolev inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`
bounds `‖u‖_p`, for `p = n / (n - 1)`, by `C ‖Du‖₁` for a compactly supported `C¹` function `u`
on a space of dimension `n ≥ 2`, where `C = MeasureTheory.eLpNormLESNormFDerivOneConst μ p`.
This file removes the compact support hypothesis: the same inequality, with the same constant,
holds for every integrable `C¹` function, with `‖Du‖₁` finite or infinite.

The constant is positive (`TauCeti.eLpNormLESNormFDerivOneConst_pos`), as one sees by applying
the inequality to a bump function; this is what makes the inequality meaningful when `‖Du‖₁` is
infinite. When `‖Du‖₁` is finite, the compactly supported functions `χ(x / R) u(x)`, for a bump
function `χ` equal to one near zero, converge to `u` in `L¹` and their derivatives converge to
`Du` in `L¹` (`TauCeti.tendsto_eLpNorm_iteratedFDeriv_cutoff_sub`). Mathlib's inequality holds
for each of them, and Fatou's lemma along an almost everywhere convergent subsequence passes it
to `u`.

## Main results

* `TauCeti.eLpNormLESNormFDerivOneConst_pos`: the constant of the Gagliardo–Nirenberg–Sobolev
  inequality is positive.
* `TauCeti.eLpNorm_le_eLpNorm_fderiv_one_of_integrable`: the Gagliardo–Nirenberg–Sobolev
  inequality for integrable `C¹` functions.

## References

* L. C. Evans, *Partial Differential Equations*, §5.6.1, Theorem 1.
-/

public section

namespace TauCeti

open MeasureTheory Module Filter
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The constant `MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the Gagliardo–Nirenberg–
Sobolev inequality `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one` is positive. -/
theorem eLpNormLESNormFDerivOneConst_pos {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) : 0 < eLpNormLESNormFDerivOneConst μ p := by
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  refine pos_iff_ne_zero.2 fun h => ?_
  have hle := eLpNorm_le_eLpNorm_fderiv_one μ (χ.contDiff (n := 1)) χ.hasCompactSupport hp
  rw [h, ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero,
    eLpNorm_eq_zero_iff (by exact_mod_cast hp.symm.pos.ne')] at hle
  -- The bump vanishes almost everywhere, but its support is the open ball `ball 0 2`.
  refine (Metric.measure_ball_pos μ (0 : E) two_pos).ne' ?_
  rw [← χ.support_eq]
  exact ae_iff.1 hle

/-- **The Gagliardo–Nirenberg–Sobolev inequality for integrable functions.** Let `E` have
dimension `n ≥ 2` and let `p = n / (n - 1)`. Every integrable `C¹` function `u` satisfies
`‖u‖_p ≤ C ‖Du‖₁`, with `‖Du‖₁` finite or infinite, where `C` is the constant
`MeasureTheory.eLpNormLESNormFDerivOneConst μ p` of the compactly supported case
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`. -/
theorem eLpNorm_le_eLpNorm_fderiv_one_of_integrable {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {u : E → F} (hu : ContDiff ℝ 1 u) (hi : Integrable u μ) {p : ℝ≥0}
    (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p * eLpNorm (fderiv ℝ u) 1 μ := by
  set C := eLpNormLESNormFDerivOneConst μ p
  have hdu : AEStronglyMeasurable (fderiv ℝ u) μ :=
    (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable
  rcases eq_or_ne (eLpNorm (fderiv ℝ u) 1 μ) ∞ with htop | htop
  · rw [htop, ENNReal.mul_top (by exact_mod_cast (eLpNormLESNormFDerivOneConst_pos μ hp).ne')]
    exact le_top
  -- The cutoffs `g n = χ((n + 1)⁻¹ x) u(x)` of a bump `χ` equal to one near zero.
  let χ : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
  have hbdd (i : ℕ) : ∃ B, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B :=
    (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (χ.hasCompactSupport.iteratedFDeriv i)
  choose B hB using hbdd
  set g : ℕ → E → F := fun n x => χ (((n : ℝ) + 1)⁻¹ • x) • u x
  have hg (n : ℕ) : ContDiff ℝ 1 (g n) := (χ.contDiff.comp (contDiff_const_smul _)).smul hu
  have hgc (n : ℕ) : HasCompactSupport (g n) :=
    (χ.hasCompactSupport.comp_smul (by positivity : ((n : ℝ) + 1)⁻¹ ≠ 0)).smul_right
  have hmem : ∀ i ≤ 1, MemLp (iteratedFDeriv ℝ i u) 1 μ := fun i hi1 => by
    interval_cases i
    · exact (memLp_one_iff_integrable.2 hi).congr_norm
        (hu.continuous_iteratedFDeriv (by simp) |>.aestronglyMeasurable)
        (.of_forall fun x => norm_iteratedFDeriv_zero.symm)
    · have hdi : Integrable (fderiv ℝ u) μ := ⟨hdu, by
        rwa [HasFiniteIntegral, ← eLpNorm_one_eq_lintegral_enorm hdu, lt_top_iff_ne_top]⟩
      exact (memLp_one_iff_integrable.2 hdi).congr_norm
        (hu.continuous_iteratedFDeriv le_rfl |>.aestronglyMeasurable)
        (.of_forall fun x => (norm_iteratedFDeriv_one u).symm)
  have hlim (k : ℕ) (hk : k ≤ 1) := tendsto_eLpNorm_iteratedFDeriv_cutoff_sub (μ := μ)
    one_ne_zero ENNReal.one_ne_top (χ.contDiff (n := k)) χ.eventuallyEq_one
    (fun i _ x => hB i x) (hu.of_le (by exact_mod_cast hk))
    fun i hi => hmem i (hi.trans hk)
  -- The cutoffs converge to `u` in `L¹`, and the `L¹` norms of their derivatives are at most
  -- `‖Du‖₁ + ε n` with `ε n → 0`.
  have hval : Tendsto (fun n => eLpNorm (g n - u) 1 μ) atTop (𝓝 0) :=
    (hlim 0 zero_le_one).congr fun n => eLpNorm_congr_norm_ae
      (((hg n).continuous_iteratedFDeriv (by simp)).sub
        (hu.continuous_iteratedFDeriv (by simp))).aestronglyMeasurable
      ((hg n).continuous.sub hu.continuous).aestronglyMeasurable
      (.of_forall fun x => by
        simp only [g, iteratedFDeriv_zero_eq_comp, Pi.sub_apply, Function.comp_apply, ← map_sub,
          LinearIsometryEquiv.norm_map])
  set ε := fun n => eLpNorm (iteratedFDeriv ℝ 1 (g n) - iteratedFDeriv ℝ 1 u) 1 μ
  have hderiv (n : ℕ) : eLpNorm (fderiv ℝ (g n)) 1 μ ≤ eLpNorm (fderiv ℝ u) 1 μ + ε n := by
    rw [eLpNorm_congr_norm_ae ((hg n).continuous_fderiv one_ne_zero).aestronglyMeasurable
        ((hg n).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
        (.of_forall fun x => (norm_iteratedFDeriv_one _).symm),
      eLpNorm_congr_norm_ae hdu (hu.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
        (.of_forall fun x => (norm_iteratedFDeriv_one _).symm), add_comm]
    simpa using eLpNorm_add_le (μ := μ)
      (f := iteratedFDeriv ℝ 1 (g n) - iteratedFDeriv ℝ 1 u) (g := iteratedFDeriv ℝ 1 u) le_rfl
  have hbound : Tendsto (fun n => (C : ℝ≥0∞) * (eLpNorm (fderiv ℝ u) 1 μ + ε n)) atTop
      (𝓝 (C * eLpNorm (fderiv ℝ u) 1 μ)) := by
    simpa using ENNReal.Tendsto.const_mul (tendsto_const_nhds.add (hlim 1 le_rfl))
      (Or.inr ENNReal.coe_ne_top)
  -- Fatou's lemma along an almost everywhere convergent subsequence.
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hval).exists_seq_tendsto_ae
  refine (Lp.eLpNorm_lim_le_liminf_eLpNorm (fun n => (hg (ns n)).continuous.aestronglyMeasurable)
    u hi.aestronglyMeasurable hae).trans ?_
  refine (liminf_le_liminf (.of_forall fun n => ?_)).trans_eq
    (hbound.comp hns.tendsto_atTop).liminf_eq
  exact (eLpNorm_le_eLpNorm_fderiv_one μ (hg (ns n)) (hgc (ns n)) hp).trans
    (mul_le_mul_right (hderiv (ns n)) _)

end TauCeti
