/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Sets.Opens
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Normed.Module.OpenDiameter
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Closed-ball cutoff integral bounds for `Lᵖ` functions

Bounds `‖∫ y in Ω, g y ∂μ‖` on a bounded open set `Ω ⊆ E` against `f ∈ Lᵖ(Ω; F)` (`1 ≤ p ≤ ∞`) in
terms of `Metric.diam Ω` and the chunkiness parameter `γ` when `g` is supported in `closedBall x₀ ρ`
with `Metric.diam Ω ≤ γ * ρ` (`MeasureTheory.Lp.norm_setIntegral_le_of_support_subset_closedBall`),
feeding uniform Sobolev averaged-Taylor bounds.
-/

public section

namespace MeasureTheory.Lp

open Set TopologicalSpace
open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Closed-ball cutoff integral bound on `Lᵖ(Ω)`.** -/
theorem norm_setIntegral_le_of_support_subset_closedBall
    {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hΩ_bdd : Bornology.IsBounded (Ω : Set E)) (f : Lp F p (μ.restrict Ω))
    {g : E → G} {x₀ : E} {ρ K γ : ℝ} (hρ : 0 < ρ) (hdiam : Metric.diam (Ω : Set E) ≤ γ * ρ)
    (hsupp : Function.support g ⊆ Metric.closedBall x₀ ρ)
    (hg : ∀ᵐ y ∂μ.restrict (Ω : Set E), ‖g y‖ ≤ K * ρ ^ (-(Module.finrank ℝ E : ℝ)) * ‖f y‖) :
    ‖∫ y in Ω, g y ∂μ‖ ≤
      K * μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Ω : Set E) ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) * ‖f‖ := by
  let n := Module.finrank ℝ E
  rcases (Ω : Set E).eq_empty_or_nonempty with hΩ0 | hΩ_ne
  · have hf0 : ‖f‖ = 0 := by simp [Lp.norm_def, hΩ0]
    simp [hΩ0, hf0]
  rcases lt_or_ge K 0 with hK | hK
  · have hρn : 0 < ρ ^ (-(n : ℝ)) := Real.rpow_pos_of_pos hρ _
    have hf : ∀ᵐ y ∂μ.restrict (Ω : Set E), ‖f y‖ = 0 := hg.mono fun y hy => by
      nlinarith [mul_neg_of_neg_of_pos hK hρn, norm_nonneg (g y), norm_nonneg (f y)]
    have hf0 : ‖f‖ = 0 :=
      norm_eq_zero.2 <| Lp.eq_zero_iff_ae_eq_zero.2 (hf.mono fun _ hy => norm_eq_zero.1 hy)
    have hg0 : ∀ᵐ y ∂μ.restrict (Ω : Set E), g y = 0 :=
      hg.mp (hf.mono fun _ hy hgy => norm_le_zero_iff.1 (by rwa [hy, mul_zero] at hgy))
    simp [hf0, integral_eq_zero_of_ae hg0]
  let S := (Ω : Set E) ∩ Metric.closedBall x₀ ρ
  have hB_fin : μ (Metric.closedBall x₀ ρ) < ⊤ := (isCompact_closedBall x₀ ρ).measure_lt_top
  have : IsFiniteMeasure (μ.restrict S) :=
    isFiniteMeasure_restrict.2 ((measure_mono inter_subset_right).trans_lt hB_fin).ne
  have hfS : MemLp f p (μ.restrict S) :=
    (Lp.memLp f).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hgS : ∀ᵐ y ∂μ.restrict S, ‖g y‖ ≤ K * ρ ^ (-(n : ℝ)) * ‖hfS.toLp f y‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hg,
      hfS.coeFn_toLp] with _ hy hcoe; rwa [hcoe]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Ω.isOpen.measurableSet
    inter_subset_left fun y hy => Function.notMem_support.1 fun hgy => hy.2 ⟨hy.1, hsupp hgy⟩]
  have hnorm_le : ‖hfS.toLp f‖ ≤ ‖f‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_mono_measure f (Measure.restrict_mono inter_subset_left le_rfl))
  have hbase := (Lp.norm_integral_le_of_ae_norm_le_mul (hfS.toLp f) hgS).trans
    (mul_le_mul_of_nonneg_left hnorm_le (by positivity))
  have hexp : 0 ≤ 1 - 1 / p.toReal := ENNReal.one_sub_one_div_toReal_nonneg Fact.out
  have hmeas_le : ((μ.restrict S) Set.univ ^ (1 - 1 / p.toReal)).toReal ≤
      ρ ^ ((n : ℝ) * (1 - 1 / p.toReal)) * μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) := by
    rw [Measure.restrict_apply_univ, ← ENNReal.toReal_rpow, ← measureReal_def]
    refine (Real.rpow_le_rpow measureReal_nonneg ((measureReal_mono inter_subset_right
      hB_fin.ne).trans_eq (μ.addHaar_real_closedBall x₀ hρ.le)) hexp).trans_eq ?_
    rw [Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast ρ n,
      ← Real.rpow_mul hρ.le]
  have hadd : ρ ^ (-(n : ℝ)) * ρ ^ ((n : ℝ) * (1 - 1 / p.toReal)) =
      ρ ^ (-(n : ℝ) / p.toReal) := by rw [← Real.rpow_add hρ]; congr 1; ring
  have hrpow : ρ ^ (-(n : ℝ) / p.toReal) ≤
      γ ^ ((n : ℝ) / p.toReal) * Metric.diam (Ω : Set E) ^ (-(n : ℝ) / p.toReal) := by
    simpa only [div_eq_mul_inv] using
      Ω.isOpen.rpow_neg_finrank_mul_le hΩ_bdd hΩ_ne hρ hdiam (inv_nonneg.2 ENNReal.toReal_nonneg)
  calc ‖∫ y in S, g y ∂μ‖
      ≤ K * μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
          ρ ^ (-(n : ℝ) / p.toReal) * ‖f‖ :=
        (hbase.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmeas_le
          (by positivity)) (norm_nonneg f))).trans_eq
          (by linear_combination K * μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) * ‖f‖ *
            hadd)
    _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (a := K * μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal))
            hrpow (by positivity)) (norm_nonneg f)

end MeasureTheory.Lp
