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
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Closed-ball cutoff integral bounds for `Lᵖ` functions

Let `Ω` be a bounded open subset of a finite-dimensional real normed space `E` equipped with an
additive Haar measure `μ`, and let `f ∈ Lᵖ(Ω; F)` (`1 ≤ p ≤ ∞`). If `g : E → G` is supported in
`Metric.closedBall x₀ ρ` with `Metric.diam Ω ≤ γ * ρ` (`0 < ρ`) and satisfies the scaled pointwise
bound `‖g y‖ ≤ K * ρ ^ (-finrank ℝ E) * ‖f y‖` almost everywhere on `Ω`, Hölder's inequality on
`Ω ∩ closedBall x₀ ρ` combined with additive Haar scaling bounds `‖∫ y in Ω, g y ∂μ‖` explicitly in
terms of `Metric.diam Ω` and the chunkiness ratio `γ`
(`MeasureTheory.Lp.norm_setIntegral_le_of_support_subset_closedBall`).
-/

public section

namespace MeasureTheory.Lp

open Set TopologicalSpace
open scoped ENNReal

section ClosedBall

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {Ω : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [Fact (1 ≤ p)] in
private theorem rpow_neg_finrank_div_le (hΩ_bdd : Bornology.IsBounded (Ω : Set E))
    (hΩ_ne : (Ω : Set E).Nonempty) {ρ γ : ℝ} (hρ : 0 < ρ)
    (hdiam : Metric.diam (Ω : Set E) ≤ γ * ρ) :
    ρ ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) ≤
      γ ^ ((Module.finrank ℝ E : ℝ) / p.toReal) *
        Metric.diam (Ω : Set E) ^ (-(Module.finrank ℝ E : ℝ) / p.toReal) := by
  let n := Module.finrank ℝ E
  let d := Metric.diam (Ω : Set E)
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · simp [n, hn0]
  have := Module.nontrivial_of_finrank_pos hn_pos
  obtain ⟨y₀, hy₀⟩ := hΩ_ne
  have hd_pos : 0 < d := Ω.isOpen.diam_pos hΩ_bdd hy₀
  have hγ_pos : 0 < γ := pos_of_mul_pos_left (hd_pos.trans_le hdiam) hρ.le
  have hinv : ρ⁻¹ ≤ γ / d := by
    rw [inv_le_iff_one_le_mul₀ hρ, div_mul_eq_mul_div, le_div_iff₀ hd_pos, one_mul]
    exact hdiam
  calc ρ ^ (-(n : ℝ) / p.toReal)
      = (ρ⁻¹) ^ ((n : ℝ) / p.toReal) := by
        rw [Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le, neg_div]
    _ ≤ (γ / d) ^ ((n : ℝ) / p.toReal) :=
        Real.rpow_le_rpow (by positivity) hinv (by positivity)
    _ = γ ^ ((n : ℝ) / p.toReal) * d ^ (-(n : ℝ) / p.toReal) := by
        rw [div_eq_mul_inv, Real.mul_rpow hγ_pos.le (by positivity), Real.inv_rpow hd_pos.le,
          ← Real.rpow_neg hd_pos.le, neg_div]

/-- **Closed-ball cutoff integral bound on `Lᵖ(Ω)`.** For a bounded open set `Ω ⊆ E` with
`Metric.diam Ω ≤ γ * ρ` (`0 < ρ`), `1 ≤ p ≤ ∞`, and `g` supported in `Metric.closedBall x₀ ρ`
satisfying `‖g y‖ ≤ K * ρ ^ (-finrank ℝ E) * ‖f y‖` almost everywhere on `Ω`, the set integral
`∫ y in Ω, g y ∂μ` is bounded in norm by
`K * μ.real (ball 0 1) ^ (1 - 1/p) * γ ^ (n/p) * (diam Ω) ^ (-n/p) * ‖f‖`. -/
theorem norm_setIntegral_le_of_support_subset_closedBall
    {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hΩ_bdd : Bornology.IsBounded (Ω : Set E)) (f : Lp F p (μ.restrict Ω))
    {g : E → G} {x₀ : E} {ρ K γ : ℝ} (hρ : 0 < ρ)
    (hdiam : Metric.diam (Ω : Set E) ≤ γ * ρ)
    (hsupp : Function.support g ⊆ Metric.closedBall x₀ ρ)
    (hg : ∀ᵐ y ∂μ.restrict (Ω : Set E),
      ‖g y‖ ≤ K * ρ ^ (-(Module.finrank ℝ E : ℝ)) * ‖f y‖) :
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
      have := mul_neg_of_neg_of_pos hK hρn
      nlinarith [norm_nonneg (g y), norm_nonneg (f y)]
    have hf0 : ‖f‖ = 0 := by
      rw [norm_eq_zero, Lp.eq_zero_iff_ae_eq_zero]
      exact hf.mono fun y hy => norm_eq_zero.1 hy
    have hg0 : ∀ᵐ y ∂μ.restrict (Ω : Set E), g y = 0 := hg.mp (hf.mono fun y hy hgy => by
      rw [hy, mul_zero] at hgy
      exact norm_le_zero_iff.1 hgy)
    simp [hf0, integral_eq_zero_of_ae hg0]
  let S := (Ω : Set E) ∩ Metric.closedBall x₀ ρ
  have hB_fin : μ (Metric.closedBall x₀ ρ) < ⊤ := (isCompact_closedBall x₀ ρ).measure_lt_top
  have hS_fin : μ S < ⊤ := (measure_mono inter_subset_right).trans_lt hB_fin
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hS_fin.ne
  have hfS : MemLp f p (μ.restrict S) :=
    (Lp.memLp f).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hgS : ∀ᵐ y ∂μ.restrict S, ‖g y‖ ≤ K * ρ ^ (-(n : ℝ)) * ‖hfS.toLp f y‖ := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hg,
      hfS.coeFn_toLp] with y hy hcoe
    rwa [hcoe]
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
      ρ ^ ((n : ℝ) * (1 - 1 / p.toReal)) *
        μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) := by
    rw [Measure.restrict_apply_univ, ← ENNReal.toReal_rpow, ← measureReal_def]
    refine (Real.rpow_le_rpow measureReal_nonneg
      ((measureReal_mono inter_subset_right hB_fin.ne).trans_eq
        (μ.addHaar_real_closedBall x₀ hρ.le)) hexp).trans_eq ?_
    rw [Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast ρ n,
      ← Real.rpow_mul hρ.le]
  have hadd : ρ ^ (-(n : ℝ)) * ρ ^ ((n : ℝ) * (1 - 1 / p.toReal)) =
      ρ ^ (-(n : ℝ) / p.toReal) := by rw [← Real.rpow_add hρ]; congr 1; ring
  have hstep1 : ‖∫ y in S, g y ∂μ‖ ≤ K * μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
      ρ ^ (-(n : ℝ) / p.toReal) * ‖f‖ :=
    (hbase.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmeas_le (by positivity)) (norm_nonneg f))).trans_eq
      (by linear_combination K * μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal) * ‖f‖ * hadd)
  refine hstep1.trans ?_
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (a := K * μ.real (Metric.ball (0 : E) 1) ^ (1 - 1 / p.toReal))
      (rpow_neg_finrank_div_le hΩ_bdd hΩ_ne hρ hdiam) (by positivity))
    (norm_nonneg f)

end ClosedBall

-- For `p = 1` on `(-1, 1) ⊆ ℝ` with `ρ = 1` and `γ = 2` (`diam (-1, 1) = 2`), the unit-ball
-- factor has exponent `0` and `2 ^ 1 * 2 ^ (-1) = 1`, giving `‖∫_{(-1,1)} g‖ ≤ K * ‖f‖`.
example {μ : Measure ℝ} [μ.IsAddHaarMeasure]
    (f : Lp ℝ 1 (μ.restrict (Set.Ioo (-1 : ℝ) 1))) {g : ℝ → ℝ} {K : ℝ}
    (hsupp : Function.support g ⊆ Metric.closedBall (0 : ℝ) 1)
    (hg : ∀ᵐ y ∂μ.restrict (Set.Ioo (-1 : ℝ) 1), ‖g y‖ ≤ K * ‖f y‖) :
    ‖∫ y in Set.Ioo (-1 : ℝ) 1, g y ∂μ‖ ≤ K * ‖f‖ := by
  let I : Opens ℝ := ⟨Set.Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
  have hdiam : Metric.diam (Set.Ioo (-1 : ℝ) 1) = 2 := by
    rw [Real.diam_Ioo (by norm_num)]; norm_num
  refine (norm_setIntegral_le_of_support_subset_closedBall (Ω := I)
    (Metric.isBounded_Ioo (-1) 1) f zero_lt_one (γ := 2) (K := K) (by simpa [I] using hdiam.le)
    hsupp (by simpa [I] using hg)).trans_eq ?_
  have htwo : (2 : ℝ) * ((2 : ℝ) ^ (-1 : ℝ) * ‖f‖) = ‖f‖ := by
    rw [← mul_assoc]; norm_num
  simpa [I, hdiam, mul_assoc] using congrArg (K * ·) htwo

end MeasureTheory.Lp
