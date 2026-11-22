/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.SubExponential
public import TauCeti.Probability.Moments.SubGaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Probability.Moments.SubGaussian

/-!
# Sub-Gaussian and sub-exponential moment bounds

A centered sub-Gaussian variable with variance proxy `c` is sub-exponential with any positive
parameter `K` such that `c / 2 ≤ K ^ 2`. In particular the standard Gaussian is sub-exponential
with parameter `1`. Products of two sub-Gaussian variables with proxy `c > 0`
are sub-exponential with parameter `40 * c`, including when the factors are dependent.

## Main results

* `ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF` compares the two MGF conventions.
* `hasSubexponentialMGF_fun_id_gaussianReal` treats Gaussian laws of any mean and variance.
* `ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_mul` controls products.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), Lemma 2.7.7 and Exercise 2.7.10.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory.HasSubgaussianMGF

/-- A sub-Gaussian bound on the centered variable implies a sub-exponential bound. -/
theorem hasSubexponentialMGF_of_centered {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} {K : ℝ}
    (hcenter : HasSubgaussianMGF (fun ω ↦ X ω - μ[X]) c μ)
    (hK : 0 < K) (hc : (c : ℝ) / 2 ≤ K ^ 2) :
    TauCeti.Probability.HasSubexponentialMGF X K μ := by
  have hX : Integrable X μ := by
    convert hcenter.integrable.add (integrable_const μ[X]) using 1
    funext ω
    simp
  refine ⟨hK, hX, ?_, ?_⟩
  · intro t _
    exact hcenter.integrable_exp_mul t
  · intro t _
    have hbound : (c : ℝ) * t ^ 2 / 2 ≤ K ^ 2 * t ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg t)]
    exact (hcenter.mgf_le t).trans (Real.exp_le_exp.mpr hbound)

/-- A sub-Gaussian variable is sub-exponential when the quadratic MGF constants
are compatible. -/
theorem hasSubexponentialMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} {K : ℝ}
    (hX : HasSubgaussianMGF X c μ)
    (hK : 0 < K) (hc : (c : ℝ) / 2 ≤ K ^ 2) :
    TauCeti.Probability.HasSubexponentialMGF X K μ := by
  apply hasSubexponentialMGF_of_centered _ hK hc
  simpa only [hX.integral_eq_zero, sub_zero] using hX

private theorem mgf_sq_sub_sq_centered_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {X Y : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) (hY : HasSubgaussianMGF Y c μ)
    {t : ℝ} (ht : (c : ℝ) * |2 * t| ≤ 1 / 8) :
    let Z := fun ω ↦ X ω ^ 2 - Y ω ^ 2
    Integrable (fun ω ↦ exp (t * (Z ω - μ[Z]))) μ ∧
      mgf (fun ω ↦ Z ω - μ[Z]) μ t ≤ exp (1536 * c ^ 2 * t ^ 2) := by
  intro Z
  have hX₂ := (hX.memLp 2).integrable_sq
  have hY₂ := (hY.memLp 2).integrable_sq
  have hmean : μ[Z] = μ[fun ω ↦ X ω ^ 2] - μ[fun ω ↦ Y ω ^ 2] :=
    integral_sub hX₂ hY₂
  obtain ⟨hXi, hXm⟩ := hX.mgf_sq_sub_integral_le ht
  obtain ⟨hYi, hYm⟩ := hY.mgf_sq_sub_integral_le (by rwa [abs_neg] : (c : ℝ) * |-(2 * t)| ≤ _)
  let Yc : Ω → ℝ := fun ω ↦ Y ω ^ 2 - μ[fun z ↦ Y z ^ 2]
  have hYneg : Integrable (fun ω ↦ exp (2 * t * (-Yc) ω)) μ := by
    simpa only [Yc, Pi.neg_apply, mul_neg, neg_mul] using hYi
  have hYmgf : mgf (-Yc) μ (2 * t) ≤ exp (384 * (c : ℝ) ^ 2 * (2 * t) ^ 2) := by
    simpa only [Yc, mgf_neg, even_two.neg_pow] using hYm
  have hcenter (ω : Ω) : Z ω - μ[Z] =
      (X ω ^ 2 - μ[fun z ↦ X z ^ 2]) + (-Yc) ω := by
    rw [hmean]
    simp only [Z, Yc, Pi.neg_apply]
    ring
  simp only [hcenter]
  obtain ⟨hint, hle⟩ := TauCeti.mgf_add_le_of_mgf_two_mul_le hXi hYneg hXm hYmgf
  exact ⟨hint, hle.trans_eq (by rw [add_self_div_two]; congr 1; ring)⟩

/-- The product of two random variables with common positive sub-Gaussian proxy `c` is
sub-exponential with parameter `40 * c`. The factors may be dependent. -/
theorem hasSubexponentialMGF_mul {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {U V : Ω → ℝ} {c : ℝ≥0}
    (hU : HasSubgaussianMGF U c μ) (hV : HasSubgaussianMGF V c μ) (hc : 0 < c) :
    TauCeti.Probability.HasSubexponentialMGF (fun ω ↦ U ω * V ω) (40 * c) μ := by
  let X : Ω → ℝ := fun ω ↦ (1 / 2) * (U ω + V ω)
  let Y : Ω → ℝ := fun ω ↦ (1 / 2) * (U ω - V ω)
  have hproxy : NNReal.mk ((1 / 2 : ℝ) ^ 2) (by positivity) *
      ((c.sqrt + c.sqrt) ^ 2) = c := by
    rw [← two_mul, mul_pow, NNReal.sq_sqrt, ← mul_assoc]
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    norm_num
  have hX : HasSubgaussianMGF X c μ := by
    convert (hU.add hV).const_mul (1 / 2) using 1
    exact hproxy.symm
  have hY : HasSubgaussianMGF Y c μ := by
    convert (hU.add hV.neg).const_mul (1 / 2) using 1
    exact hproxy.symm
  have hpolar : (fun ω ↦ U ω * V ω) = fun ω ↦ X ω ^ 2 - Y ω ^ 2 := by
    ext ω
    dsimp [X, Y]
    ring
  have hmul : Integrable (fun ω ↦ U ω * V ω) μ :=
    (hU.memLp 2).integrable_mul (hV.memLp 2) (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
  have hbound (t : ℝ) (ht : |t| ≤ (40 * (c : ℝ))⁻¹) :
      Integrable (fun ω ↦ exp (t * (U ω * V ω - μ[fun a ↦ U a * V a]))) μ ∧
      mgf (fun ω ↦ U ω * V ω - μ[fun a ↦ U a * V a]) μ t ≤ exp ((40 * c) ^ 2 * t ^ 2) := by
    have hc' : 0 < (c : ℝ) := NNReal.coe_pos.mpr hc
    have hsmall : (c : ℝ) * |2 * t| ≤ 1 / 8 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [← one_div] at ht
      have ht' := (le_div_iff₀ (by positivity : 0 < 40 * (c : ℝ))).mp ht
      linarith
    obtain ⟨hint, hmgf⟩ := mgf_sq_sub_sq_centered_le hX hY hsmall
    have hrate : 1536 * (c : ℝ) ^ 2 * t ^ 2 ≤ (40 * c) ^ 2 * t ^ 2 := by
      nlinarith [sq_nonneg ((c : ℝ) * t)]
    simp only [congrFun hpolar]
    exact ⟨hint, hmgf.trans (exp_le_exp.mpr hrate)⟩
  exact ⟨by positivity, hmul, fun t ht ↦ (hbound t ht).1, fun t ht ↦ (hbound t ht).2⟩

end ProbabilityTheory.HasSubgaussianMGF

namespace TauCeti.Probability

/-- A Gaussian satisfies the sub-exponential MGF bound for compatible parameters. -/
theorem hasSubexponentialMGF_fun_id_gaussianReal {m : ℝ} {v : ℝ≥0} {K : ℝ}
    (hK : 0 < K) (hv : (v : ℝ) / 2 ≤ K ^ 2) :
    HasSubexponentialMGF (fun x : ℝ ↦ x) K (gaussianReal m v) := by
  have hX : HasSubgaussianMGF (fun x : ℝ ↦ x) v (gaussianReal 0 v) := by
    refine ⟨integrable_exp_mul_gaussianReal, ?_⟩
    intro t
    simp [mgf_fun_id_gaussianReal]
  have hcenter : HasSubgaussianMGF (fun x : ℝ ↦ x - m) v (gaussianReal m v) := by
    have hmap : HasSubgaussianMGF (fun x : ℝ ↦ x) v
        ((gaussianReal m v).map (fun x ↦ x - m)) := by
      simpa [gaussianReal_map_sub_const] using hX
    have h := HasSubgaussianMGF.of_map (μ := gaussianReal m v)
      (Y := fun x : ℝ ↦ x - m) (by fun_prop) hmap
    convert h using 1
    funext x
    rfl
  apply ProbabilityTheory.HasSubgaussianMGF.hasSubexponentialMGF_of_centered _ hK hv
  simpa [integral_id_gaussianReal] using hcenter

end TauCeti.Probability
