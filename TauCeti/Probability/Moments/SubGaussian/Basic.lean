/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Basic properties of sub-Gaussian moment-generating functions

The quadratic MGF bound forces a sub-Gaussian random variable to have mean zero, and is monotone in
the variance proxy. A family with a common almost everywhere envelope and a common centered
sub-Gaussian bound has uniformly bounded means, even when the envelope is not measurable.
-/

public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace ProbabilityTheory.HasSubgaussianMGF

/-- Monotonicity of `HasSubgaussianMGF` in the variance proxy. -/
theorem mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c₁ c₂ : ℝ≥0}
    (h : HasSubgaussianMGF X c₁ μ) (hle : c₁ ≤ c₂) : HasSubgaussianMGF X c₂ μ :=
  ⟨h.integrable_exp_mul, fun t ↦ (h.mgf_le t).trans <| by gcongr⟩

/-- Under a zero or probability measure, a sub-Gaussian MGF bound forces the expectation to
vanish. -/
theorem integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) : μ[X] = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · simp
  have hset := hX.integrableExpSet_eq_univ
  have hm : 0 ∈ interior (integrableExpSet X μ) := by simp [hset]
  let g : ℝ → ℝ := (fun t ↦ Real.exp ((c : ℝ) * t ^ 2 / 2)) - mgf X μ
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [g, Pi.sub_apply] using sub_nonneg.mpr (hX.mgf_le t)
  have hd : HasDerivAt g (-μ[X]) 0 := by
    have he : HasDerivAt (fun t : ℝ ↦ Real.exp ((c : ℝ) * t ^ 2 / 2)) 0 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (c : ℝ)).div_const 2 |>.exp
        using 1 <;> simp
    have hx : HasDerivAt (mgf X μ) μ[X] 0 := by
      simpa using hasDerivAt_mgf hm
    simpa only [g, zero_sub] using he.sub hx
  exact neg_eq_zero.mp (hmin.hasDerivAt_eq_zero hd)

end ProbabilityTheory.HasSubgaussianMGF

namespace TauCeti.Probability

/-- A family bounded in absolute value almost everywhere by a common real function, and uniformly
sub-Gaussian about its means, has uniformly bounded means. No measurability or integrability of
the envelope is required. -/
theorem exists_forall_abs_integral_le_of_hasSubgaussianMGF {ι Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    {g : ι → Ω → ℝ} {c : ℝ≥0} (hgf : ∀ n, ∀ᵐ x ∂μ, |g n x| ≤ f x)
    (hsub : ∀ n, HasSubgaussianMGF (fun x ↦ g n x - ∫ y, g n y ∂μ) c μ) :
    ∃ B, ∀ n, |∫ y, g n y ∂μ| ≤ B := by
  -- Some sublevel set of the envelope has positive outer measure.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, μ {x | f x ≤ N} ≠ 0 := by
    by_contra! H
    have hU : (⋃ N : ℕ, {x | f x ≤ N}) = Set.univ :=
      Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 (exists_nat_ge (f x))
    simpa [hU] using measure_iUnion_null_iff.2 H
  have hp : 0 < μ.real {x | f x ≤ N} := ENNReal.toReal_pos hN (measure_ne_top _ _)
  refine ⟨N + 2 * exp (c / 2) / μ.real {x | f x ≤ N}, fun n ↦ ?_⟩
  set m := ∫ y, g n y ∂μ
  have hX := hsub n
  -- The first absolute moment about the mean is at most `2 exp (c / 2)`.
  have habs : ∫ x, |g n x - m| ∂μ ≤ 2 * exp (c / 2) := by
    calc ∫ x, |g n x - m| ∂μ
        ≤ ∫ x, (exp (1 * (g n x - m)) + exp ((-1) * (g n x - m))) ∂μ :=
          integral_mono hX.integrable.abs
            ((hX.integrable_exp_mul 1).add (hX.integrable_exp_mul (-1))) fun x ↦ by
              simp only [one_mul, neg_one_mul]
              linarith [add_one_le_exp |g n x - m|, exp_abs_le (g n x - m)]
      _ = mgf (fun x ↦ g n x - m) μ 1 + mgf (fun x ↦ g n x - m) μ (-1) :=
          integral_add (hX.integrable_exp_mul 1) (hX.integrable_exp_mul (-1))
      _ ≤ exp (c * 1 ^ 2 / 2) + exp (c * (-1) ^ 2 / 2) := add_le_add (hX.mgf_le 1) (hX.mgf_le (-1))
      _ = 2 * exp (c / 2) := by norm_num; ring
  by_cases hm : |m| ≤ N
  · exact hm.trans (le_add_of_nonneg_right (by positivity))
  -- Markov's inequality applies without measurability of the envelope's sublevel set.
  have hle : μ.real {x | f x ≤ N} ≤ μ.real {x | |m| - N ≤ |g n x - m|} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hgf n] with x hx hxf
    have : f x ≤ N := hxf
    linarith [abs_sub_abs_le_abs_sub m (g n x), abs_sub_comm m (g n x)]
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (.of_forall fun x ↦ abs_nonneg (g n x - m)) hX.integrable.abs (|m| - N)
  have : |m| - N ≤ 2 * exp (c / 2) / μ.real {x | f x ≤ N} := by
    rw [le_div_iff₀ hp]
    exact (mul_le_mul_of_nonneg_left hle (by linarith)).trans (hmarkov.trans habs)
  linarith

end TauCeti.Probability
