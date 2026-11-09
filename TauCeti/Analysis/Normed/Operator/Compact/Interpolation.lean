/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# Compactness by interpolation

Let `T₀ : X → Y₀` be a compact operator and `T₁ : X → Y₁` a bounded one. A linear map
`T : X → Y` into a Banach space whose norm is controlled by an interpolation inequality

`‖T x‖ ≤ C ‖T₀ x‖ ^ (1 - θ) ‖T₁ x‖ ^ θ`, with `0 ≤ θ < 1`,

is compact as well. On a ball, `T₁` is bounded, so `T x` is small whenever `T₀ x` is; an `ε`-net
for the image of the ball under `T₀` therefore gives a net for its image under `T`.

The typical instance is the scale of `Lᵖ` spaces. An operator that is compact into `L^{p₀}` and
bounded into `L^{p₁}` is compact into every `Lᵖ` with `1 / p = (1 - θ) / p₀ + θ / p₁` and
`0 ≤ θ < 1`, by the logarithmic convexity of the `Lᵖ` norms
(`MeasureTheory.Lp.norm_le_norm_rpow_mul_norm_rpow_of_ae_eq`). On a finite measure space it is
also compact into every `Lᵖ` with `p ≤ p₀`, since `‖f‖_p ≤ μ(α) ^ (1/p - 1/p₀) ‖f‖_{p₀}`; this is
the case `θ = 0`, where the operator is dominated by a compact one. For Sobolev spaces these pass
Rellich–Kondrachov compactness from `Lᵖ` to every subcritical target exponent.

## Main declarations

* `IsCompactOperator.of_norm_le_mul_rpow_mul_rpow`: compactness by interpolation.
* `IsCompactOperator.of_forall_ae_eq_of_interpolation`: compactness into `L^{p₀}` and boundedness
  into `L^{p₁}` give compactness into the intermediate `Lᵖ`.
* `IsCompactOperator.of_forall_ae_eq_of_le`: on a finite measure space, compactness into `L^{p₀}`
  gives compactness into `Lᵖ` for `p ≤ p₀`.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., proof of Theorem 6.3.
-/

public section

open Filter Metric Set
open scoped Topology

namespace IsCompactOperator

variable {𝕜 X Y Y₀ Y₁ : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
  [SeminormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀]
  [SeminormedAddCommGroup Y₁] [NormedSpace 𝕜 Y₁]

/-- **Compactness by interpolation.** Let `T₀ : X → Y₀` be a compact operator and
`T₁ : X → Y₁` a bounded one, and let `0 ≤ θ < 1`. A linear map `T : X → Y` into a Banach space
with `‖T x‖ ≤ C ‖T₀ x‖ ^ (1 - θ) ‖T₁ x‖ ^ θ` for all `x` is compact. -/
theorem of_norm_le_mul_rpow_mul_rpow {T₀ : X →ₗ[𝕜] Y₀} (hT₀ : IsCompactOperator T₀)
    (T₁ : X →L[𝕜] Y₁) {T : X →ₗ[𝕜] Y} {C θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hT : ∀ x, ‖T x‖ ≤ C * ‖T₀ x‖ ^ (1 - θ) * ‖T₁ x‖ ^ θ) : IsCompactOperator T := by
  refine (isCompactOperator_iff_totallyBounded_image_closedBall _ zero_lt_one).mpr ?_
  rw [totallyBounded_iff]
  intro ε hε
  -- Differences of points of the closed unit ball have `T₁`-norm at most `M`.
  set M := ‖T₁‖ * 2
  have hlim : Tendsto (fun d : ℝ => |C| * d ^ (1 - θ) * M ^ θ) (𝓝 0) (𝓝 0) := by
    have hc : Continuous fun d : ℝ => |C| * d ^ (1 - θ) * M ^ θ :=
      (continuous_const.mul (Real.continuous_rpow_const (sub_nonneg.2 hθ₁.le))).mul
        continuous_const
    simpa [Real.zero_rpow (sub_pos.2 hθ₁).ne'] using hc.tendsto 0
  obtain ⟨δ, hδ, hδε⟩ := Metric.tendsto_nhds_nhds.1 hlim ε hε
  obtain ⟨t, hts, htf, hcover⟩ :=
    finite_approx_of_totallyBounded (hT₀.totallyBounded_image_closedBall 1) δ hδ
  have hpre : ∀ y ∈ t, ∃ x ∈ closedBall (0 : X) 1, T₀ x = y := fun y hy => hts hy
  choose! g hgB hgt using hpre
  refine ⟨(fun y => T (g y)) '' t, htf.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (hcover (mem_image_of_mem T₀ hx))
  refine mem_iUnion₂.2 ⟨T (g y), mem_image_of_mem _ hyt, ?_⟩
  rw [mem_ball, dist_eq_norm, ← map_sub]
  have h₀ : ‖T₀ (x - g y)‖ < δ := by
    rwa [map_sub, hgt y hyt, ← dist_eq_norm]
  have hxy : ‖x - g y‖ ≤ 2 := by
    rw [mem_closedBall_zero_iff] at hx
    have := mem_closedBall_zero_iff.1 (hgB y hyt)
    linarith [norm_sub_le x (g y)]
  have h₁ : ‖T₁ (x - g y)‖ ≤ M :=
    (T₁.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxy (norm_nonneg _))
  have hε' : |C| * ‖T₀ (x - g y)‖ ^ (1 - θ) * M ^ θ < ε := by
    have := hδε (x := ‖T₀ (x - g y)‖) (by rwa [dist_zero_right, norm_norm])
    rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
  calc ‖T (x - g y)‖ ≤ C * ‖T₀ (x - g y)‖ ^ (1 - θ) * ‖T₁ (x - g y)‖ ^ θ := hT _
    _ ≤ |C| * ‖T₀ (x - g y)‖ ^ (1 - θ) * M ^ θ :=
        mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
          (Real.rpow_le_rpow (norm_nonneg _) h₁ hθ₀) (by positivity) (by positivity)
    _ < ε := hε'

section Lp

open MeasureTheory
open scoped ENNReal

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E] {p₀ p₁ p : ℝ≥0∞} [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)]
  [Fact (1 ≤ p)]

/-- **Compactness by interpolation in the `Lᵖ` scale.** Let `S₀ : X → L^{p₀}` be a compact
operator and `T : X → L^{p₁}` a bounded one, and let `S : X → Lᵖ` represent the same functions,
where `1 / p = (1 - θ) / p₀ + θ / p₁` with `0 ≤ θ < 1`. Then `S` is compact. -/
theorem of_forall_ae_eq_of_interpolation {S₀ : X →L[𝕜] Lp E p₀ μ} (hS₀ : IsCompactOperator S₀)
    (T : X →L[𝕜] Lp E p₁ μ) {S : X →L[𝕜] Lp E p μ} {θ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (h₀ : ∀ x, (S x : α → E) =ᵐ[μ] S₀ x) (h₁ : ∀ x, (S x : α → E) =ᵐ[μ] T x) :
    IsCompactOperator S :=
  hS₀.of_norm_le_mul_rpow_mul_rpow (T₀ := S₀.toLinearMap) (T := S.toLinearMap) T (C := 1) hθ₀
    hθ₁ fun x => (Lp.norm_le_norm_rpow_mul_norm_rpow_of_ae_eq ⟨hθ₀, hθ₁.le⟩ hp (h₀ x)
      (h₁ x)).trans_eq (by simp only [ContinuousLinearMap.coe_coe, one_mul])

/-- **Compactness at lower exponents.** On a finite measure space, if `S₀ : X → L^{p₀}` is a
compact operator and `S : X → Lᵖ` represents the same functions, where `p ≤ p₀`, then `S` is
compact. -/
theorem of_forall_ae_eq_of_le [IsFiniteMeasure μ] {S₀ : X →L[𝕜] Lp E p₀ μ}
    (hS₀ : IsCompactOperator S₀) {S : X →L[𝕜] Lp E p μ} (hp : p ≤ p₀)
    (h : ∀ x, (S x : α → E) =ᵐ[μ] S₀ x) : IsCompactOperator S := by
  have hexp : 0 ≤ 1 / p.toReal - 1 / p₀.toReal := by
    rcases eq_or_ne p₀ ∞ with rfl | hp₀
    · simp only [ENNReal.toReal_top, div_zero, sub_zero]
      positivity
    · exact sub_nonneg.2 (one_div_le_one_div_of_le (ENNReal.toReal_pos
        (zero_lt_one.trans_le Fact.out).ne' (ne_top_of_le_ne_top hp₀ hp))
        (ENNReal.toReal_mono hp₀ hp))
  -- `‖S x‖_p ≤ μ(α) ^ (1/p - 1/p₀) ‖S₀ x‖_{p₀}`, an interpolation bound with `θ = 0`.
  refine hS₀.of_norm_le_mul_rpow_mul_rpow (T₀ := S₀.toLinearMap) (T := S.toLinearMap) S₀
    (C := (μ Set.univ ^ (1 / p.toReal - 1 / p₀.toReal)).toReal) le_rfl zero_lt_one fun x => ?_
  simp only [ContinuousLinearMap.coe_coe, sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
  calc ‖S x‖ = (eLpNorm (S₀ x) p μ).toReal := by rw [Lp.norm_def, eLpNorm_congr_ae (h x)]
    _ ≤ (eLpNorm (S₀ x) p₀ μ * μ Set.univ ^ (1 / p.toReal - 1 / p₀.toReal)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _)
          (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ _)))
          (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp (Lp.aestronglyMeasurable _))
    _ = _ := by rw [ENNReal.toReal_mul, Lp.norm_def, mul_comm]

end Lp

end IsCompactOperator
