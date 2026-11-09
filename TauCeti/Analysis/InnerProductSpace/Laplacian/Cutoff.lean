/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# Dilated cutoffs with Laplacian bounds

In a finite-dimensional real inner product space, dilating a fixed smooth bump by `R` gives cutoffs
`χ_R`, equal to `1` on `ball 0 R` and to `0` off `closedBall 0 (2R)`, with
`‖Dχ_R‖ = O(1/R)` and `|Δχ_R| = O(1/R²)` uniformly in `R`
(`TauCeti.exists_forall_contDiff_cutoff_ball_norm_laplacian_le`). These are the truncations used
to localize solutions of the Poisson equation: the error `Δ(χ_R u) - χ_R Δu` lives on the annulus
`R ≤ ‖x‖ ≤ 2R` and is controlled by the decay of `u` and `Du` there.

In dimension two the bound `|Δχ_R| = O(1/R²)` makes `∫ |Δχ_R|` bounded uniformly in `R`, so
`∫ Δχ_R f → 0` for every `f` tending to `0` at infinity
(`TauCeti.tendsto_integral_laplacian_smul_of_tendsto_cocompact`). This lets identities tested
against `χ_R` pass to `R → ∞`.
-/

public section

namespace TauCeti

open ContinuousLinearMap Filter Metric MeasureTheory Topology
open scoped ContDiff Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Dilated cutoffs with Laplacian bounds.** There is a constant `C` such that for every `R > 0`
some smooth compactly supported `χ` equals `1` near every point of `ball 0 R`, equals `0` near
every point outside `closedBall 0 (2R)`, and satisfies `0 ≤ χ ≤ 1`, `‖Dχ‖ ≤ C / R` and
`|Δχ| ≤ C / R²`. The cutoff is `x ↦ b (R⁻¹ • x)` for a fixed smooth bump `b` equal to `1` on
`closedBall 0 1` and supported in `closedBall 0 2`. -/
theorem exists_forall_contDiff_cutoff_ball_norm_laplacian_le :
    ∃ C : ℝ, ∀ R : ℝ, 0 < R → ∃ χ : E → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x, ‖x‖ < R → χ =ᶠ[𝓝 x] fun _ => 1) ∧
        (∀ x, 2 * R < ‖x‖ → χ =ᶠ[𝓝 x] fun _ => 0) ∧ (∀ x, ‖fderiv ℝ χ x‖ ≤ C / R) ∧
          (∀ x, ‖Δ χ x‖ ≤ C / R ^ 2) ∧ ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1 := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  have hb : ContDiff ℝ ∞ b := b.contDiff
  obtain ⟨C₁, hC₁⟩ := (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (b.hasCompactSupport.fderiv (𝕜 := ℝ))
  obtain ⟨C₂, hC₂⟩ := (continuousOn_univ.1 ((hb.of_le (by simp)).contDiffOn.continuousOn_laplacian
    isOpen_univ)).bounded_above_of_compact_support
      (b.hasCompactSupport.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset _)))
  refine ⟨max C₁ C₂, fun R hR => ⟨fun x => b (R⁻¹ • x), hb.comp (contDiff_id.const_smul R⁻¹),
    b.hasCompactSupport.comp_smul (inv_ne_zero hR.ne'), fun x hx => ?_, fun x hx => ?_,
    fun x => ?_, (fun x => ?_), fun _ => ⟨b.nonneg, b.le_one⟩⟩⟩
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hx)] with y hy
    refine b.one_of_mem_closedBall (mem_closedBall_zero_iff.2 ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_mul_le_iff₀ hR, mul_one]
    exact (mem_ball_zero_iff.1 hy).le
  · filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    refine b.zero_of_le_dist ?_
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR,
      le_inv_mul_iff₀ hR]
    have hy' : 2 * R < ‖y‖ := hy
    linarith
  · have h : HasFDerivAt (fun x => b (R⁻¹ • x)) _ x :=
      ((hb.differentiable (by simp)) (R⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul R⁻¹)
    rw [h.fderiv]
    refine (opNorm_comp_le _ _).trans ?_
    rw [div_eq_mul_inv]
    refine mul_le_mul ((hC₁ _).trans (le_max_left _ _)) ?_ (norm_nonneg _)
      ((norm_nonneg _).trans ((hC₁ 0).trans (le_max_left _ _)))
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_inv, abs_of_pos hR]
    exact mul_le_of_le_one_right (inv_nonneg.2 hR.le) (norm_id_le)
  · rw [laplacian_comp_smul_right, norm_smul, Real.norm_eq_abs, div_eq_mul_inv, ← inv_pow,
      abs_pow, abs_inv, abs_of_pos hR, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC₂ _).trans (le_max_right _ _)) (by positivity)

section Limits

open InnerProductSpace

variable [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type*} {l : Filter ι} {χ : ι → E → ℝ} {R : ι → ℝ}

/-- **Laplacians of planar cutoffs against decaying functions.** In a two-dimensional space, let
the cutoffs `χ i` equal `1` near `ball 0 (R i)` and `0` near the complement of
`closedBall 0 (2 * R i)`, with `|Δ χ i| ≤ C / (R i)²` and `R i → ∞`. Then `∫ Δ χ i • f → 0` for
every `f` tending to `0` at infinity, since `∫ |Δ χ i|` is bounded uniformly in `i`. -/
theorem tendsto_integral_laplacian_smul_of_tendsto_cocompact (μ : Measure E)
    [μ.IsAddHaarMeasure] (hE : Module.finrank ℝ E = 2) {C : ℝ} (hR : Tendsto R l atTop)
    (hχ1 : ∀ i x, ‖x‖ < R i → χ i =ᶠ[𝓝 x] fun _ => 1)
    (hχ0 : ∀ i x, 2 * R i < ‖x‖ → χ i =ᶠ[𝓝 x] fun _ => 0)
    (hχΔ : ∀ i x, ‖Δ (χ i) x‖ ≤ C / R i ^ 2) {f : E → F}
    (hf : Tendsto f (cocompact E) (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, Δ (χ i) x • f x ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set C' := max C 0
  set V := μ.real (closedBall (0 : E) 1)
  have hV : 0 ≤ V := measureReal_nonneg
  set ε' := ε / (4 * V * C' + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨R', -, hR'⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ Metric.tendsto_nhds.mp hf ε' hε'pos)
  filter_upwards [hR.eventually_gt_atTop (max R' 0)] with i hi
  have hRi : 0 < R i := (le_max_right _ _).trans_lt hi
  -- `Δ χ i • f` is supported in `closedBall 0 (2 * R i)`, where it is at most `C' / R i ^ 2 * ε'`.
  set g : E → ℝ := (closedBall (0 : E) (2 * R i)).indicator fun _ ↦ C' / R i ^ 2 * ε'
  have hg : Integrable g μ :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hbound : ∀ x, ‖Δ (χ i) x • f x‖ ≤ g x := by
    intro x
    have hg₀ : 0 ≤ g x := Set.indicator_nonneg (fun _ _ ↦ by positivity) x
    by_cases h₁ : ‖x‖ < R i
    · rw [(laplacian_congr_nhds (hχ1 i x h₁)).eq_of_nhds, laplacian_const]
      simpa using hg₀
    by_cases h₂ : 2 * R i < ‖x‖
    · rw [(laplacian_congr_nhds (hχ0 i x h₂)).eq_of_nhds, laplacian_const]
      simpa using hg₀
    have hx : x ∈ closedBall (0 : E) (2 * R i) := mem_closedBall_zero_iff.mpr (not_lt.mp h₂)
    have hfx : ‖f x‖ ≤ ε' := by
      simpa using (hR' (((le_max_left _ _).trans_lt hi).le.trans (not_lt.mp h₁))).le
    have hgx : g x = C' / R i ^ 2 * ε' := Set.indicator_of_mem hx _
    rw [hgx, norm_smul]
    exact mul_le_mul ((hχΔ i x).trans (div_le_div_of_nonneg_right (le_max_left _ _)
      (by positivity))) hfx (norm_nonneg _) (by positivity)
  have hgint : ∫ x, g x ∂μ = 4 * V * C' * ε' := by
    rw [integral_indicator_const _ measurableSet_closedBall,
      Measure.addHaar_real_closedBall' μ _ (by positivity), hE, smul_eq_mul]
    field_simp
    ring
  rw [dist_zero_right]
  calc ‖∫ x, Δ (χ i) x • f x ∂μ‖ ≤ ∫ x, g x ∂μ :=
        norm_integral_le_of_norm_le hg (.of_forall hbound)
    _ = 4 * V * C' * ε' := hgint
    _ < ε := by
      rw [hε', mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hV) (le_max_right C 0)]

end Limits

end TauCeti
