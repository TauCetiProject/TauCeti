/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.Topology.MetricSpace.Lipschitz.Extension
import TauCeti.Analysis.Convolution.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Smooth approximation retaining Lipschitz constants

Lipschitz functions on finite-dimensional real normed spaces admit uniform smooth
approximations with the same Lipschitz constant, including for Banach-valued functions.
For real data given only on a subset and valued in a fixed closed interval, the approximant
is defined on the entire space and stays in that interval. Thus both the derivative bound
and boundedness survive the local extension and smoothing used in manifold approximation.
For finite-dimensional values, data which are Lipschitz only on a neighbourhood of a compact set
have smooth approximations, uniformly close on the compact set, whose derivatives are bounded at
its points by the same Lipschitz constant.

The construction combines Mathlib's McShane extension and normalized smooth bumps with
`LipschitzWith.normed_convolution`. Derivative bounds follow directly from Mathlib's
`norm_fderiv_le_of_lipschitz`.

## References

* D. Azagra, J. Ferrera, F. López-Mesas and Y. Rangel,
  *Smooth approximation of Lipschitz functions on Riemannian manifolds*,
  J. Math. Anal. Appl. 326 (2007), 1370–1378, Section 2.
-/

public section

open ContinuousLinearMap MeasureTheory Metric Set
open scoped Convolution ContDiff NNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {K : ℝ≥0} {f : E → F}

/-- A Lipschitz function has smooth uniform approximations with exactly the same Lipschitz
bound. The domain may have dimension zero, and the function need not be bounded. -/
theorem LipschitzWith.exists_contDiff_lipschitzWith_dist_lt (hf : LipschitzWith K f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ LipschitzWith K g ∧ ∀ x, dist (g x) (f x) < ε := by
  borelize E
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_mul_lt hε (K : ℝ)
  let ρ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  refine ⟨ρ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] f, ?_,
    hf.normed_convolution ρ, fun x => ?_⟩
  · exact ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed
      hf.continuous.locallyIntegrable
  · refine (ρ.dist_normed_convolution_le hf.continuous.aestronglyMeasurable
      fun y hy => (hf.dist_le_mul y x).trans ?_).trans_lt hbound
    exact mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg

/-- Bounded real Lipschitz data on any subset have globally defined smooth approximations
with the same Lipschitz bound and the same closed interval of values.

No openness, closedness or nonemptiness is required of the subset. -/
theorem LipschitzOnWith.exists_contDiff_lipschitzWith_mem_Icc_dist_lt {f : E → ℝ} {s : Set E}
    (hf : LipschitzOnWith K f s) {a b : ℝ} (hab : a ≤ b)
    (hmem : ∀ x ∈ s, f x ∈ Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LipschitzWith K g ∧
      (∀ x, g x ∈ Icc a b) ∧ ∀ x ∈ s, dist (g x) (f x) < ε := by
  obtain ⟨u, hu, heq, hub⟩ := hf.extend_real_mem_Icc hab hmem
  borelize E
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_mul_lt hε (K : ℝ)
  let ρ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let g := ρ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] u
  have hi : ConvolutionExists (ρ.normed Measure.addHaar) u (lsmul ℝ ℝ) Measure.addHaar :=
    ρ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) ρ.integrable_normed.locallyIntegrable hu.continuous
  refine ⟨g, ?_, hu.normed_convolution ρ, ?_, ?_⟩
  · exact ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed
      hu.continuous.locallyIntegrable
  · intro x
    exact ⟨le_convolution_lsmul_of_forall_le ρ.support_normed_eq.subset
        ρ.nonneg_normed ρ.integral_normed (hi x) (fun y _ => (hub y).1),
      convolution_lsmul_le_of_forall_le ρ.support_normed_eq.subset
        ρ.nonneg_normed ρ.integral_normed (hi x) (fun y _ => (hub y).2)⟩
  · intro x hx
    rw [heq hx]
    refine (ρ.dist_normed_convolution_le hu.continuous.aestronglyMeasurable
      fun y hy => (hu.dist_le_mul y x).trans ?_).trans_lt hbound
    exact mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg

/-- Data with values in a finite-dimensional space which are `K`-Lipschitz on a neighbourhood `U`
of a compact set `s` have smooth approximations, uniformly close on `s`, whose derivatives are
bounded by `K` at every point of `s`. Outside `U` the data are arbitrary. -/
theorem LipschitzOnWith.exists_contDiff_dist_lt_norm_fderiv_le [FiniteDimensional ℝ F]
    {s U : Set E} (hf : LipschitzOnWith K f U) (hs : IsCompact s) (hU : U ∈ 𝓝ˢ s) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ (∀ x ∈ s, dist (g x) (f x) < ε) ∧
      ∀ x ∈ s, ‖fderiv ℝ g x‖ ≤ K := by
  -- Extend `f` from `U` to a Lipschitz map `G` on `E`, with a worse constant `K'`.
  obtain ⟨G, hG, hGf⟩ := hf.extend_finite_dimension
  set K' := lipschitzExtensionConstant F * K
  obtain ⟨δ, hδ, hδU⟩ := hs.exists_thickening_subset_open isOpen_interior
    (subset_interior_iff_mem_nhdsSet.2 hU)
  -- Mollify `G` at a scale `r` small for both `δ` and `ε`.
  set r := min (δ / 2) (ε / (2 * (K' + 1)))
  have hr : 0 < r := lt_min (half_pos hδ) (by positivity)
  have hrK : (K' : ℝ) * r < ε := by
    calc (K' : ℝ) * r ≤ K' * (ε / (2 * (K' + 1))) := by gcongr; exact min_le_right _ _
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [K'.coe_nonneg]
  borelize E
  let ρ : ContDiffBump (0 : E) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨ρ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] G, ?_, fun x hx => ?_,
    fun x hx => ?_⟩
  · exact ρ.hasCompactSupport_normed.contDiff_convolution_left _ ρ.contDiff_normed
      hG.continuous.locallyIntegrable
  · rw [hGf (interior_subset (hδU (self_subset_thickening hδ s hx)))]
    refine (ρ.dist_normed_convolution_le hG.continuous.aestronglyMeasurable
      fun y hy => (hG.dist_le_mul y x).trans ?_).trans_lt hrK
    exact mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K'.coe_nonneg
  · -- Near `x`, the mollification only sees values of `G` in `ball x δ ⊆ U`, where `G = f`.
    have hmem {y t : E} (hy : y ∈ ball x r) (ht : t ∈ ball (0 : E) r) : y - t ∈ U := by
      refine interior_subset (hδU (ball_subset_thickening hx δ ?_))
      rw [mem_ball, dist_eq_norm] at hy ⊢
      rw [mem_ball_zero_iff] at ht
      calc ‖y - t - x‖ ≤ ‖y - x‖ + ‖t‖ := by
            simpa only [sub_right_comm] using _root_.norm_sub_le (y - x) t
        _ < r + r := add_lt_add hy ht
        _ ≤ δ := by linarith [min_le_left (δ / 2) (ε / (2 * (K' + 1)))]
    refine norm_fderiv_le_of_lipschitzOn ℝ (ball_mem_nhds x hr)
      (LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_)
    refine ρ.dist_normed_convolution_le_of_dist_sub_le hG.continuous fun t ht => ?_
    rw [← hGf (hmem hy ht), ← hGf (hmem hz ht), ← dist_sub_right y z t]
    exact hf.dist_le_mul _ (hmem hy ht) _ (hmem hz ht)

/-- Data with values in a finite-dimensional space which are `K`-Lipschitz on a neighbourhood `U`
of a compact set `s` are the uniform limit on `s` of smooth maps whose derivatives are bounded by
`K` at every point of `s`. -/
theorem LipschitzOnWith.exists_seq_contDiff_tendstoUniformlyOn [FiniteDimensional ℝ F]
    {s U : Set E} (hf : LipschitzOnWith K f U) (hs : IsCompact s) (hU : U ∈ 𝓝ˢ s) :
    ∃ g : ℕ → E → F, (∀ j, ContDiff ℝ ∞ (g j)) ∧ TendstoUniformlyOn g f Filter.atTop s ∧
      ∀ j, ∀ x ∈ s, ‖fderiv ℝ (g j) x‖ ≤ K := by
  choose g hg hgf hgK using fun j : ℕ =>
    hf.exists_contDiff_dist_lt_norm_fderiv_le hs hU (Nat.one_div_pos_of_nat (n := j))
  refine ⟨g, hg, Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_, hgK⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [Filter.eventually_ge_atTop N] with j hj x hx
  rw [dist_comm]
  calc dist (g j x) (f x) < 1 / ((j : ℝ) + 1) := hgf j x hx
    _ ≤ 1 / ((N : ℝ) + 1) := by gcongr
    _ < ε := hN
