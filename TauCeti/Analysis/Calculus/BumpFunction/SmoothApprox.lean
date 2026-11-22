/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Zhiyuan Zhang, Leheng Chen
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
`LipschitzWith.exists_seq_contDiff_lipschitzWith_tendsto` gives a pointwise approximation sequence
of bounded smooth real functions with the same Lipschitz constant and a common bound `|f| + 1`.

The construction combines Mathlib's McShane extension and normalized smooth bumps with
`LipschitzWith.normed_convolution`. Derivative bounds follow directly from Mathlib's
`norm_fderiv_le_of_lipschitz`.
`LipschitzWith.exists_contDiffBump_normed_convolution` also bounds the bump's outer radius,
so additional local properties can be proved for the same approximating convolution; for instance
`LipschitzWith.exists_contDiff_lipschitzWith_dist_lt_fderiv_eq_zero` gives approximations whose
differential vanishes wherever the function is constant on a ball of fixed radius.

## References

* D. Azagra, J. Ferrera, F. López-Mesas and Y. Rangel,
  *Smooth approximation of Lipschitz functions on Riemannian manifolds*,
  J. Math. Anal. Appl. 326 (2007), 1370–1378, Section 2.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped Convolution ContDiff NNReal Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {K : ℝ≥0} {f : E → F}

/-- A Lipschitz function can be mollified with a normalized smooth bump of arbitrarily small
outer radius, retaining its Lipschitz constant and any prescribed strict uniform error. -/
theorem LipschitzWith.exists_contDiffBump_normed_convolution [MeasurableSpace E] [BorelSpace E]
    (hf : LipschitzWith K f) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ φ : ContDiffBump (0 : E), φ.rOut ≤ δ ∧
      ContDiff ℝ ∞ (φ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] f) ∧
      LipschitzWith K (φ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] f) ∧
      ∀ x, dist ((φ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] f) x) (f x) < ε := by
  obtain ⟨r, hr, hbound⟩ := exists_pos_mul_lt hε (K : ℝ)
  have hρ : 0 < min δ r := lt_min hδ hr
  let φ : ContDiffBump (0 : E) :=
    ⟨min δ r / 2, min δ r, half_pos hρ, half_lt_self hρ⟩
  refine ⟨φ, min_le_left _ _, ?_, hf.normed_convolution φ, fun x ↦ ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hf.continuous.locallyIntegrable
  · exact (hf.dist_normed_convolution_le φ x).trans_lt
      ((mul_le_mul_of_nonneg_left (min_le_right δ r) K.coe_nonneg).trans_lt hbound)

/-- A Lipschitz function has smooth uniform approximations with exactly the same Lipschitz
bound. The domain may have dimension zero, and the function need not be bounded. -/
theorem LipschitzWith.exists_contDiff_lipschitzWith_dist_lt (hf : LipschitzWith K f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ LipschitzWith K g ∧ ∀ x, dist (g x) (f x) < ε := by
  borelize E
  obtain ⟨φ, -, hsmooth, hLip, herr⟩ := hf.exists_contDiffBump_normed_convolution one_pos hε
  exact ⟨φ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] f, hsmooth, hLip, herr⟩

/-- A Lipschitz function has smooth uniform approximations with exactly the same Lipschitz bound
whose differential vanishes at every point `x` such that the function is constant on the ball of
radius `r` about `x`. -/
theorem LipschitzWith.exists_contDiff_lipschitzWith_dist_lt_fderiv_eq_zero (hf : LipschitzWith K f)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ LipschitzWith K g ∧ (∀ x, dist (g x) (f x) < ε) ∧
      ∀ x, (∀ y ∈ ball x r, f y = f x) → fderiv ℝ g x = 0 := by
  borelize E
  obtain ⟨φ, hφr, hsmooth, hLip, herr⟩ :=
    hf.exists_contDiffBump_normed_convolution (half_pos hr) hε
  refine ⟨φ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] f, hsmooth, hLip, herr,
    fun x hx => ?_⟩
  -- On the ball of radius `r / 2` about `x`, the convolution only averages the constant `f x`.
  have hg : (φ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] f) =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [ball_mem_nhds x (half_pos hr)] with y hy
    have hfy : f y = f x := hx y (ball_subset_ball (half_le_self hr.le) hy)
    rw [← hfy]
    refine φ.normed_convolution_eq_right fun z hz => (hx z ?_).trans hfy.symm
    rw [mem_ball] at hy hz ⊢
    linarith [dist_triangle z y x, hz.trans_le hφr]
  rw [hg.fderiv_eq, fderiv_const_apply]

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
  obtain ⟨ρ, -, hsmooth, hLip, herr⟩ := hu.exists_contDiffBump_normed_convolution one_pos hε
  let g := ρ.normed Measure.addHaar ⋆[lsmul ℝ ℝ, Measure.addHaar] u
  have hi : ConvolutionExists (ρ.normed Measure.addHaar) u (lsmul ℝ ℝ) Measure.addHaar :=
    ρ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (lsmul ℝ ℝ) ρ.integrable_normed.locallyIntegrable hu.continuous
  refine ⟨g, hsmooth, hLip, ?_, ?_⟩
  · intro x
    exact ⟨le_convolution_lsmul_of_forall_le ρ.support_normed_eq.subset
        ρ.nonneg_normed ρ.integral_normed (hi x) (fun y _ => (hub y).1),
      convolution_lsmul_le_of_forall_le ρ.support_normed_eq.subset
        ρ.nonneg_normed ρ.integral_normed (hi x) (fun y _ => (hub y).2)⟩
  · intro x hx
    rw [heq hx]
    exact herr x

/-- A `K`-Lipschitz function is the pointwise limit of smooth functions `g n` with values in
`[-n, n]`, Lipschitz constant `K`, and `|g n| ≤ |f| + 1`. -/
theorem LipschitzWith.exists_seq_contDiff_lipschitzWith_tendsto {f : E → ℝ}
    (hf : LipschitzWith K f) :
    ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n x, |g n x| ≤ n) ∧
      (∀ n, LipschitzWith K (g n)) ∧ (∀ n x, |g n x| ≤ |f x| + 1) ∧
      ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
  have H (n : ℕ) := (hf.lipschitzOnWith (s := {x | f x ∈ Icc (-(n : ℝ)) n}))
    |>.exists_contDiff_lipschitzWith_mem_Icc_dist_lt (neg_le_self n.cast_nonneg) (fun _ hx ↦ hx)
      (Nat.one_div_pos_of_nat (n := n))
  choose g hgs hgK hgI hgf using H
  have hclose {n : ℕ} {x : E} (hx : |f x| ≤ n) : |g n x - f x| ≤ 1 / ((n : ℝ) + 1) := by
    rw [← Real.dist_eq]; exact (hgf n x (abs_le.1 hx)).le
  refine ⟨g, hgs, fun n x ↦ abs_le.2 (hgI n x), hgK,
    fun n x ↦ ?_, fun x ↦ ?_⟩
  · by_cases hx : |f x| ≤ n
    · have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 (by simp)
      linarith [abs_sub_abs_le_abs_sub (g n x) (f x), hclose hx]
    · linarith [abs_le.2 (hgI n x), not_le.1 hx]
  · obtain ⟨N, hN⟩ := exists_nat_ge |f x|
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Real.dist_eq]
    exact hclose (hN.trans (Nat.cast_le.2 hn))
