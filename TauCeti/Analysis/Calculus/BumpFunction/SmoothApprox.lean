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

The construction combines Mathlib's McShane extension and normalized smooth bumps with
`LipschitzWith.normed_convolution`. Derivative bounds follow directly from Mathlib's
`norm_fderiv_le_of_lipschitz`.

## References

* D. Azagra, J. Ferrera, F. López-Mesas and Y. Rangel,
  *Smooth approximation of Lipschitz functions on Riemannian manifolds*,
  J. Math. Anal. Appl. 326 (2007), 1370–1378, Section 2.
-/

public section

open ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped Convolution ContDiff NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K : ℝ≥0}

/-- A Lipschitz function has smooth uniform approximations with exactly the same Lipschitz
bound. The domain may have dimension zero, and the function need not be bounded. -/
theorem LipschitzWith.exists_contDiff_lipschitzWith_dist_lt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E → F} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
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

/-- Any real-valued `K`-Lipschitz function on a finite-dimensional real normed space is the
pointwise limit of a sequence of smooth bounded `K`-Lipschitz functions uniformly dominated by
`|f x| + 1`. -/
theorem LipschitzWith.exists_contDiff_lipschitzWith_abs_le_tendsto {f : E → ℝ}
    (hf : LipschitzWith K f) :
    ∃ g : ℕ → E → ℝ, (∀ n, ContDiff ℝ ∞ (g n)) ∧ (∀ n, LipschitzWith K (g n)) ∧
      (∀ n, ∃ M, ∀ x, |g n x| ≤ M) ∧ (∀ n x, |g n x| ≤ |f x| + 1) ∧
      ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
  classical
  let R : ℕ → ℝ := fun n ↦ (n : ℝ) + 1
  let ftr : ℕ → E → ℝ := fun n x ↦ max (-R n) (min (R n) (f x))
  have hR_pos (n : ℕ) : 0 < R n := by positivity
  have hftr_lip (n : ℕ) : LipschitzWith K (ftr n) := (hf.const_min (R n)).const_max (-R n)
  have hftr_mem (n : ℕ) (x : E) : ftr n x ∈ Icc (-R n) (R n) :=
    ⟨le_max_left _ _, max_le (by linarith [hR_pos n]) (min_le_left _ _)⟩
  have hftr_abs (n : ℕ) (x : E) : |ftr n x| ≤ |f x| := by
    rcases le_total (f x) (-R n) with hlo | hlo
    · have hfx_neg : f x ≤ 0 := hlo.trans (by linarith [hR_pos n])
      have heq : ftr n x = -R n := max_eq_left (min_le_of_right_le hlo)
      rw [heq, abs_neg, abs_of_pos (hR_pos n), abs_of_nonpos hfx_neg]
      linarith
    · rcases le_total (R n) (f x) with hhi | hhi
      · have hfx_pos : 0 ≤ f x := (hR_pos n).le.trans hhi
        have heq : ftr n x = R n := by
          simp only [ftr, min_eq_left hhi]
          exact max_eq_right (by linarith [hR_pos n])
        rw [heq, abs_of_pos (hR_pos n), abs_of_nonneg hfx_pos]
        exact hhi
      · have heq : ftr n x = f x := by
          simp only [ftr, min_eq_right hhi, max_eq_right hlo]
        rw [heq]
  have hε (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hex (n : ℕ) :=
    ((hftr_lip n).lipschitzOnWith (s := univ)).exists_contDiff_lipschitzWith_mem_Icc_dist_lt
      (a := -R n) (b := R n) (by linarith [hR_pos n]) (fun x _ ↦ hftr_mem n x) (hε n)
  choose g hgs hgK hg_mem hgf using hex
  refine ⟨g, hgs, hgK, fun n ↦ ⟨R n, fun x ↦ abs_le.2 (hg_mem n x)⟩, fun n x ↦ ?_, fun x ↦ ?_⟩
  · have hdist : |g n x - ftr n x| ≤ 1 := by
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
      exact (Real.dist_eq _ _ ▸ (hgf n x (mem_univ x)).le).trans h1
    linarith [abs_sub_abs_le_abs_sub (g n x) (ftr n x), hftr_abs n x]
  · apply tendsto_iff_dist_tendsto_zero.2
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    filter_upwards [eventually_ge_atTop (Nat.ceil |f x|)] with n hn
    have hfx_le : |f x| ≤ R n := by
      have hceil : |f x| ≤ (Nat.ceil |f x| : ℝ) := Nat.le_ceil |f x|
      have hcast : (Nat.ceil |f x| : ℝ) ≤ n := Nat.cast_le.2 hn
      dsimp only [R]
      linarith
    obtain ⟨hlo, hhi⟩ := abs_le.1 hfx_le
    have heq : ftr n x = f x := by simp only [ftr, min_eq_right hhi, max_eq_right hlo]
    rw [← heq]
    exact (hgf n x (mem_univ x)).le
