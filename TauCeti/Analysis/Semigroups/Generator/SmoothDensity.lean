/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.SmoothVectors
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Density of smooth semigroup vectors

Convolving an orbit with a smooth kernel and evaluating at a positive time produces a smooth
vector. Shrinking the kernel and the evaluation time to zero approximates any vector. This is
the smooth-vector form of the standard regularization argument for strongly continuous semigroups.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Lemma II.1.3.
-/

public section

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ContDiff Convolution

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X)

/-- A normalized kernel with support in the ball of radius `1/(n+1)` around zero. -/
private def smoothBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  let ε : ℝ := 1 / (n + 1)
  ⟨ε / 2, ε, half_pos (by positivity), half_lt_self (by positivity)⟩

/-- The evaluation time is twice the support radius, so every sampled orbit time is positive. -/
private def smoothingTime (n : ℕ) : ℝ := 2 / (n + 1)

/-- Smooth convolution of the real-time orbit, evaluated past the support of the kernel. -/
private def smoothApprox (x : X) (n : ℕ) : X :=
  ((smoothBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (fun t : ℝ => S.realOperator t x)) (smoothingTime n)

/-- The orbit of a time-smoothed vector is the translated convolution. -/
private theorem realOperator_smoothApprox (x : X) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    S.realOperator t (S.smoothApprox x n) =
      ((smoothBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun u : ℝ => S.realOperator u x)) (t + smoothingTime n) := by
  let φ := (smoothBump n).normed volume
  let g := fun u : ℝ => S.realOperator u x
  let a := smoothingTime n
  have hcont : Continuous g := S.continuous_realOperator_apply x
  have hint : Integrable (fun s : ℝ => φ s • g (a - s)) volume := by
    exact (((smoothBump n).hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (Continuous.locallyIntegrable ((smoothBump n).contDiff_normed (n := (⊤ : ℕ∞))).continuous)
      hcont a).integrable)
  -- Unfolding convolution exposes the integrand needed for `integral_comp_comm`.
  change S.realOperator t (∫ s, φ s • g (a - s) ∂volume) =
    ∫ s, φ s • g (t + a - s) ∂volume
  rw [← (S.realOperator t).integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : φ s = 0
  · simp [hs]
  · have hsball : s ∈ Metric.ball (0 : ℝ) (smoothBump n).rOut := by
      rw [← (smoothBump n).support_normed_eq (μ := volume)]
      exact hs
    have hsabs : |s| < 1 / ((n : ℝ) + 1) := by
      simpa [smoothBump, Metric.mem_ball, Real.dist_0_eq_abs] using hsball
    have ha : 0 ≤ a - s := by
      dsimp [a, smoothingTime]
      rcases abs_lt.mp hsabs with ⟨hlo, hhi⟩
      have htwice : (2 : ℝ) / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
      rw [htwice]
      linarith
    simp only [φ, g, ContinuousLinearMap.map_smul]
    rw [add_sub_assoc]
    rw [← S.realOperator_add_apply t (a - s) ht ha x]

/-- Smoothing a semigroup orbit in time produces a vector in every generator domain. -/
private theorem isSmoothVector_smoothApprox (x : X) (n : ℕ) :
    S.IsSmoothVector (S.smoothApprox x n) := by
  let f : ℝ → X := (smoothBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (fun u : ℝ => S.realOperator u x)
  have hcont : ContDiff ℝ ∞ f :=
    (smoothBump n).hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      ((smoothBump n).contDiff_normed (n := (⊤ : ℕ∞)))
      (S.continuous_realOperator_apply x).locallyIntegrable
  have hshift : ContDiffOn ℝ ∞ (fun t => f (t + smoothingTime n)) (Ici 0) :=
    (hcont.comp (contDiff_id.add contDiff_const)).contDiffOn
  apply (S.isSmoothVector_iff_contDiffOn_realOperator _).2
  apply hshift.congr
  intro t ht
  exact S.realOperator_smoothApprox x n ht

/-- The time-smoothed vectors converge to the original vector. -/
private theorem tendsto_smoothApprox (x : X) :
    Tendsto (fun n : ℕ => S.smoothApprox x n) atTop (nhds x) := by
  let g := fun t : ℝ => S.realOperator t x
  have hg : Continuous g := S.continuous_realOperator_apply x
  have hδ : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφ : Tendsto (fun n : ℕ => (smoothBump n).rOut) atTop (nhds 0) := by
    simpa [smoothBump] using hδ
  have ht : Tendsto smoothingTime atTop (nhds (0 : ℝ)) := by
    -- Eta expansion lets `simp` unfold the evaluation time at each `n`.
    change Tendsto (fun n : ℕ => smoothingTime n) atTop (nhds (0 : ℝ))
    simpa [smoothingTime, div_eq_mul_inv] using hδ.const_mul 2
  have hlim : Tendsto (uncurry (fun _ : ℕ => g)) (atTop ×ˢ nhds 0) (nhds x) := by
    -- `uncurry` of a constant family is composition with the second projection.
    change Tendsto (g ∘ Prod.snd) (atTop ×ˢ nhds 0) (nhds x)
    simpa [g, S.realOperator_zero] using (hg.tendsto 0).comp tendsto_snd
  exact ContDiffBump.convolution_tendsto_right hφ
    (Eventually.of_forall fun _ => hg.aestronglyMeasurable) hlim ht

/-- Smooth vectors of a strongly continuous semigroup are dense in the Banach space. -/
theorem dense_smoothVectors : Dense (S.smoothVectors : Set X) := by
  intro x
  apply mem_closure_of_tendsto (S.tendsto_smoothApprox x)
  filter_upwards with n
  exact (S.mem_smoothVectors).2 (S.isSmoothVector_smoothApprox x n)

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end

end
