/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Regular curves are locally monotone along a functional

A `C¹` curve `γ : ℝ → E` in a real normed space with nowhere vanishing derivative is, on every short
parameter window `[s, s + δ]`, strictly increasing after composing with a continuous linear
functional: one of norm one that takes the value `‖γ' s‖` at `γ' s`. On a compact interval of
starting parameters the window width `δ` can be chosen uniformly.

## Main results

* `ContDiff.exists_strictMonoOn_dual_comp`: uniform windows on which a regular `C¹` curve is
  strictly increasing along a continuous linear functional.
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E}

/-- A `C¹` curve with nowhere vanishing derivative is strictly increasing after a suitable
continuous linear functional on every window `[s, s + δ]` of a uniform width `δ > 0`, for starting
parameters `s` in a compact interval `[a, b]`. -/
theorem ContDiff.exists_strictMonoOn_dual_comp (hγ : ContDiff ℝ 1 γ)
    (hderiv : ∀ t, deriv γ t ≠ 0) (a b : ℝ) :
    ∃ δ > 0, ∀ s ∈ Icc a b, ∃ φ : StrongDual ℝ E,
      StrictMonoOn (fun t ↦ φ (γ t)) (Icc s (s + δ)) := by
  rcases lt_or_ge b a with hba | hab
  · exact ⟨1, one_pos, fun s hs ↦ absurd (hs.1.trans hs.2) (not_le.2 hba)⟩
  have hcd : Continuous (deriv γ) := hγ.continuous_deriv_one
  have hdiff : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  -- A lower bound `m > 0` for `‖γ'‖` and a modulus of uniform continuity of `γ'` on `[a, b + 1]`.
  obtain ⟨t₀, -, ht₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith : a ≤ b + 1))
    (hcd.norm.continuousOn)
  have hm : 0 < ‖deriv γ t₀‖ := norm_pos_iff.2 (hderiv t₀)
  obtain ⟨δ₀, hδ₀, hu⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_Icc (a := a) (b := b + 1)).uniformContinuousOn_of_continuous hcd.continuousOn)
    _ hm
  refine ⟨min (δ₀ / 2) 1, by positivity, fun s hs ↦ ?_⟩
  set δ := min (δ₀ / 2) 1
  have hδ₁ : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδ₂ : δ ≤ 1 := min_le_right _ _
  obtain ⟨φ, hφ, hφs⟩ := exists_dual_vector ℝ (deriv γ s) (norm_ne_zero_iff.2 (hderiv s))
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hφs
  refine ⟨φ, strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (φ.continuous.comp hγ.continuous).continuousOn fun t ht ↦ ?_⟩
  obtain ⟨hst, hts⟩ := interior_subset ht
  have hd : deriv (fun t ↦ φ (γ t)) t = φ (deriv γ t) :=
    (φ.hasFDerivAt.comp_hasDerivAt t (hdiff t).hasDerivAt).deriv
  -- `‖γ' t - γ' s‖ < m ≤ ‖γ' s‖`, so `φ (γ' t) ≥ ‖γ' s‖ - ‖γ' t - γ' s‖ > 0`.
  have hclose : ‖deriv γ t - deriv γ s‖ < ‖deriv γ s‖ := by
    have h := hu t ⟨by linarith [hs.1], by linarith [hs.2]⟩ s ⟨hs.1, by linarith [hs.2]⟩
      (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith)
    rw [dist_eq_norm] at h
    exact h.trans_le (ht₀ ⟨hs.1, by linarith [hs.2]⟩)
  have hle : |φ (deriv γ t - deriv γ s)| ≤ ‖deriv γ t - deriv γ s‖ := by
    simpa [hφ] using φ.le_opNorm (deriv γ t - deriv γ s)
  rw [hd, show deriv γ t = deriv γ s + (deriv γ t - deriv γ s) by abel, map_add, hφs]
  linarith [neg_abs_le (φ (deriv γ t - deriv γ s))]
