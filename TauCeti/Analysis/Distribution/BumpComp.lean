/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Testing a continuous function against bumps composed with a curve

A variant of the fundamental lemma of the calculus of variations on an interval, in which the test
functions are smooth bumps `ψ` on a normed space `E` composed with a fixed continuous curve
`F : ℝ → E`: if `∫ₐᵀ g(σ) ψ(F σ) dσ = 0` for every bump `ψ` centred at `F σ₀`, and `σ₀` is the only
point of `[a, T]` at which `F` takes the value `F σ₀` (for instance, `F` is injective on `[a, T]`),
then `g σ₀ = 0`. Such test functions arise when a bump is pulled back along a function that
decreases strictly along a curve, for instance a Morse function along a negative-gradient orbit.

## Main results

* `ContinuousOn.nonpos_of_forall_intervalIntegral_mul_contDiffBump_comp`: the one-sided version.
* `ContinuousOn.eq_zero_of_forall_intervalIntegral_mul_contDiffBump_comp`.
-/

public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

/-- **A one-sided test against bumps composed with a curve.** If `∫ₐᵀ b(σ) ψ(F σ) dσ = 0` for
every smooth bump `ψ` centred at `F σ₀`, with `b` and `F` continuous on `[a, T]`, `a < T`,
`σ₀ ∈ [a, T]`, and `σ₀` the only point of `[a, T]` at which `F` takes the value `F σ₀`, then
`b σ₀ ≤ 0`. -/
theorem ContinuousOn.nonpos_of_forall_intervalIntegral_mul_contDiffBump_comp {b : ℝ → ℝ}
    {F : ℝ → E} {a T σ₀ : ℝ} (hb : ContinuousOn b (Icc a T)) (hF : ContinuousOn F (Icc a T))
    (hFσ₀ : ∀ σ ∈ Icc a T, F σ = F σ₀ → σ = σ₀) (haT : a < T) (hσ₀ : σ₀ ∈ Icc a T)
    (h : ∀ ψ : ContDiffBump (F σ₀), ∫ σ in a..T, b σ * ψ (F σ) = 0) : b σ₀ ≤ 0 := by
  by_contra! hpos
  -- `b` is positive on `ball σ₀ δ ∩ [a, T]`.
  obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhdsWithin_iff.1 ((hb σ₀ hσ₀).eventually (lt_mem_nhds hpos))
  -- Away from `σ₀`, `F` stays outside a ball `ball (F σ₀) r`, since it maps the compact set
  -- `[a, T] \ ball σ₀ δ` to a compact set not containing `F σ₀`.
  have hK : IsCompact (F '' (Icc a T \ Metric.ball σ₀ δ)) :=
    (isCompact_Icc.diff Metric.isOpen_ball).image_of_continuousOn (hF.mono sdiff_subset)
  have hFK : F σ₀ ∉ F '' (Icc a T \ Metric.ball σ₀ δ) := by
    rintro ⟨σ, ⟨hσ, hσδ⟩, hFσ⟩
    exact hσδ (hFσ₀ σ hσ hFσ ▸ Metric.mem_ball_self hδ)
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl _ hFK
  -- A bump `ψ` around `F σ₀` of outer radius `r`, so that `ψ ∘ F` vanishes off `ball σ₀ δ`.
  let ψ : ContDiffBump (F σ₀) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hnonneg : ∀ σ ∈ Icc a T, 0 ≤ b σ * ψ (F σ) := fun σ hσ ↦ by
    by_cases hσδ : σ ∈ Metric.ball σ₀ δ
    · exact mul_nonneg (hδb ⟨hσδ, hσ⟩).le ψ.nonneg
    · refine (mul_eq_zero_of_right _ (ψ.zero_of_le_dist (not_lt.1 fun hFσ ↦ ?_))).ge
      exact hrK hFσ ⟨σ, ⟨hσ, hσδ⟩, rfl⟩
  -- The integrand is nonnegative and positive at `σ₀`, so its integral is positive.
  have hcont : ContinuousOn (fun σ ↦ b σ * ψ (F σ)) (Icc a T) :=
    hb.mul (ψ.continuous.comp_continuousOn hF)
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt haT
    continuousOn_const hcont (fun σ hσ ↦ hnonneg σ (Ioc_subset_Icc_self hσ))
    ⟨σ₀, hσ₀, mul_pos hpos (ψ.pos_of_mem_ball (Metric.mem_ball_self hr))⟩
  rw [intervalIntegral.integral_zero, h ψ] at hlt
  exact lt_irrefl _ hlt

/-- **Testing against bumps composed with a curve.** If `∫ₐᵀ g(σ) ψ(F σ) dσ = 0` for every smooth
bump `ψ` centred at `F σ₀`, with `g` and `F` continuous on `[a, T]`, `a < T`, `σ₀ ∈ [a, T]`, and
`σ₀` the only point of `[a, T]` at which `F` takes the value `F σ₀`, then `g σ₀ = 0`. -/
theorem ContinuousOn.eq_zero_of_forall_intervalIntegral_mul_contDiffBump_comp {g : ℝ → ℝ}
    {F : ℝ → E} {a T σ₀ : ℝ} (hg : ContinuousOn g (Icc a T)) (hF : ContinuousOn F (Icc a T))
    (hFσ₀ : ∀ σ ∈ Icc a T, F σ = F σ₀ → σ = σ₀) (haT : a < T) (hσ₀ : σ₀ ∈ Icc a T)
    (h : ∀ ψ : ContDiffBump (F σ₀), ∫ σ in a..T, g σ * ψ (F σ) = 0) : g σ₀ = 0 := by
  have hle := hg.nonpos_of_forall_intervalIntegral_mul_contDiffBump_comp hF hFσ₀ haT hσ₀ h
  have hge := hg.neg.nonpos_of_forall_intervalIntegral_mul_contDiffBump_comp (b := fun σ ↦ -g σ) hF
    hFσ₀ haT hσ₀ fun ψ ↦ by simp only [neg_mul, intervalIntegral.integral_neg, h ψ, neg_zero]
  linarith
