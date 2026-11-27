/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Basic

/-!
# Testing a function against bumps on an interval

The pointwise, local form of the fundamental lemma of the calculus of variations: a function
`g : ℝ → ℝ` vanishes at a time `t₀ ∈ [a, b]` if, for every smooth bump `φ` supported near `t₀`,
the product `φ g` is continuous on `[a, b]`, and its integral over `[a, b]` vanishes whenever `φ`
is moreover supported in `(a, b)` (`TauCeti.eq_zero_of_intervalIntegral_contDiffBump_mul_eq_zero`).

Only the bumps near `t₀` are tested, and `g` is only assumed continuous near `t₀` through these
products, so the lemma applies to a function `g` that is only meaningful near `t₀`, such as the
pairing of a curve's velocity with a vector field in one chart. This is the final step of the
first variation arguments showing that the critical points of action functionals solve their
Euler–Lagrange equations.
-/

public section

open Set Metric Filter

namespace TauCeti

/-- The positive half of `TauCeti.eq_zero_of_intervalIntegral_contDiffBump_mul_eq_zero`: `g` is not
positive at `t₀`. A bump equal to `1` near `t₀` shows that `g` is continuous at `t₀` within
`[a, b]`; if `g t₀ > 0`, a bump centred at an interior time near `t₀`, where `g > 0`, has a
positive integral against `g`. -/
private theorem not_pos_of_intervalIntegral_contDiffBump_mul_eq_zero {g : ℝ → ℝ} {a b t₀ δ : ℝ}
    (hab : a < b) (ht₀ : t₀ ∈ Icc a b) (hδ : 0 < δ)
    (hcont : ∀ {c : ℝ} (φ : ContDiffBump c), tsupport φ ⊆ ball t₀ δ →
      ContinuousOn (fun t ↦ φ t * g t) (Icc a b))
    (hint : ∀ {c : ℝ} (φ : ContDiffBump c), tsupport φ ⊆ ball t₀ δ ∩ Ioo a b →
      ∫ t in a..b, φ t * g t = 0) :
    ¬0 < g t₀ := by
  intro hg₀
  -- `g` is continuous at `t₀` within `[a, b]`, where it agrees with `φ g` for a bump `φ` equal to
  -- `1` near `t₀`
  have hgcont : ContinuousWithinAt g (Icc a b) t₀ := by
    obtain ⟨φ, hφ⟩ := exists_contDiffBump_tsupport_subset_ball t₀ hδ
    refine (hcont φ hφ t₀ ht₀).congr_of_eventuallyEq ?_ (by rw [φ.one_of_mem_closedBall
      (mem_closedBall_self φ.rIn_pos.le), one_mul])
    filter_upwards [mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds t₀ φ.rIn_pos)] with t ht
    rw [φ.one_of_mem_closedBall ht, one_mul]
  obtain ⟨ε, hε, hεg⟩ := Metric.mem_nhdsWithin_iff.mp (hgcont.eventually (lt_mem_nhds hg₀))
  -- an interior time `t₁` near `t₀`, and a ball around it inside `(a, b)` where `g > 0`
  obtain ⟨t₁, ht₁, ht₁₀⟩ : ∃ t₁ ∈ Ioo a b, dist t₀ t₁ < min δ ε :=
    Metric.mem_closure_iff.mp (by rwa [closure_Ioo hab.ne]) _ (lt_min hδ hε)
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp (isOpen_Ioo.inter isOpen_ball) t₁
    ⟨ht₁, by rwa [mem_ball, dist_comm]⟩
  obtain ⟨φ, hφ⟩ := exists_contDiffBump_tsupport_subset_ball t₁ hr
  have hφJ : tsupport φ ⊆ ball t₀ δ ∩ Ioo a b := fun t ht ↦
    ⟨ball_subset_ball (min_le_left _ _) (hrsub (hφ ht)).2, (hrsub (hφ ht)).1⟩
  have hg : ∀ t ∈ ball t₁ r, 0 < g t := fun t ht ↦
    hεg ⟨ball_subset_ball (min_le_right _ _) (hrsub ht).2, Ioo_subset_Icc_self (hrsub ht).1⟩
  -- `φ g` is nonnegative, as `g > 0` on the support of `φ`, and `φ g = g > 0` at `t₁`
  refine (intervalIntegral.integral_pos hab (hcont φ fun t ht ↦ (hφJ ht).1)
    (fun t _ ↦ ?_) ⟨t₁, Ioo_subset_Icc_self ht₁, ?_⟩).ne' (hint φ hφJ)
  · by_cases hφt : φ t = 0
    · rw [hφt, zero_mul]
    · exact mul_nonneg φ.nonneg (hg t (hφ (subset_tsupport _ hφt))).le
  · rw [φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le), one_mul]
    exact hg t₁ (mem_ball_self hr)

/-- **Testing against bumps near a point.** Let `g : ℝ → ℝ`, `a < b`, `t₀ ∈ [a, b]` and `δ > 0`.
If, for every smooth bump `φ` supported in the ball of radius `δ` about `t₀`, the product `φ g`
is continuous on `[a, b]`, and `∫_a^b φ g = 0` whenever `φ` is moreover supported in `(a, b)`,
then `g t₀ = 0`. -/
theorem eq_zero_of_intervalIntegral_contDiffBump_mul_eq_zero {g : ℝ → ℝ} {a b t₀ δ : ℝ}
    (hab : a < b) (ht₀ : t₀ ∈ Icc a b) (hδ : 0 < δ)
    (hcont : ∀ {c : ℝ} (φ : ContDiffBump c), tsupport φ ⊆ ball t₀ δ →
      ContinuousOn (fun t ↦ φ t * g t) (Icc a b))
    (hint : ∀ {c : ℝ} (φ : ContDiffBump c), tsupport φ ⊆ ball t₀ δ ∩ Ioo a b →
      ∫ t in a..b, φ t * g t = 0) :
    g t₀ = 0 := by
  refine le_antisymm (not_lt.mp (not_pos_of_intervalIntegral_contDiffBump_mul_eq_zero hab ht₀ hδ
    hcont hint)) ?_
  -- the same argument for `-g`
  have := not_pos_of_intervalIntegral_contDiffBump_mul_eq_zero (g := -g) hab ht₀ hδ
    (fun φ hφ ↦ by simp only [Pi.neg_apply, mul_neg]; exact (hcont φ hφ).neg)
    (fun φ hφ ↦ by simp only [Pi.neg_apply, mul_neg, intervalIntegral.integral_neg, hint φ hφ,
      neg_zero])
  rwa [Pi.neg_apply, neg_pos, not_lt] at this

end TauCeti
