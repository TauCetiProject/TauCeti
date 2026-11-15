/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Chaining pairwise almost-everywhere comparisons

Harnack inequalities for functions defined only almost everywhere are stated pairwise: for sets
`A` and `B`, almost every `x ∈ A` and almost every `y ∈ B` satisfy `f y ≤ c * f x`. This avoids
the junk values of a real essential supremum or infimum. This file shows that such comparisons
compose through a set of positive measure, and so propagate along a chain of sets in which
consecutive sets overlap in positive measure. This is how a Harnack inequality on small balls
gives one on a larger ball, with a constant controlled by the length of the chain.

## Main declarations

* `TauCeti.ae_ae_le_mul_trans`: comparisons between `A` and `B` and between `B` and `D` give one
  between `A` and `D`, when `B` has positive measure.
* `TauCeti.ae_ae_le_pow_mul_of_chain`: along a chain `S 0, …, S m` of sets with overlapping
  neighbours, comparisons within each set give a comparison between `S 0` and `S m`, in both
  directions, with constant `C ^ (m + 1)`.
* `TauCeti.ae_ae_le_pow_mul_of_forall_mem_closedBall`: in a proper real normed space, a
  comparison on every ball `B(z, ρ)` with `z ∈ closedBall x₀ r` gives one on `B(x₀, r)`, with
  constant `C ^ (2 * m + 2)` whenever `r < m ρ`.
-/

public section

open Filter MeasureTheory Metric

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ} {A B D : Set X} {c d C : ℝ}

/-- **Composition of pairwise comparisons.** If almost every `x ∈ A` and `y ∈ B` satisfy
`f y ≤ c * f x`, and almost every `y ∈ B` and `z ∈ D` satisfy `f z ≤ d * f y`, with `d ≥ 0` and
`B` of positive measure, then almost every `x ∈ A` and `z ∈ D` satisfy `f z ≤ d * c * f x`. -/
theorem ae_ae_le_mul_trans (hd : 0 ≤ d) (hB : μ B ≠ 0)
    (h₁ : ∀ᵐ x ∂μ.restrict A, ∀ᵐ y ∂μ.restrict B, f y ≤ c * f x)
    (h₂ : ∀ᵐ y ∂μ.restrict B, ∀ᵐ z ∂μ.restrict D, f z ≤ d * f y) :
    ∀ᵐ x ∂μ.restrict A, ∀ᵐ z ∂μ.restrict D, f z ≤ d * c * f x := by
  have : (ae (μ.restrict B)).NeBot := ae_neBot.2 (by rwa [Ne, Measure.restrict_eq_zero])
  filter_upwards [h₁] with x hx
  obtain ⟨y, hxy, hy⟩ := (hx.and h₂).exists
  filter_upwards [hy] with z hz
  calc f z ≤ d * f y := hz
    _ ≤ d * (c * f x) := mul_le_mul_of_nonneg_left hxy hd
    _ = d * c * f x := (mul_assoc _ _ _).symm

/-- **Harnack chains.** Let `S 0, …, S m` be sets such that consecutive sets `S j` and `S (j + 1)`
meet in a set of positive measure, and such that almost every `x, y ∈ S j` satisfy
`f y ≤ C * f x`, with `C ≥ 0`. Then almost every `x ∈ S 0` and `y ∈ S m` satisfy
`f y ≤ C ^ (m + 1) * f x`, and so do almost every `x ∈ S m` and `y ∈ S 0`. -/
theorem ae_ae_le_pow_mul_of_chain (S : ℕ → Set X) (hC : 0 ≤ C) {m : ℕ}
    (hS : ∀ j ≤ m, ∀ᵐ x ∂μ.restrict (S j), ∀ᵐ y ∂μ.restrict (S j), f y ≤ C * f x)
    (hI : ∀ j < m, μ (S j ∩ S (j + 1)) ≠ 0) :
    (∀ᵐ x ∂μ.restrict (S 0), ∀ᵐ y ∂μ.restrict (S m), f y ≤ C ^ (m + 1) * f x) ∧
      ∀ᵐ x ∂μ.restrict (S m), ∀ᵐ y ∂μ.restrict (S 0), f y ≤ C ^ (m + 1) * f x := by
  induction m with
  | zero => simpa using hS 0 le_rfl
  | succ m ih =>
    obtain ⟨h₀, h₁⟩ := ih (fun j hj => hS j (hj.trans m.le_succ))
      (fun j hj => hI j (hj.trans m.lt_succ_self))
    have hm := hS (m + 1) le_rfl
    have hI' := hI m m.lt_succ_self
    -- Both directions pass through the overlap `S m ∩ S (m + 1)` of the last two sets.
    have hl : S m ∩ S (m + 1) ⊆ S m := Set.inter_subset_left
    have hr : S m ∩ S (m + 1) ⊆ S (m + 1) := Set.inter_subset_right
    constructor
    · have := ae_ae_le_mul_trans hC hI'
        (h₀.mono fun x hx => ae_restrict_of_ae_restrict_of_subset hl hx)
        (ae_restrict_of_ae_restrict_of_subset hr hm)
      simpa only [pow_succ', mul_assoc] using this
    · have := ae_ae_le_mul_trans (pow_nonneg hC _) hI'
        (hm.mono fun x hx => ae_restrict_of_ae_restrict_of_subset hr hx)
        (ae_restrict_of_ae_restrict_of_subset hl h₁)
      simpa only [pow_succ] using this

/-- **Harnack chains of balls.** Let `μ` be positive on nonempty open subsets of a proper real
normed space, and let `0 < ρ` and `r < m ρ`. If for every `z ∈ closedBall x₀ r` almost every
`x, y ∈ B(z, ρ)` satisfy `f y ≤ C * f x`, with `C ≥ 0`, then almost every `x, y ∈ B(x₀, r)`
satisfy `f y ≤ C ^ (2 * m + 2) * f x`. -/
theorem ae_ae_le_pow_mul_of_forall_mem_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [MeasurableSpace E] {μ : Measure E} [μ.IsOpenPosMeasure]
    {f : E → ℝ} {x₀ : E} {r ρ : ℝ} {m : ℕ} (hC : 0 ≤ C) (hρ : 0 < ρ) (hmρ : r < m * ρ)
    (h : ∀ z ∈ closedBall x₀ r, ∀ᵐ x ∂μ.restrict (ball z ρ), ∀ᵐ y ∂μ.restrict (ball z ρ),
      f y ≤ C * f x) :
    ∀ᵐ x ∂μ.restrict (ball x₀ r), ∀ᵐ y ∂μ.restrict (ball x₀ r), f y ≤ C ^ (2 * m + 2) * f x := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  have hm : (0 : ℝ) < m := pos_of_mul_pos_left (hr.trans hmρ) hρ.le
  have hmρ' : 1 / m * r < ρ := by rwa [one_div_mul_eq_div, div_lt_iff₀' hm]
  -- Each `y ∈ closedBall x₀ r` is joined to `x₀` by the chain of the `m + 1` balls of radius `ρ`
  -- centred at `x₀ + (j / m) (y - x₀)`, whose consecutive centres are less than `ρ` apart.
  have hchain : ∀ y ∈ closedBall x₀ r,
      (∀ᵐ x ∂μ.restrict (ball x₀ ρ), ∀ᵐ z ∂μ.restrict (ball y ρ), f z ≤ C ^ (m + 1) * f x) ∧
        ∀ᵐ x ∂μ.restrict (ball y ρ), ∀ᵐ z ∂μ.restrict (ball x₀ ρ), f z ≤ C ^ (m + 1) * f x := by
    intro y hy
    rw [mem_closedBall, dist_comm] at hy
    have := ae_ae_le_pow_mul_of_chain
      (fun j : ℕ => ball (AffineMap.lineMap x₀ y ((j : ℝ) / m)) ρ) hC (m := m)
      (fun j hj => h _ ?_) (fun j _ => ?_)
    · simpa [div_self hm.ne'] using this
    · -- The centres lie on the segment from `x₀` to `y`.
      rw [mem_closedBall, dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (j : ℝ) / m * dist x₀ y ≤ 1 * r := by
            gcongr
            exact div_le_one_of_le₀ (by exact_mod_cast hj) hm.le
        _ = r := one_mul r
    · -- Consecutive centres are less than `ρ` apart, so consecutive balls overlap.
      refine (isOpen_ball.inter isOpen_ball).measure_ne_zero μ
        ⟨AffineMap.lineMap x₀ y (((j + 1 : ℕ) : ℝ) / m), ?_, mem_ball_self hρ⟩
      rw [mem_ball, dist_lineMap_lineMap, Real.dist_eq]
      calc |((j + 1 : ℕ) : ℝ) / m - (j : ℝ) / m| * dist x₀ y ≤ 1 / m * r := by
            gcongr
            push_cast
            rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity)]
        _ < ρ := hmρ'
  -- Any two balls of a finite cover are compared through `B(x₀, ρ)`.
  obtain ⟨t, hts, htf, hcover⟩ := finite_cover_balls_of_compact (isCompact_closedBall x₀ r) hρ
  have hU : ∀ᵐ x ∂μ.restrict (⋃ y ∈ t, ball y ρ), ∀ᵐ z ∂μ.restrict (⋃ y ∈ t, ball y ρ),
      f z ≤ C ^ (2 * m + 2) * f x := by
    rw [ae_restrict_biUnion_iff _ htf.countable]
    intro y hy
    filter_upwards [(Filter.eventually_all_finite htf).2 fun y' hy' =>
      ae_ae_le_mul_trans (by positivity) (measure_ball_pos μ x₀ hρ).ne'
        (hchain y (hts hy)).2 (hchain y' (hts hy')).1] with x hx
    rw [show 2 * m + 2 = (m + 1) + (m + 1) by ring, pow_add]
    exact (ae_restrict_biUnion_iff _ htf.countable _).2 hx
  have hsub : ball x₀ r ⊆ ⋃ y ∈ t, ball y ρ := ball_subset_closedBall.trans hcover
  exact (ae_restrict_of_ae_restrict_of_subset hsub hU).mono fun x hx =>
    ae_restrict_of_ae_restrict_of_subset hsub hx

end TauCeti
