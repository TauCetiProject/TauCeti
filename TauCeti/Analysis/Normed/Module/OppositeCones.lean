/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Closed cones without opposite directions

Let `Γ₁` and `Γ₂` be closed subsets of a proper real normed space, both closed under
multiplication by positive reals, such that no nonzero `ξ ∈ Γ₁` has `-ξ ∈ Γ₂`. Then the summands
of `a + b`, for `a ∈ Γ₁` and `b ∈ Γ₂`, are controlled by the sum: for some `κ > 0`,

`κ (‖a‖ + ‖b‖) ≤ ‖a + b‖`.

On the compact set of pairs `(a, b) ∈ Γ₁ × Γ₂` with `‖a‖ + ‖b‖ = 1` the continuous function
`‖a + b‖` does not vanish, so it is bounded below by some `κ > 0`, and both sides of the inequality
are homogeneous. Consequently the sum `Γ₁ + Γ₂` is closed: near a point it is the image of a
compact set of pairs.

This is the geometry behind the wave front set of a product of distributions, where `Γ₁` and `Γ₂`
contain the frequencies of the wave front sets of the factors and those of the product lie in
`Γ₁ + Γ₂`.

## Main results

* `TauCeti.exists_mul_norm_add_le_norm_add`: `κ (‖a‖ + ‖b‖) ≤ ‖a + b‖` for some `κ > 0`.
* `TauCeti.isClosed_add_of_forall_neg_mem`: the sum `Γ₁ + Γ₂` is closed.
-/

public section

open Metric Set
open scoped Pointwise

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {Γ₁ Γ₂ : Set E}

/-- **The summands are controlled by the sum.** If `Γ₁` and `Γ₂` are closed, closed under
multiplication by positive reals, and no nonzero `ξ ∈ Γ₁` has `-ξ ∈ Γ₂`, then for some `κ > 0`
every `a ∈ Γ₁` and `b ∈ Γ₂` satisfy `κ (‖a‖ + ‖b‖) ≤ ‖a + b‖`. -/
theorem exists_mul_norm_add_le_norm_add (h₁ : IsClosed Γ₁) (h₂ : IsClosed Γ₂)
    (hc₁ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₁, t • ξ ∈ Γ₁) (hc₂ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₂, t • ξ ∈ Γ₂)
    (hopp : ∀ ξ ∈ Γ₁, -ξ ∈ Γ₂ → ξ = 0) :
    ∃ κ > 0, ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, κ * (‖a‖ + ‖b‖) ≤ ‖a + b‖ := by
  -- The pairs with `‖a‖ + ‖b‖ = 1` form a compact set on which `‖a + b‖` is positive.
  set P : Set (E × E) := Γ₁ ×ˢ Γ₂ ∩ {p | ‖p.1‖ + ‖p.2‖ = 1}
  have hP : IsCompact P := by
    refine isCompact_of_isClosed_isBounded
      ((h₁.prod h₂).inter (isClosed_eq (by fun_prop) continuous_const))
      ((isBounded_closedBall (x := (0 : E × E)) (r := 1)).subset fun p hp ↦ ?_)
    have h1 : ‖p.1‖ + ‖p.2‖ = 1 := hp.2
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le (by linarith [norm_nonneg p.2]) (by linarith [norm_nonneg p.1])
  have hpos : ∀ p ∈ P, 0 < ‖p.1 + p.2‖ := by
    rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, hab⟩
    refine norm_pos_iff.2 fun h ↦ ?_
    have hba : b = -a := eq_neg_of_add_eq_zero_right h
    have ha0 : a = 0 := hopp a ha (hba ▸ hb)
    simp [ha0, hba] at hab
  obtain ⟨κ, hκ, hκP⟩ := hP.exists_forall_le' (by fun_prop) hpos
  refine ⟨κ, hκ, fun a ha b hb ↦ ?_⟩
  rcases (add_nonneg (norm_nonneg a) (norm_nonneg b)).eq_or_lt with hs | hs
  · rw [← hs, mul_zero]
    exact norm_nonneg _
  -- Rescale `(a, b)` into `P`.
  have hs' : 0 < (‖a‖ + ‖b‖)⁻¹ := inv_pos.2 hs
  have hnorm : ‖(‖a‖ + ‖b‖)⁻¹ • a‖ + ‖(‖a‖ + ‖b‖)⁻¹ • b‖ = 1 := by
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hs'.le, ← mul_add, inv_mul_cancel₀ hs.ne']
  have h := hκP (_, _) ⟨⟨hc₁ _ hs' a ha, hc₂ _ hs' b hb⟩, hnorm⟩
  rw [← smul_add, norm_smul, Real.norm_of_nonneg hs'.le, le_inv_mul_iff₀ hs] at h
  rwa [mul_comm]

/-- **The sum of closed cones without opposite directions is closed.** If `Γ₁` and `Γ₂` are closed,
closed under multiplication by positive reals, and no nonzero `ξ ∈ Γ₁` has `-ξ ∈ Γ₂`, then
`Γ₁ + Γ₂` is closed. -/
theorem isClosed_add_of_forall_neg_mem (h₁ : IsClosed Γ₁) (h₂ : IsClosed Γ₂)
    (hc₁ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₁, t • ξ ∈ Γ₁) (hc₂ : ∀ t : ℝ, 0 < t → ∀ ξ ∈ Γ₂, t • ξ ∈ Γ₂)
    (hopp : ∀ ξ ∈ Γ₁, -ξ ∈ Γ₂ → ξ = 0) : IsClosed (Γ₁ + Γ₂) := by
  obtain ⟨κ, hκ, hκab⟩ := exists_mul_norm_add_le_norm_add h₁ h₂ hc₁ hc₂ hopp
  refine isClosed_of_closure_subset fun z hz ↦ ?_
  -- Near `z`, the sum is the image of the compact set of pairs with `‖a‖ + ‖b‖ ≤ R`.
  set R := (‖z‖ + 1) / κ
  set P : Set (E × E) := Γ₁ ×ˢ Γ₂ ∩ {p | ‖p.1‖ + ‖p.2‖ ≤ R}
  have hP : IsCompact P := by
    refine isCompact_of_isClosed_isBounded
      ((h₁.prod h₂).inter (isClosed_le (by fun_prop) continuous_const))
      ((isBounded_closedBall (x := (0 : E × E)) (r := R)).subset fun p hp ↦ ?_)
    have h1 : ‖p.1‖ + ‖p.2‖ ≤ R := hp.2
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le (by linarith [norm_nonneg p.2]) (by linarith [norm_nonneg p.1])
  have hsub : (fun p : E × E ↦ p.1 + p.2) '' P ⊆ Γ₁ + Γ₂ := by
    rintro _ ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, -⟩, rfl⟩
    exact add_mem_add ha hb
  refine hsub ((hP.image (by fun_prop)).isClosed.closure_subset ?_)
  rw [Metric.mem_closure_iff] at hz ⊢
  intro ε hε
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hd⟩ := hz (min ε 1) (lt_min hε one_pos)
  refine ⟨a + b, ⟨(a, b), ⟨⟨ha, hb⟩, ?_⟩, rfl⟩, hd.trans_le (min_le_left _ _)⟩
  have hab : ‖a + b‖ ≤ ‖z‖ + 1 := by
    have h := norm_le_norm_add_norm_sub' (a + b) z
    rw [← dist_eq_norm, dist_comm] at h
    linarith [hd.trans_le (min_le_right ε 1)]
  change ‖a‖ + ‖b‖ ≤ R
  rw [le_div_iff₀ hκ, mul_comm]
  exact (hκab a ha b hb).trans hab

end TauCeti
