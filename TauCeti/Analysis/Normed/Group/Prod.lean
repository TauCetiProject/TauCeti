/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real

import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Order.OrderClosed

/-!
# Weighted lower bounds for the product norm

The norm on a product of seminormed groups is the maximum of the coordinate norms.
`Prod.min_mul_norm_pow_le_add` bounds a weighted sum of `n`-th powers of coordinate norms below
by `min a b * ‖x‖ ^ n`, provided at least one coefficient is nonnegative. The other coefficient
may be negative, allowing the estimate to apply to quadratic forms with a signed mass term.
`Prod.norm_mul_self_le_sq_add_sq_add_sq` bounds the squared sup norm on `ℝ³` by the sum of the
squares of the coordinates.
`TauCeti.exists_setOf_norm_fst_sq_add_norm_snd_sq_lt_subset` shows that the round balls
`‖z.1‖² + ‖z.2‖² < r²` form a basis of neighbourhoods of the origin.
`TauCeti.isOpen_setOf_norm_fst_lt_and_lt_norm_snd` shows that the regions `‖z.1‖ < r`,
`R < ‖z.2‖` are open, and `TauCeti.norm_fst_le_and_sub_le_norm_snd_of_mem_closedBall` that a
closed ball of radius `ε` about `w` lies in the region `‖z.1‖ ≤ ‖w.1‖ + ε`, `‖w.2‖ - ε ≤ ‖z.2‖`.
-/

public section

/-- A weighted sum of `n`-th powers of coordinate norms bounds the `n`-th power of the product
norm below with coefficient `min a b`, provided at least one coefficient is nonnegative. -/
theorem Prod.min_mul_norm_pow_le_add {E F : Type*} [SeminormedAddGroup E] [SeminormedAddGroup F]
    (x : E × F) (n : ℕ) {a b : ℝ} (h : 0 ≤ max a b) :
    min a b * ‖x‖ ^ n ≤ a * ‖x.1‖ ^ n + b * ‖x.2‖ ^ n := by
  have hs := pow_nonneg (norm_nonneg x.1) n
  have ht := pow_nonneg (norm_nonneg x.2) n
  rcases le_total a b with hab | hab <;> rcases le_total ‖x.1‖ ‖x.2‖ with hx | hx <;>
    simp only [Prod.norm_def, min_eq_left, min_eq_right, max_eq_left, max_eq_right, hab, hx]
      at h ⊢ <;>
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hx n]

/-- The square of the sup norm on `ℝ³` is at most the sum of the squares of the coordinates. -/
theorem Prod.norm_mul_self_le_sq_add_sq_add_sq (v : ℝ × ℝ × ℝ) :
    ‖v‖ * ‖v‖ ≤ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
  have hv : ‖v‖ ≤ √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩ <;>
      refine Real.abs_le_sqrt ?_ <;> nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
  exact (mul_self_le_mul_self (norm_nonneg v) hv).trans (Real.mul_self_sqrt (by positivity)).le

namespace TauCeti

open Topology

/-- Every neighbourhood of the origin of a product of seminormed groups contains a round ball
`‖z.1‖² + ‖z.2‖² < r²` with `r > 0`. -/
theorem exists_setOf_norm_fst_sq_add_norm_snd_sq_lt_subset {E F : Type*} [SeminormedAddGroup E]
    [SeminormedAddGroup F] {U : Set (E × F)} (hU : U ∈ 𝓝 0) :
    ∃ r > 0, {z : E × F | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2} ⊆ U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨r, hr, fun z hz ↦ hball ?_⟩
  have h1 : ‖z.1‖ < r := lt_of_pow_lt_pow_left₀ 2 hr.le (by nlinarith [sq_nonneg ‖z.2‖, hz.out])
  have h2 : ‖z.2‖ < r := lt_of_pow_lt_pow_left₀ 2 hr.le (by nlinarith [sq_nonneg ‖z.1‖, hz.out])
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
  exact max_lt h1 h2

/-- The region `‖z.1‖ < r`, `R < ‖z.2‖` of a product of seminormed groups is open. -/
theorem isOpen_setOf_norm_fst_lt_and_lt_norm_snd {E F : Type*} [SeminormedAddGroup E]
    [SeminormedAddGroup F] (r R : ℝ) : IsOpen {z : E × F | ‖z.1‖ < r ∧ R < ‖z.2‖} :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    (isOpen_lt continuous_const (continuous_norm.comp continuous_snd))

/-- A point of the closed ball of radius `ε` about `w` in a product of seminormed commutative
groups has first component of norm at most `‖w.1‖ + ε` and second component of norm at least
`‖w.2‖ - ε`. -/
theorem norm_fst_le_and_sub_le_norm_snd_of_mem_closedBall {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {w z : E × F} {ε : ℝ}
    (hz : z ∈ Metric.closedBall w ε) :
    ‖z.1‖ ≤ ‖w.1‖ + ε ∧ ‖w.2‖ - ε ≤ ‖z.2‖ := by
  rw [mem_closedBall_iff_norm] at hz
  have h₁ : ‖z.1 - w.1‖ ≤ ε := (norm_fst_le (z - w)).trans hz
  have h₂ : ‖z.2 - w.2‖ ≤ ε := (norm_snd_le (z - w)).trans hz
  constructor
  · linarith [norm_le_norm_add_norm_sub' z.1 w.1]
  · linarith [norm_le_norm_add_norm_sub' w.2 z.2, norm_sub_rev w.2 z.2]

end TauCeti
