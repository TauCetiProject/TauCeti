/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Eventual norm boundedness under perturbations

In a seminormed group, if `f x / g x` tends to `1` (additively, `f x - g x` tends to `0`) along a
filter `l` and `‖g x‖` is eventually bounded along `l`, then `‖f x‖` is eventually bounded along
`l` (`Filter.Tendsto.exists_eventually_norm_le_of_div'`,
`Filter.Tendsto.exists_eventually_norm_le_of_sub`).
-/

public section

open Filter
open scoped Topology

/-- If `f x / g x` tends to `1` along `l` and `‖g x‖` is eventually bounded along `l`, then `‖f x‖`
is eventually bounded along `l`. -/
@[to_additive Filter.Tendsto.exists_eventually_norm_le_of_sub
/-- If `f x - g x` tends to `0` along `l` and `‖g x‖` is eventually bounded along `l`, then `‖f x‖`
is eventually bounded along `l`. -/]
theorem Filter.Tendsto.exists_eventually_norm_le_of_div' {α E : Type*} [SeminormedGroup E]
    {l : Filter α} {f g : α → E} (h : Tendsto (fun x ↦ f x / g x) l (𝓝 1))
    (hg : ∃ C, ∀ᶠ x in l, ‖g x‖ ≤ C) :
    ∃ C, ∀ᶠ x in l, ‖f x‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := h.norm'.isBoundedUnder_le.eventually_le
  obtain ⟨C₂, hC₂⟩ := hg
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [hC₁, hC₂] with x hx₁ hx₂
  calc ‖f x‖ = ‖f x / g x * g x‖ := by rw [div_mul_cancel]
    _ ≤ ‖f x / g x‖ + ‖g x‖ := norm_mul_le' _ _
    _ ≤ C₁ + C₂ := add_le_add hx₁ hx₂
