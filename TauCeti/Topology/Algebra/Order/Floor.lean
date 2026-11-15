/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.OrderClosed
public import TauCeti.Algebra.Order.Floor.Ring

/-!
# Neighbourhoods and the intervals between multiples of a step

For a step `δ > 0` in a linearly ordered field with an integer floor and an order-closed
topology, the closed intervals `[δ m, δ (m + 1)]` with `m ∈ ℤ` through a point `x` cover a
neighbourhood of `x`: every point near `x` shares one of these intervals with `x`.

## Main results

* `TauCeti.eventually_exists_int_mem_Icc_and_mem`: every point near `x` lies in an interval
  `[δ m, δ (m + 1)]` that contains `x`.
-/

public section

open Set Filter Topology

namespace TauCeti

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
  [TopologicalSpace K] [OrderClosedTopology K] {δ : K}

/-- For a step `δ > 0`, every point near `x` shares an interval `[δ m, δ (m + 1)]`, `m ∈ ℤ`,
with `x`. -/
theorem eventually_exists_int_mem_Icc_and_mem (hδ : 0 < δ) (x : K) :
    ∀ᶠ y in 𝓝 x, ∃ m : ℤ,
      x ∈ Icc (δ * m) (δ * (m + 1)) ∧ y ∈ Icc (δ * m) (δ * (m + 1)) := by
  have hm₁ : δ * ⌊x / δ⌋ ≤ x := (mem_Icc_mul_floor_div hδ x).1
  have hm₂ : x < δ * (⌊x / δ⌋ + 1) := by
    rw [mul_comm, ← div_lt_iff₀ hδ]
    exact Int.lt_floor_add_one _
  have hn₁ : δ * ((⌈x / δ⌉ - 1 : ℤ) : K) < x := by
    rw [mul_comm, ← lt_div_iff₀ hδ]
    push_cast
    linarith [Int.ceil_lt_add_one (x / δ)]
  have hn₂ : x ≤ δ * (((⌈x / δ⌉ - 1 : ℤ) : K) + 1) := by
    rw [mul_comm, ← div_le_iff₀ hδ]
    push_cast
    linarith [Int.le_ceil (x / δ)]
  filter_upwards [Ioo_mem_nhds hn₁ hm₂] with y hy
  rcases le_total x y with hxy | hyx
  · exact ⟨⌊x / δ⌋, ⟨hm₁, hm₂.le⟩, hm₁.trans hxy, hy.2.le⟩
  · exact ⟨⌈x / δ⌉ - 1, ⟨hn₁.le, hn₂⟩, hy.1.le, hyx.trans hn₂⟩

end TauCeti
