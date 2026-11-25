/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.OrderClosed
public import TauCeti.Algebra.Order.Floor.Ring

import Mathlib.Tactic.Ring

/-!
# Neighbourhoods and the intervals between multiples of a step

For a step `δ > 0` in a linearly ordered field with an integer floor and an order-closed
topology, the closed intervals `[δ m, δ (m + 1)]` with `m ∈ ℤ` through a point `x` cover a
neighbourhood of `x`: every point near `x` shares one of these intervals with `x`.

A map `G` on `X × K` which is periodic in the second coordinate near `0`, in the sense that
`G (y, t + 1) = G (y, t)` for `t` slightly below `0`, has a periodization
`(y, t) ↦ G (y, fract t)` which near every point `z` is a translate `(y, t) ↦ G (y, t - ⌊z.2⌋)`
of `G`. So the periodization inherits every local property of `G`, such as smoothness.

Away from the natural numbers, the natural floor `⌊·⌋₊` is locally constant.

## Main results

* `TauCeti.eventually_exists_int_mem_Icc_and_mem`: every point near `x` lies in an interval
  `[δ m, δ (m + 1)]` that contains `x`.
* `TauCeti.apply_fract_snd_eventuallyEq`: near every point, the periodization of a map which is
  periodic near `0` is a translate of the map.
* `TauCeti.eventually_natFloor_eq`: `⌊y⌋₊ = ⌊x⌋₊` for all `y` near a point `x` which is not a
  natural number.
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

/-- Near every point `z`, the periodization `(y, t) ↦ G (y, fract t)` of a map `G` which is periodic
in its second coordinate near `0` is the translate `(y, t) ↦ G (y, t - ⌊z.2⌋)` of `G`. -/
theorem apply_fract_snd_eventuallyEq {X M : Type*} [TopologicalSpace X] {G : X × K → M} {ε : K}
    (hε : 0 < ε) (hG : ∀ y {t : K}, -ε < t → t < 0 → G (y, t + 1) = G (y, t)) (z : X × K) :
    (fun w : X × K ↦ G (w.1, Int.fract w.2)) =ᶠ[𝓝 z] fun w ↦ G (w.1, w.2 - ⌊z.2⌋) := by
  have hz₁ : z.2 < ⌊z.2⌋ + 1 := Int.lt_floor_add_one _
  have hz₀ : (⌊z.2⌋ : K) ≤ z.2 := Int.floor_le _
  have hδ : 0 < min ε 1 := lt_min hε one_pos
  have hδε : min ε 1 ≤ ε := min_le_left _ _
  have hδ₁ : min ε 1 ≤ 1 := min_le_right _ _
  by_cases h : Int.fract z.2 = 0
  · -- At the seam, `fract` jumps by `1`, across which `G` is periodic.
    rw [← Int.self_sub_floor, sub_eq_zero] at h
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds
        (by linarith : (⌊z.2⌋ : K) - min ε 1 < z.2),
      (isOpen_lt continuous_snd continuous_const).mem_nhds
        (by linarith : z.2 < ⌊z.2⌋ + min ε 1)] with w hw₀ hw₁
    rcases le_or_gt (⌊z.2⌋ : K) w.2 with hw | hw
    · have h' : Int.fract w.2 = w.2 - ⌊z.2⌋ :=
        Int.fract_eq_iff.2 ⟨by linarith, by linarith, ⌊z.2⌋, by ring⟩
      rw [h']
    · have h' : Int.fract w.2 = w.2 - ⌊z.2⌋ + 1 :=
        Int.fract_eq_iff.2 ⟨by linarith, by linarith, ⌊z.2⌋ - 1, by push_cast; ring⟩
      rw [h']
      exact hG _ (by linarith) (by linarith)
  · -- Off the seam, `fract` is a translation near `z`.
    have hz : (⌊z.2⌋ : K) < z.2 :=
      lt_of_le_of_ne hz₀ fun h' ↦ h (by rw [← Int.self_sub_floor]; linarith)
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hz,
      (isOpen_lt continuous_snd continuous_const).mem_nhds hz₁] with w hw₀ hw₁
    have h' : Int.fract w.2 = w.2 - ⌊z.2⌋ :=
      Int.fract_eq_iff.2 ⟨by linarith, by linarith, ⌊z.2⌋, by ring⟩
    rw [h']

/-- Away from the natural numbers `⌊·⌋₊` is locally constant. -/
theorem eventually_natFloor_eq {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] [TopologicalSpace R] [OrderClosedTopology R] {x : R}
    (hx : ∀ n : ℕ, x ≠ n) : ∀ᶠ y in 𝓝 x, ⌊y⌋₊ = ⌊x⌋₊ := by
  rcases lt_or_ge x 0 with hx0 | hx0
  · filter_upwards [Iio_mem_nhds hx0] with y hy
    rw [Nat.floor_of_nonpos hy.le, Nat.floor_of_nonpos hx0.le]
  · have hlt : (⌊x⌋₊ : R) < x := lt_of_le_of_ne (Nat.floor_le hx0) (hx _).symm
    filter_upwards [Ioo_mem_nhds hlt (Nat.lt_floor_add_one x)] with y hy
    exact (Nat.floor_eq_iff ((Nat.cast_nonneg _).trans hy.1.le)).mpr ⟨hy.1.le, hy.2⟩

end TauCeti
