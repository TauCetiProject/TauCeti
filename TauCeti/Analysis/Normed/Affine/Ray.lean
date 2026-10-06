/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Convex.Between

/-!
# Rays from a point of a normed affine space

The ray from a point `z` of a real normed affine space along a vector `d` is the set of points
`t • d +ᵥ z` with `0 ≤ t`. Near `z` a segment from `z` cannot be told apart from the ray through its
other endpoint, and two rays from `z` on which a continuous functional `ℓ` takes opposite signs
together form a graph over the coordinate `y ↦ ℓ (y -ᵥ z)`.

## Main results

* `TauCeti.mem_affineSegment_iff_of_dist_lt`: within distance `‖c -ᵥ z‖` of `z`, the segment from
  `z` to `c` is the ray from `z` through `c`.
* `TauCeti.exists_continuous_range_eq_rays`: two rays from `z` along directions where `ℓ` is
  negative and positive form the range of a continuous section of `y ↦ ℓ (y -ᵥ z)`.
-/

public section

open Set

namespace TauCeti

variable {V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- Within distance `‖c - z‖` of `z`, the segment from `z` to `c` is the ray from `z` through
`c`. -/
theorem mem_affineSegment_iff_of_dist_lt {c y z : P} (hy : dist y z < ‖c -ᵥ z‖) :
    y ∈ affineSegment ℝ z c ↔ ∃ t : ℝ, 0 ≤ t ∧ y = t • (c -ᵥ z) +ᵥ z := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, AffineMap.lineMap_apply _ _ _⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ⟨ht, ?_⟩, AffineMap.lineMap_apply _ _ _⟩
    rw [dist_vadd_left, norm_smul, Real.norm_of_nonneg ht] at hy
    by_contra! ht1
    nlinarith [norm_nonneg (c -ᵥ z)]

/-- If `ℓ d₁ < 0 < ℓ d₂`, the union of the rays from `z` along `d₁` and along `d₂` is the range of
a continuous map `g` with `ℓ (g s - z) = s`: it runs out along `d₁` for negative parameters and
along `d₂` for positive ones. -/
theorem exists_continuous_range_eq_rays (ℓ : StrongDual ℝ V) {d₁ d₂ : V} (h₁ : ℓ d₁ < 0)
    (h₂ : 0 < ℓ d₂) (z : P) : ∃ g : ℝ → P, Continuous g ∧ (∀ s, ℓ (g s -ᵥ z) = s) ∧
      ∀ y, y ∈ range g ↔
        (∃ t : ℝ, 0 ≤ t ∧ y = t • d₁ +ᵥ z) ∨ (∃ t : ℝ, 0 ≤ t ∧ y = t • d₂ +ᵥ z) := by
  refine ⟨fun s => ((max s 0 / ℓ d₂) • d₂ + (min s 0 / ℓ d₁) • d₁) +ᵥ z, by fun_prop,
    fun s => ?_, fun y => ⟨?_, ?_⟩⟩
  · rw [vadd_vsub, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      div_mul_cancel₀ _ h₂.ne', div_mul_cancel₀ _ h₁.ne, max_add_min, add_zero]
  · rintro ⟨s, rfl⟩
    rcases le_total 0 s with hs | hs
    · exact .inr ⟨s / ℓ d₂, div_nonneg hs h₂.le, by simp [max_eq_left hs, min_eq_right hs]⟩
    · exact .inl ⟨s / ℓ d₁, div_nonneg_of_nonpos hs h₁.le,
        by simp [max_eq_right hs, min_eq_left hs]⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · have hs : t * ℓ d₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht h₁.le
      exact ⟨t * ℓ d₁, by simp [max_eq_right hs, min_eq_left hs, mul_div_cancel_right₀ _ h₁.ne]⟩
    · have hs : 0 ≤ t * ℓ d₂ := mul_nonneg ht h₂.le
      exact ⟨t * ℓ d₂, by simp [max_eq_left hs, min_eq_right hs, mul_div_cancel_right₀ _ h₂.ne']⟩

end TauCeti
