/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Affine
import Mathlib.Tactic.Positivity

/-!
# Separating two directions by a functional

Two vectors `d₁` and `d₂` of a real locally convex Hausdorff space with `0 ∉ [-d₁, d₂]`, that is,
both nonzero and not on a common ray from `0`, are separated by a continuous functional `ℓ` with
`ℓ d₁ < 0 < ℓ d₂`. This is the geometric Hahn--Banach theorem
`geometric_hahn_banach_point_closed` applied to the point `0` and the segment `[-d₁, d₂]`. Both
strict inequalities are open conditions, so `ℓ` can moreover be perturbed to be nonzero at any
prescribed vector on which some functional does not vanish.

## Main results

* `TauCeti.exists_strongDual_neg_pos_ne_zero`: a functional negative on `d₁`, positive on `d₂`,
  and nonzero at a prescribed vector `u`.
-/

public section

open Set

namespace TauCeti

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]

/-- Two vectors with `0 ∉ [-d₁, d₂]`, that is nonzero and not on a common ray from `0`, are
separated by a continuous functional which is negative on `d₁` and positive on `d₂`; it can be
chosen nonzero at any vector `u` on which some functional `ℓ₀` takes the value `1`. -/
theorem exists_strongDual_neg_pos_ne_zero {d₁ d₂ : E} (h : (0 : E) ∉ segment ℝ (-d₁) d₂)
    (ℓ₀ : StrongDual ℝ E) {u : E} (hu : ℓ₀ u = 1) :
    ∃ ℓ : StrongDual ℝ E, ℓ d₁ < 0 ∧ 0 < ℓ d₂ ∧ ℓ u ≠ 0 := by
  have hclosed : IsClosed (segment ℝ (-d₁) d₂) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  obtain ⟨f, c, hf0, hfc⟩ := geometric_hahn_banach_point_closed (convex_segment _ _) hclosed h
  have h₁ : c < -f d₁ := by simpa using hfc _ (left_mem_segment ℝ _ _)
  have h₂ : c < f d₂ := hfc _ (right_mem_segment ℝ _ _)
  rw [map_zero] at hf0
  by_cases hfu : f u = 0
  · -- Perturb `f` by a small multiple of `ℓ₀`, small enough to keep both signs.
    set ε := c / (|ℓ₀ d₁| + |ℓ₀ d₂| + 1) with hε
    have hpos : 0 < |ℓ₀ d₁| + |ℓ₀ d₂| + 1 := by positivity
    have hεpos : 0 < ε := div_pos hf0 hpos
    have hεc : ε * (|ℓ₀ d₁| + |ℓ₀ d₂| + 1) = c := div_mul_cancel₀ _ hpos.ne'
    refine ⟨f + ε • ℓ₀, ?_, ?_, ?_⟩
    · simp only [add_apply, smul_apply, smul_eq_mul]
      nlinarith [le_abs_self (ℓ₀ d₁), abs_nonneg (ℓ₀ d₂)]
    · simp only [add_apply, smul_apply, smul_eq_mul]
      nlinarith [neg_abs_le (ℓ₀ d₂), abs_nonneg (ℓ₀ d₁)]
    · simp [hfu, hu, hεpos.ne']
  · exact ⟨f, by linarith, by linarith, hfu⟩

end TauCeti
