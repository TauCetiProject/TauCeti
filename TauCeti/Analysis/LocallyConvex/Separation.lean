/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Affine
import Mathlib.Tactic.Positivity

/-!
# Separation by functionals

Two vectors `d₁` and `d₂` of a real locally convex Hausdorff space with `0 ∉ [-d₁, d₂]`, that is,
both nonzero and not on a common ray from `0`, are separated by a continuous functional `ℓ` with
`ℓ d₁ < 0 < ℓ d₂`. This is the geometric Hahn--Banach theorem
`geometric_hahn_banach_point_closed` applied to the point `0` and the segment `[-d₁, d₂]`. Both
strict inequalities are open conditions, so `ℓ` can moreover be perturbed to be nonzero at any
prescribed vector on which some functional does not vanish.

In a real Hilbert space, the geometric Hahn--Banach theorem `geometric_hahn_banach_closed_point`
together with the Riesz representation shows that a nonempty closed convex set is determined by
its supporting half-spaces in unit directions.

## Main results

* `TauCeti.exists_strongDual_neg_pos_ne_zero`: a functional negative on `d₁`, positive on `d₂`,
  and nonzero at a prescribed vector `u`.
* `Convex.subset_of_forall_upperBounds_image_inner_subset`: if every supporting half-space of a
  nonempty closed convex set `S` in a unit direction contains `T`, then `T ⊆ S`.
-/

public section

open Set
open scoped RealInnerProductSpace

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
    set ε := c / (|ℓ₀ d₁| + |ℓ₀ d₂| + 1) with _
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

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Supporting half-spaces determine a closed convex set.** If every upper bound of the heights
`⟪e, x⟫` over a nonempty closed convex set `S`, in a unit direction `e`, also bounds the heights
over `T`, then `T ⊆ S`. -/
theorem Convex.subset_of_forall_upperBounds_image_inner_subset [CompleteSpace E] {S T : Set E}
    (hS : Convex ℝ S) (hSc : IsClosed S) (hSne : S.Nonempty)
    (h : ∀ e : E, ‖e‖ = 1 → upperBounds ((⟪e, ·⟫) '' S) ⊆ upperBounds ((⟪e, ·⟫) '' T)) :
    T ⊆ S := by
  intro x hx
  by_contra hxS
  obtain ⟨f, u, hfS, hfx⟩ := geometric_hahn_banach_closed_point hS hSc hxS
  set w := (InnerProductSpace.toDual ℝ E).symm f
  have hw (y : E) : f y = ⟪w, y⟫ := InnerProductSpace.toDual_symm_apply.symm
  obtain ⟨a, ha⟩ := hSne
  have hw0 : w ≠ 0 := by
    rintro hw0
    have h₁ := hfS a ha
    rw [hw, hw0, inner_zero_left] at h₁ hfx
    linarith
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  -- The unit normal `‖w‖⁻¹ • w` bounds the heights over `S` by `‖w‖⁻¹ * u` but not at `x`.
  have hub : ‖w‖⁻¹ * u ∈ upperBounds ((⟪‖w‖⁻¹ • w, ·⟫) '' S) := by
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    rw [real_inner_smul_left, ← hw]
    exact mul_le_mul_of_nonneg_left (hfS y hy).le (inv_nonneg.2 hwpos.le)
  have hunit : ‖‖w‖⁻¹ • w‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwpos.ne']
  have hx' := h _ hunit hub ⟨x, hx, rfl⟩
  dsimp only at hx'
  rw [real_inner_smul_left, ← hw] at hx'
  have := le_of_mul_le_mul_left hx' (inv_pos.2 hwpos)
  linarith

end InnerProductSpace
