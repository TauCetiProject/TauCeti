/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# The centroid is an algebraic relative interior point

Over a linearly ordered field there is no topology to speak of relative interiors, but the
centroid of a nonempty finite set `s` still behaves like a relative interior point of the convex
hull of `s`: for every point `p` of the affine span of `s`, the point slightly beyond the centroid
on the ray from `p` remains in the convex hull (`Finset.exists_lineMap_centroid_mem_convexHull`).

This is what makes a point outside a "visible" set lie off the affine span of every simplex in it,
as used for cones of geometric simplicial complexes.
-/

public section

open Finset

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

namespace Finset

/-- For every point `p` in the affine span of a nonempty finite set `s`, some point strictly beyond
the centroid of `s` on the ray from `p` still lies in the convex hull of `s`. -/
theorem exists_lineMap_centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) {p : E}
    (hp : p ∈ affineSpan 𝕜 (s : Set E)) :
    ∃ ε : 𝕜, 0 < ε ∧ AffineMap.lineMap p (s.centroid 𝕜 id) (1 + ε) ∈ convexHull 𝕜 (s : Set E) := by
  classical
  have hrange : (s : Set E) = Set.range ((↑) : s → E) := by simp
  rw [hrange] at hp
  obtain ⟨w, hw, hpw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  rw [affineCombination_eq_linear_combination _ _ _ hw] at hpw
  set n : 𝕜 := (#s : 𝕜)
  have hn : 0 < n := Nat.cast_pos.2 hs.card_pos
  have hc : s.centroid 𝕜 id = ∑ i : s, n⁻¹ • (i : E) := by
    rw [centroid_def, affineCombination_eq_linear_combination _ _ _
      (sum_centroidWeights_eq_one_of_nonempty 𝕜 _ hs)]
    simp only [centroidWeights_apply, id]
    exact (sum_coe_sort s fun i => n⁻¹ • i).symm
  -- `ε` is small enough that pushing past the centroid keeps every weight nonnegative
  set M : 𝕜 := ∑ i : s, |w i|
  have hM : 0 ≤ M := sum_nonneg fun i _ => abs_nonneg (w i)
  set ε : 𝕜 := (n * (M + 1))⁻¹
  have hε : 0 < ε := inv_pos.2 (mul_pos hn (by linarith))
  set μ : s → 𝕜 := fun i => (1 + ε) * n⁻¹ - ε * w i
  have hμ : ∀ i, 0 ≤ μ i := by
    intro i
    have hwi : ε * w i ≤ n⁻¹ := by
      calc ε * w i ≤ ε * M :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans
              (single_le_sum (f := fun i : s => |w i|) (fun i _ => abs_nonneg _) (mem_univ i)))
              hε.le
        _ ≤ ε * (M + 1) := by nlinarith
        _ = n⁻¹ := by
            simp only [ε, mul_inv]
            field_simp
    have : 0 ≤ ε * n⁻¹ := (mul_pos hε (inv_pos.2 hn)).le
    simp only [μ]
    nlinarith
  have hμsum : ∑ i : s, μ i = 1 := by
    simp only [μ, sum_sub_distrib, ← mul_sum, hw, sum_const, card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    field_simp
    ring
  refine ⟨ε, hε, ?_⟩
  have hq : AffineMap.lineMap p (s.centroid 𝕜 id) (1 + ε) = ∑ i : s, μ i • (i : E) := by
    rw [AffineMap.lineMap_apply_module', hc, hpw]
    simp only [μ, sub_smul, sum_sub_distrib, ← smul_sum, mul_smul]
    module
  rw [hq]
  exact (convex_convexHull 𝕜 _).sum_mem (fun i _ => hμ i) hμsum fun i _ => subset_convexHull 𝕜 _ i.2

end Finset
