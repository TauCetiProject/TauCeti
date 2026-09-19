/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-!
# Distances to the centroid of finitely many points

For a nonempty finite family of points `p i`, `i ∈ s`, of a real normed affine space whose
pairwise distances are at most `d`, the centroid `s.centroid ℝ p` lies within
`(1 - 1 / #s) * d` of each point `p j`, `j ∈ s`, and of the centroid of every nonempty subfamily.
These are the estimates behind the shrinking of barycentric subdivision: the vertices of a
simplex of the barycentric subdivision of a `k`-simplex of diameter `d` are centroids of nested
faces, hence lie within `k / (k + 1) * d` of each other.

## Main results

* `Finset.dist_centroid_le`: the centroid lies in every closed ball containing the points.
* `Finset.dist_centroid_apply_le`: the distance from the centroid to one of the points.
* `Finset.dist_centroid_centroid_le_of_subset`: the distance between the centroids of a family
  and of a nonempty subfamily.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, proof of Proposition 2.21, step (2).
-/

public section

open Finset Metric

namespace Finset

variable {ι V P : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] {s t : Finset ι} {p : ι → P}

/-- The displacement of the centroid from a point `q` is the average of the displacements of
the points from `q`. -/
private lemma centroid_vsub_eq_sum (hs : s.Nonempty) (q : P) :
    s.centroid ℝ p -ᵥ q = ∑ i ∈ s, (#s : ℝ)⁻¹ • (p i -ᵥ q) := by
  rw [s.centroid_vsub_const ℝ hs, centroid_def, affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp [centroidWeights_apply]

/-- The centroid of a nonempty family of points lies in every closed ball containing all of
them. -/
theorem dist_centroid_le (hs : s.Nonempty) {q : P} {r : ℝ} (h : ∀ i ∈ s, dist (p i) q ≤ r) :
    dist (s.centroid ℝ p) q ≤ r := by
  rw [dist_eq_norm_vsub V, ← mem_closedBall_zero_iff, centroid_vsub_eq_sum hs]
  refine (convex_closedBall 0 r).sum_mem (fun _ _ ↦ by positivity) ?_ fun i hi ↦ ?_
  · rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ (by exact_mod_cast hs.card_pos.ne')]
  · rw [mem_closedBall_zero_iff, ← dist_eq_norm_vsub V]
    exact h i hi

/-- If the points `p i`, `i ∈ s`, are pairwise at distance at most `d`, then the centroid lies
within `(1 - 1 / #s) * d` of each of them. -/
theorem dist_centroid_apply_le {d : ℝ} (hd : ∀ i ∈ s, ∀ j ∈ s, dist (p i) (p j) ≤ d) {j : ι}
    (hj : j ∈ s) : dist (s.centroid ℝ p) (p j) ≤ (1 - (#s : ℝ)⁻¹) * d := by
  have hcard : (#s : ℝ) ≠ 0 := by exact_mod_cast (card_pos.2 ⟨j, hj⟩).ne'
  -- The term of `p j` itself vanishes, so only `#s - 1` distances contribute.
  have hsum : ∑ i ∈ s, dist (p i) (p j) ≤ (#s - 1 : ℝ) * d := by
    classical
    rw [← sum_erase (f := fun i ↦ dist (p i) (p j)) s (dist_self (p j))]
    refine (sum_le_card_nsmul _ _ d fun i hi ↦ hd i (mem_of_mem_erase hi) j hj).trans_eq ?_
    rw [card_erase_of_mem hj, nsmul_eq_mul, Nat.cast_sub (card_pos.2 ⟨j, hj⟩), Nat.cast_one]
  calc dist (s.centroid ℝ p) (p j)
      = ‖∑ i ∈ s, (#s : ℝ)⁻¹ • (p i -ᵥ p j)‖ := by
        rw [dist_eq_norm_vsub V, centroid_vsub_eq_sum ⟨j, hj⟩]
    _ ≤ ∑ i ∈ s, (#s : ℝ)⁻¹ * dist (p i) (p j) := by
        refine (norm_sum_le _ _).trans_eq (sum_congr rfl fun i _ ↦ ?_)
        rw [norm_smul, Real.norm_of_nonneg (by positivity), dist_eq_norm_vsub V]
    _ ≤ (#s : ℝ)⁻¹ * ((#s - 1 : ℝ) * d) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 - (#s : ℝ)⁻¹) * d := by
        field_simp

/-- If the points `p i`, `i ∈ s`, are pairwise at distance at most `d`, then the centroid of a
nonempty subfamily lies within `(1 - 1 / #s) * d` of the centroid of the whole family. -/
theorem dist_centroid_centroid_le_of_subset {d : ℝ}
    (hd : ∀ i ∈ s, ∀ j ∈ s, dist (p i) (p j) ≤ d) (hts : t ⊆ s) (ht : t.Nonempty) :
    dist (t.centroid ℝ p) (s.centroid ℝ p) ≤ (1 - (#s : ℝ)⁻¹) * d :=
  dist_centroid_le ht fun i hi ↦ dist_comm (p i) _ ▸ dist_centroid_apply_le hd (hts hi)

end Finset
