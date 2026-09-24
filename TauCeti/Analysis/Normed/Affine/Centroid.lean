/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-!
# Distances to the centroid of finitely many points

For a nonempty finite family of points `p i`, `i ∈ s`, in a pseudometric affine space over a
real seminormed space, whose pairwise distances are at most `d`, the centroid `s.centroid ℝ p`
lies within `(1 - 1 / #s) * d` of each point `p j`, `j ∈ s`. More precisely, the centroid of a
nonempty subfamily `t ⊆ s` lies within `(1 - #t / #s) * d` of the whole family’s centroid.
These are the estimates behind the shrinking of barycentric subdivision: the vertices of a
simplex of the barycentric subdivision of a `k`-simplex of diameter `d` are centroids of nested
faces, hence lie within `k / (k + 1) * d` of each other.

## Main results

* `Finset.dist_centroid_le_sum_dist`: distance to the centroid is bounded by the average distance.
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

variable {ι : Type*} {s t : Finset ι}

variable {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]
  [NormedAddTorsor V P] {p : ι → P}

/-- Distance to the centroid is at most the average distance to the points. -/
theorem dist_centroid_le_sum_dist (hs : s.Nonempty) (q : P) :
    dist (s.centroid ℝ p) q ≤ (#s : ℝ)⁻¹ * ∑ i ∈ s, dist (p i) q := by
  rw [dist_eq_norm_vsub V, centroid_def,
    ← s.sum_smul_vsub_const_eq_affineCombination_vsub _ _ _
      (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  calc
    _ ≤ ∑ i ∈ s, ‖s.centroidWeights ℝ i • (p i -ᵥ q)‖ := norm_sum_le _ _
    _ = (#s : ℝ)⁻¹ * ∑ i ∈ s, dist (p i) q := by
      simp [norm_smul, dist_eq_norm_vsub V, ← mul_sum]

/-- The centroid of a nonempty family of points lies in every closed ball containing all of
them. -/
theorem dist_centroid_le (hs : s.Nonempty) {q : P} {r : ℝ} (h : ∀ i ∈ s, dist (p i) q ≤ r) :
    dist (s.centroid ℝ p) q ≤ r := by
  refine (dist_centroid_le_sum_dist hs q).trans ?_
  calc
    _ ≤ (#s : ℝ)⁻¹ * (#s * r) := by
      gcongr
      simpa using sum_le_card_nsmul s (fun i => dist (p i) q) r h
    _ = r := by
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hs.card_pos.ne'), one_mul]

/-- If the cross-distances between a family and a nonempty subfamily are at most `d`, the
centroids are at distance at most `(1 - #t / #s) * d`. In particular, the bound is zero when
the two index sets agree. -/
theorem dist_centroid_centroid_le_of_subset {d : ℝ}
    (hd : ∀ i ∈ s, ∀ j ∈ t, dist (p i) (p j) ≤ d) (hts : t ⊆ s) (ht : t.Nonempty) :
    dist (t.centroid ℝ p) (s.centroid ℝ p) ≤ (1 - (#t : ℝ) / #s) * d := by
  classical
  have hs := ht.mono hts
  have hcard : (#s : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  -- The displacements within the smaller family sum to zero at its own centroid.
  have htzero : ∑ i ∈ t, (p i -ᵥ t.centroid ℝ p) = 0 := by
    have h := t.sum_smul_vsub_const_eq_affineCombination_vsub
      (t.centroidWeights ℝ) p (t.centroid ℝ p)
      (t.sum_centroidWeights_eq_one_of_nonempty ℝ ht)
    rw [← centroid_def, vsub_self] at h
    simp only [centroidWeights_apply, ← smul_sum] at h
    exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero (by exact_mod_cast ht.card_pos.ne'))
  have hdist : ∀ i ∈ s, dist (p i) (t.centroid ℝ p) ≤ d := fun i hi => by
    rw [dist_comm]
    exact dist_centroid_le ht fun j hj => by simpa [dist_comm] using hd i hi j hj
  calc
    dist (t.centroid ℝ p) (s.centroid ℝ p)
        = ‖(#s : ℝ)⁻¹ • ∑ i ∈ s \ t, (p i -ᵥ t.centroid ℝ p)‖ := by
      rw [dist_comm, dist_eq_norm_vsub V, centroid_def,
        ← s.sum_smul_vsub_const_eq_affineCombination_vsub _ _ _
          (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
      simp only [centroidWeights_apply, ← smul_sum, ← sum_sdiff hts, htzero, smul_zero, add_zero]
    _ ≤ (#s : ℝ)⁻¹ * ∑ i ∈ s \ t, dist (p i) (t.centroid ℝ p) := by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      simp_rw [dist_eq_norm_vsub V]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (#s : ℝ)⁻¹ * (#(s \ t) * d) := by
      gcongr
      simpa using sum_le_card_nsmul (s \ t) (fun i => dist (p i) (t.centroid ℝ p)) d
        (fun i hi => hdist i (mem_sdiff.mp hi).1)
    _ = (1 - (#t : ℝ) / #s) * d := by
      rw [card_sdiff_of_subset hts, Nat.cast_sub (card_le_card hts)]
      field_simp

/-- If `j ∈ s` and the points `p i`, `i ∈ s`, are at distance at most `d` from `p j`, then the
centroid lies within `(1 - 1 / #s) * d` of `p j`. -/
theorem dist_centroid_apply_le {d : ℝ} {j : ι} (hd : ∀ i ∈ s, dist (p i) (p j) ≤ d)
    (hj : j ∈ s) : dist (s.centroid ℝ p) (p j) ≤ (1 - (#s : ℝ)⁻¹) * d := by
  have h := dist_centroid_centroid_le_of_subset (t := {j})
    (fun i hi k hk => by simpa only [mem_singleton.mp hk] using hd i hi)
    (singleton_subset_iff.mpr hj) (singleton_nonempty j)
  simpa [dist_comm] using h

end Finset
