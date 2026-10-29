/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.BoundaryChain.Basic
public import TauCeti.Analysis.Green.WindingWeight.Basic
public import Mathlib.Analysis.Convex.Segment
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Trace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import TauCeti.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Polygonal boundaries and triangle fans

Triangle boundaries are actual three-edge raw curves. Their signed path chains use the two forward
edges and the negative of the diagonal, so radial edges cancel in a triangle fan. This convention
agrees with traversing the third edge backwards and makes the cancellation a literal chain identity.
-/

public section

noncomputable section

open Set MeasureTheory

namespace TauCeti.Green

/-- The boundary of the triangle with ordered vertices `c`, `p`, `q`, traversed on `[0,3]`. -/
def triangleCurve (c p q : ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 then c + t • (p - c)
  else if t ≤ 2 then p + (t - 1) • (q - p) else q + (t - 2) • (c - q)

/-- The first edge of the triangle boundary. -/
theorem triangleCurve_eq_first (c p q : ℂ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    triangleCurve c p q t = c + t • (p - c) := ite_eq_left ht.2

/-- The second edge of the triangle boundary, including its two vertices. -/
theorem triangleCurve_eq_second (c p q : ℂ) {t : ℝ} (ht : t ∈ Icc 1 2) :
    triangleCurve c p q t = p + (t - 1) • (q - p) := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    simp [triangleCurve]
  · simp [triangleCurve, not_le.mpr h, ht.2]

/-- The third edge of the triangle boundary, including its two vertices. -/
theorem triangleCurve_eq_third (c p q : ℂ) {t : ℝ} (ht : t ∈ Icc 2 3) :
    triangleCurve c p q t = q + (t - 2) • (c - q) := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    norm_num [triangleCurve]
  · simp [triangleCurve, not_le.mpr (by linarith : 1 < t), not_le.mpr h]

@[simp]
theorem triangleCurve_zero (c p q : ℂ) : triangleCurve c p q 0 = c := by
  simp [triangleCurve]

@[simp]
theorem triangleCurve_three (c p q : ℂ) : triangleCurve c p q 3 = c := by
  norm_num [triangleCurve]

/-- Every triangle boundary, including a degenerate one, is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_triangleCurve (c p q : ℂ) :
    AbsolutelyContinuousOnInterval (triangleCurve c p q) 0 3 := by
  have hedge (x y : ℂ) (r : ℝ) (a b : ℝ) :
      AbsolutelyContinuousOnInterval (fun t : ℝ ↦ x + (t - r) • (y - x)) a b :=
    by
      have h : ContDiffOn ℝ 1 (fun t : ℝ ↦ x + (t - r) • (y - x)) (uIcc a b) := by fun_prop
      exact h.absolutelyContinuousOnInterval
  have h₁ : AbsolutelyContinuousOnInterval (triangleCurve c p q) 0 1 :=
    (hedge c p 0 0 1).congr fun t ht ↦ by
      simpa only [sub_zero] using triangleCurve_eq_first c p q
        (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht) |>.symm
  have h₂ : AbsolutelyContinuousOnInterval (triangleCurve c p q) 1 2 :=
    (hedge p q 1 1 2).congr fun t ht ↦ (triangleCurve_eq_second c p q
      (by simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using ht)).symm
  have h₃ : AbsolutelyContinuousOnInterval (triangleCurve c p q) 2 3 :=
    (hedge q c 2 2 3).congr fun t ht ↦ (triangleCurve_eq_third c p q
      (by simpa only [uIcc_of_le (by norm_num : (2 : ℝ) ≤ 3)] using ht)).symm
  exact (h₁.trans h₂).trans h₃

/-- The trace of the triangle boundary is exactly its three closed edges. -/
theorem image_triangleCurve (c p q : ℂ) :
    triangleCurve c p q '' Icc 0 3 = segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c := by
  simp only [segment_eq_image']
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    by_cases ht₁ : t ≤ 1
    · exact Or.inl (Or.inl ⟨t, ⟨ht.1, ht₁⟩, (triangleCurve_eq_first c p q ⟨ht.1, ht₁⟩).symm⟩)
    by_cases ht₂ : t ≤ 2
    · exact Or.inl (Or.inr ⟨t - 1, ⟨by linarith, by linarith⟩,
        (triangleCurve_eq_second c p q ⟨by linarith, ht₂⟩).symm⟩)
    · exact Or.inr ⟨t - 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        (triangleCurve_eq_third c p q ⟨by linarith, ht.2⟩).symm⟩
  · rintro z ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩)
    · exact ⟨t, ⟨ht.1, ht.2.trans (by norm_num)⟩, triangleCurve_eq_first c p q ht⟩
    · refine ⟨t + 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      have hsecond : t + 1 ∈ Icc (1 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simpa only [add_sub_cancel_right] using triangleCurve_eq_second c p q hsecond
    · refine ⟨t + 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      have hthird : t + 2 ∈ Icc (2 : ℝ) 3 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simpa only [add_sub_cancel_right] using triangleCurve_eq_third c p q hthird

/-- The three triangle edges have planar area zero, without a nondegeneracy assumption. -/
theorem volume_triangle_edges (c p q : ℂ) :
    volume (segment ℝ c p ∪ segment ℝ p q ∪ segment ℝ q c) = 0 := by
  rw [← image_triangleCurve]
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)] using
    (absolutelyContinuousOnInterval_triangleCurve c p q).addHaar_image_uIcc_eq_zero volume
      (by norm_num [Complex.finrank_real_complex])

namespace BoundaryChain

/-- The signed chain around a triangle: two forward edges and the negative diagonal. -/
def triangle (c p q : ℂ) : BoundaryChain :=
  ofPath (Path.segment c p) + ofPath (Path.segment p q) - ofPath (Path.segment c q)

/-- The path generators of the signed triangle boundary. -/
theorem triangle_def (c p q : ℂ) : triangle c p q =
    ofPath (Path.segment c p) + ofPath (Path.segment p q) - ofPath (Path.segment c q) := (rfl)

@[simp]
theorem boundary_triangle (c p q : ℂ) : boundary (triangle c p q) = 0 := by
  simp only [triangle, map_sub, map_add, boundary_ofPath]
  abel

/-- The chain of successive segments through a finite vertex sequence. -/
def polygon {N : ℕ} (v : Fin (N + 1) → ℂ) : BoundaryChain :=
  ∑ i : Fin N, ofPath (Path.segment (v i.castSucc) (v i.succ))

/-- The path generators of a polygonal chain. -/
theorem polygon_def {N : ℕ} (v : Fin (N + 1) → ℂ) : polygon v =
    ∑ i : Fin N, ofPath (Path.segment (v i.castSucc) (v i.succ)) := (rfl)

/-- The endpoint boundary of the successive-edge chain telescopes. -/
theorem boundary_polygon {N : ℕ} (v : Fin (N + 1) → ℂ) :
    boundary (polygon v) = Finsupp.single (v (Fin.last N)) 1 - Finsupp.single (v 0) 1 := by
  simp only [polygon, map_sum, boundary_ofPath]
  exact Fin.sum_univ_succ_sub_castSucc (fun j ↦ Finsupp.single (v j) (1 : ℤ))

/-- A triangle fan differs from the polygonal chain only by its two outer radial segments. -/
theorem sum_triangle {N : ℕ} (v : Fin (N + 1) → ℂ) (c : ℂ) :
    (∑ i : Fin N, triangle c (v i.castSucc) (v i.succ)) = polygon v +
      ofPath (Path.segment c (v 0)) - ofPath (Path.segment c (v (Fin.last N))) := by
  simp only [triangle]
  have he (i : Fin N) : ofPath (Path.segment c (v i.castSucc)) +
      ofPath (Path.segment (v i.castSucc) (v i.succ)) - ofPath (Path.segment c (v i.succ)) =
      ofPath (Path.segment (v i.castSucc) (v i.succ)) +
        (ofPath (Path.segment c (v i.castSucc)) - ofPath (Path.segment c (v i.succ))) := by abel
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have htel : (∑ i : Fin N, (ofPath (Path.segment c (v i.castSucc)) -
      ofPath (Path.segment c (v i.succ)))) =
      ofPath (Path.segment c (v 0)) - ofPath (Path.segment c (v (Fin.last N))) := by
    exact Fin.sum_univ_castSucc_sub_succ (fun i ↦ ofPath (Path.segment c (v i)))
  rw [htel]
  simp only [polygon]
  abel

/-- For a closed vertex sequence, the fan boundary is literally the polygon boundary chain. -/
theorem sum_triangle_of_closed {N : ℕ} (v : Fin (N + 1) → ℂ)
    (hv : v (Fin.last N) = v 0) (c : ℂ) :
    (∑ i : Fin N, triangle c (v i.castSucc) (v i.succ)) = polygon v := by
  rw [sum_triangle, hv]
  abel

end BoundaryChain

end TauCeti.Green
