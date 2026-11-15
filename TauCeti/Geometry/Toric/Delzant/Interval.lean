/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Basic

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.RingTheory.Ideal.Span

/-!
# The interval as a Delzant polytope

The moment polytope of the rotation action of the circle on the two-sphere is an interval. On the
real line with its integral lattice `ℤ` (`Int.castAddHom ℝ`), the inward normals `1` and `-1` with
support constants `0` and `-a` cut out the polyhedron

`{x ∈ ℝ* | 0 ≤ x 1 ≤ a}`

(`TauCeti.Toric.mem_facetPolyhedron_interval_iff`). For `a > 0` this is a Delzant polytope
(`TauCeti.Toric.isDelzant_interval`): it is bounded, and at each of its two vertices exactly one
normal `±1` is active, which is a basis of `ℤ`. The interior points have no active constraint
and are not vertices.

## Main results

* `TauCeti.Toric.mem_facetPolyhedron_interval_iff`: the polyhedron is the interval `[0, a]`.
* `TauCeti.Toric.isDelzant_interval`: for `a > 0` it is a Delzant polytope.
-/

public section

open Set

namespace TauCeti.Toric

variable {a : ℝ}

/-- The polyhedron cut out by the normals `1, -1` with support constants `0, -a` is the interval
`[0, a]`, read through the value of a functional at `1`. -/
theorem mem_facetPolyhedron_interval_iff {x : StrongDual ℝ ℝ} :
    x ∈ facetPolyhedron (Int.castAddHom ℝ) ![1, -1] ![0, -a] ↔ x 1 ∈ Icc 0 a := by
  simp [Fin.forall_fin_two]

/-- At a point where only one constraint is active, the active normal `±1` is a basis of `ℤ`. -/
private theorem isSmoothVertex_interval_of_activeSet_eq {x : StrongDual ℝ ℝ} {j : Fin 2}
    (hx : activeSet (facetPairing (Int.castAddHom ℝ) ![1, -1]) ![0, -a] x = {j}) :
    IsSmoothVertex (Int.castAddHom ℝ) ![1, -1] ![0, -a] x := by
  rw [isSmoothVertex_iff_linearIndepOn, hx, linearIndepOn_singleton_iff, image_singleton]
  fin_cases j
  · exact ⟨by simp, Ideal.span_singleton_eq_top.2 (by simp)⟩
  · exact ⟨by simp, Ideal.span_singleton_eq_top.2 (by simp)⟩

/-- The active constraints at a point of the line. -/
private theorem mem_activeSet_interval_iff {x : StrongDual ℝ ℝ} {j : Fin 2} :
    j ∈ activeSet (facetPairing (Int.castAddHom ℝ) ![1, -1]) ![0, -a] x ↔
      (j = 0 ∧ x 1 = 0) ∨ (j = 1 ∧ x 1 = a) := by
  fin_cases j <;> simp

private theorem activeSet_interval_of_eq_zero (ha : a ≠ 0) {x : StrongDual ℝ ℝ} (hx : x 1 = 0) :
    activeSet (facetPairing (Int.castAddHom ℝ) ![1, -1]) ![0, -a] x = {0} := by
  ext j
  rw [mem_activeSet_interval_iff, mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact absurd (h.2.symm.trans hx) ha
  · exact fun hj ↦ Or.inl ⟨hj, hx⟩

private theorem activeSet_interval_of_eq (ha : a ≠ 0) {x : StrongDual ℝ ℝ} (hx : x 1 = a) :
    activeSet (facetPairing (Int.castAddHom ℝ) ![1, -1]) ![0, -a] x = {1} := by
  ext j
  rw [mem_activeSet_interval_iff, mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact absurd (hx.symm.trans h.2) ha
    · exact h.1
  · exact fun hj ↦ Or.inr ⟨hj, hx⟩

/-- **The interval is a Delzant polytope.** For `a > 0`, the interval `[0, a]` cut out by the
normals `1, -1` of the integral lattice `ℤ ⊂ ℝ` is a Delzant polytope. -/
theorem isDelzant_interval (ha : 0 < a) :
    IsDelzant (Int.castAddHom ℝ) ![1, -1] ![0, -a] := by
  refine ⟨?_, fun x hx ↦ ?_, fun j ↦ ?_⟩
  · -- Every point of the interval has norm at most `a`.
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨a, fun x hx ↦ ?_⟩
    have hx' := mem_facetPolyhedron_interval_iff.1 hx
    rw [Metric.mem_closedBall, dist_zero_right]
    refine ContinuousLinearMap.opNorm_le_bound x ha.le fun y ↦ ?_
    have hy : x y = y * x 1 := by simpa using x.map_smul y 1
    rw [hy, norm_mul, Real.norm_of_nonneg hx'.1, mul_comm]
    exact mul_le_mul_of_nonneg_right hx'.2 (norm_nonneg y)
  · -- A vertex is an endpoint: otherwise no constraint is active and `x` is not extreme.
    obtain ⟨-, hker⟩ := mem_extremePoints_facetPolyhedron_iff.1 hx
    by_cases h₀ : x 1 = 0
    · exact isSmoothVertex_interval_of_activeSet_eq (activeSet_interval_of_eq_zero ha.ne' h₀)
    by_cases h₁ : x 1 = a
    · exact isSmoothVertex_interval_of_activeSet_eq (activeSet_interval_of_eq ha.ne' h₁)
    refine absurd (hker (ContinuousLinearMap.id ℝ ℝ) fun j hj ↦ ?_) (ne_zero_of_eq_one rfl)
    rcases mem_activeSet_interval_iff.1 hj with h | h
    · exact absurd h.2 h₀
    · exact absurd h.2 h₁
  · fin_cases j
    · exact ⟨0, mem_facetPolyhedron_interval_iff.2 ⟨le_rfl, ha.le⟩,
        activeSet_interval_of_eq_zero ha.ne' rfl⟩
    · refine ⟨a • ContinuousLinearMap.id ℝ ℝ, mem_facetPolyhedron_interval_iff.2 ?_,
        activeSet_interval_of_eq ha.ne' ?_⟩ <;> simp [ha.le]

end TauCeti.Toric
