/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Basic

/-!
# Ideal vertex cycles of a side-paired hyperbolic polygon

The side-pairing successor preserves whether a vertex lies in the upper half-plane or on its
projective boundary. Thus a vertex cycle is entirely finite or entirely ideal. At an ideal
vertex, the cycle transformation fixes the boundary point and the cycle angle sum is zero.
These statements supply the boundary data for the parabolic cycle condition in a polygon
presentation; side-pairing data alone do not imply that an ideal cycle transformation is
parabolic.

## Main results

* `ConvexPolygon.SidePairing.isRight_vertex_of_mem_cycle`: all vertices in a cycle have the
  same type, finite or ideal.
* `ConvexPolygon.SidePairing.cycleMap_smul_eq_self_of_vertex_eq_inr`: an ideal cycle transformation
  fixes its boundary vertex.
* `ConvexPolygon.SidePairing.cycleAngleSum_eq_zero_of_isRight_vertex`: an ideal cycle has zero
  total angle.

## References

Walkden, *Hyperbolic geometry* (MATH32051 lecture notes, Manchester 2019), §§17.1–17.2
(elliptic and parabolic cycles). Beardon, *The Geometry of Discrete Groups*, Chapter 9.
-/

public section

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

variable {n : ℕ} [NeZero n] {P : ConvexPolygon n} (σ : P.SidePairing)

/-- The successor of an ideal vertex is ideal, and the successor of a finite vertex is finite. -/
@[simp]
theorem isRight_vertex_pair_add_one (j : Fin n) :
    (P.vertex (σ.pair j + 1)).isRight = (P.vertex j).isRight := by
  rw [← σ.next_apply, ← σ.map_smul_vertex_eq_next]
  cases P.vertex j <;> simp

/-- Following any number of side pairings preserves whether the vertex is ideal. -/
theorem isRight_vertex_iterate_next (j : Fin n) (m : ℕ) :
    (P.vertex (σ.next^[m] j)).isRight = (P.vertex j).isRight := by
  exact congrFun (Function.iterate_invariant (f := σ.next)
    (g := fun i ↦ (P.vertex i).isRight) (by
      funext i
      simpa only [Function.comp_apply, σ.next_apply] using
        σ.isRight_vertex_pair_add_one i) m) j

/-- Every vertex on a cycle has the same type, finite or ideal, as its starting vertex. -/
theorem isRight_vertex_of_mem_cycle {j i : Fin n} (hi : i ∈ σ.cycle j) :
    (P.vertex i).isRight = (P.vertex j).isRight := by
  obtain ⟨m, rfl⟩ := (σ.mem_cycle_iff j i).mp hi
  exact σ.isRight_vertex_iterate_next j m

/-- The transformation of a full ideal cycle fixes its projective boundary vertex. -/
@[simp]
theorem cycleMap_smul_eq_self_of_vertex_eq_inr {j : Fin n} {c : OnePoint ℝ}
    (hj : P.vertex j = .inr c) : σ.cycleMap j • c = c := by
  have h := σ.cycleMap_smul_vertex j
  rw [hj, Sum.smul_inr, Sum.inr.injEq] at h
  exact h

/-- All angles on the cycle of an ideal vertex vanish, since that cycle consists of ideal
vertices. -/
theorem interiorAngle_eq_zero_of_isRight_vertex_of_mem_cycle {j i : Fin n}
    (hj : (P.vertex j).isRight) (hi : i ∈ σ.cycle j) :
    P.interiorAngle i = 0 := by
  have h : (P.vertex i).isRight := by
    rw [σ.isRight_vertex_of_mem_cycle hi]
    exact hj
  obtain ⟨d, hd⟩ := Sum.isRight_iff.mp h
  exact P.interiorAngle_eq_zero_of_vertex_eq_inr hd

/-- The total angle of an ideal vertex cycle is zero. -/
@[simp]
theorem cycleAngleSum_eq_zero_of_isRight_vertex {j : Fin n}
    (hj : (P.vertex j).isRight) : σ.cycleAngleSum j = 0 := by
  rw [cycleAngleSum_def]
  exact Finset.sum_eq_zero fun i hi ↦
    σ.interiorAngle_eq_zero_of_isRight_vertex_of_mem_cycle hj hi

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
