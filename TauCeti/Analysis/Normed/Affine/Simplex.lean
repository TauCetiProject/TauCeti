/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FinCases

/-!
# Distances between the vertices of a triangle

The three sides of a triangle bound all the distances between its vertices: if the vertices are
`x`, `y`, `z` and the sides `dist x y`, `dist x z`, `dist y z` are at most `δ ≥ 0`, then
`dist (t.points k) (t.points l) ≤ δ` for all indices `k` and `l`
(`Affine.Triangle.dist_points_le`). Bounds of this form, quantified over all pairs of vertices,
measure the size of a triangle without singling out a side.

## Main results

* `Affine.Triangle.dist_points_le`: a triangle with sides at most `δ ≥ 0` has all distances between
  its vertices at most `δ`.
-/

public section

namespace Affine.Triangle

variable {k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]
  [PseudoMetricSpace P]

/-- A triangle whose three sides have length at most `δ ≥ 0` has all distances between its vertices
at most `δ`. -/
theorem dist_points_le {t : Triangle k P} {x y z : P} (ht : t.points = ![x, y, z]) {δ : ℝ}
    (hδ : 0 ≤ δ) (hxy : dist x y ≤ δ) (hxz : dist x z ≤ δ) (hyz : dist y z ≤ δ) (i j : Fin 3) :
    dist (t.points i) (t.points j) ≤ δ := by
  rw [ht]
  fin_cases i <;> fin_cases j <;>
    first
    | simpa using hδ
    | simpa using hxy
    | simpa using hxz
    | simpa using hyz
    | simpa [dist_comm] using hxy
    | simpa [dist_comm] using hxz
    | simpa [dist_comm] using hyz

end Affine.Triangle
