/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Ball
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Star.Basic

/-!
# Boundary vertex coordinates for the standard simplex

The open star of a boundary vertex is the local model needed for a combinatorial ball chart.
This file records its strict coordinate criterion in the standard simplex and proves openness of
the corresponding subset of the coordinate simplex.

Dropping the last barycentric coordinate turns positivity of that coordinate into the strict
inequality that the sum of the remaining coordinates is less than one.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to PL Topology*, Springer (1972),
Chapters 1–2 (polyhedral local models).
-/

public section

open Set TauCeti

namespace AbstractSimplicialComplex

/-- In the standard simplex, the open star of the last vertex is described in the dropped
barycentric coordinates by the strict sum inequality. -/
theorem mem_standardSimplexOpenStar_iff_sum_lt_one (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))) :
    x ∈ openStarRealization (⊤ : AbstractSimplicialComplex (Fin (n + 1)))
      (Fin.last n) ↔
      ∑ i : Fin n, (realizationTopHomeomorphCoordinateSimplex n x).1 i < 1 := by
  let c := realizationTopHomeomorphCoordinateSimplex n
  have h := realizationTopHomeomorphCoordinateSimplex_symm_last n (c x)
  rw [c.symm_apply_apply] at h
  rw [mem_openStarRealization, h, sub_pos]

end AbstractSimplicialComplex

namespace TauCeti

/-- The points of `coordinateSimplex (Fin n)` whose coordinate sum is less than one form an
open set. Under `realizationTopHomeomorphCoordinateSimplex`, these are exactly the points in the
open star of the last vertex of the standard `(n + 1)`-simplex. -/
theorem isOpen_coordinateSimplexOpenStar (n : ℕ) :
    IsOpen {y : coordinateSimplex (Fin n) | ∑ i : Fin n, y.1 i < 1} := by
  exact isOpen_lt
    (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_subtype_val)
    continuous_const

end TauCeti
