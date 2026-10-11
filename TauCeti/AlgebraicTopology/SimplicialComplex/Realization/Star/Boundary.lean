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
the corresponding subset of the solid orthant.

Dropping the apex barycentric coordinate turns positivity of that coordinate into the strict
inequality that the sum of the remaining coordinates is less than one. Constructing the resulting
homeomorphism and transporting this model to general combinatorial balls remain later steps.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to PL Topology*, Springer (1972),
Chapters 1–2 (polyhedral local models).
-/

public section

open Set TauCeti

namespace AbstractSimplicialComplex

/-- The standard orthant chart target is open in the solid orthant. -/
theorem isOpen_standardSimplexOpenStarChartTarget (n : ℕ) :
    IsOpen {q : Set.Ici (0 : (Fin n → ℝ) × ℝ) |
      (∑ i : Fin n, q.1.1 i) + q.1.2 < 1} := by
  have hs : Continuous (fun q : Set.Ici (0 : (Fin n → ℝ) × ℝ) =>
      ∑ i : Fin n, q.1.1 i + q.1.2) := by fun_prop
  exact isOpen_lt hs continuous_const

/-- In the standard simplex, the open star of the last vertex is described in the dropped
barycentric coordinates by the strict sum inequality. -/
theorem mem_standardSimplexOpenStar_iff_sum_lt_one (n : ℕ)
    (x : Realization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))) :
    x ∈ openStarRealization (⊤ : AbstractSimplicialComplex (Fin (n + 2)))
      (Fin.last (n + 1)) ↔
      ∑ i : Fin (n + 1),
        (realizationTopHomeomorphCoordinateSimplex (n + 1) x).1 i < 1 := by
  let c := realizationTopHomeomorphCoordinateSimplex (n + 1)
  have h := realizationTopHomeomorphCoordinateSimplex_symm_last (n + 1) (c x)
  rw [c.symm_apply_apply] at h
  rw [mem_openStarRealization, h, sub_pos]

end AbstractSimplicialComplex
