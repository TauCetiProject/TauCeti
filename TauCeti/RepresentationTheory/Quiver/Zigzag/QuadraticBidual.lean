/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.QuadraticOrthogonal
public import TauCeti.RepresentationTheory.Quiver.Zigzag.QuadraticDual

/-!
# The reverse quadratic relation calculation

For a finite simple graph, the quadratic orthogonal of the signless preprojective relators is
exactly the quadratic zigzag relation space. Consequently the quadratic dual of the signless
presentation has, on the opposite path algebra, precisely the zigzag relators. Together with
`TauCeti.quadraticOrthogonal_quadraticZigzagRelations` this records both directions of the
quadratic relation calculation without identifying the opposite algebra prematurely.

For a connected graph with at least three vertices, the quadratic zigzag relation ideal presents
the strict zigzag algebra. The one- and two-vertex exceptions do not have this quadratic
presentation.

The quadratic dual calculation follows Huerfano--Khovanov, *A category for the adjoint
representation*, Section 3.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]
  [∀ v : V, Fintype (G.neighborSet v)]

/-- **The quadratic orthogonal of the signless preprojective relations is the quadratic zigzag
relation space.** This is the reverse of `quadraticOrthogonal_quadraticZigzagRelations`. -/
theorem quadraticOrthogonal_signlessPreprojectiveRelators :
    quadraticOrthogonal k (DoubledQuiver G)
        (Submodule.span k
          (Set.range fun v : DoubledQuiver G => signlessPreprojectiveRelator k v)) =
      quadraticZigzagRelations k G := by
  have h := quadraticOrthogonal_quadraticOrthogonal k (DoubledQuiver G)
    (quadraticZigzagRelations k G) (quadraticZigzagRelations_le_grade_two k G)
  rw [quadraticOrthogonal_quadraticZigzagRelations] at h
  exact h

/-- The defining ideal of the quadratic dual of the signless presentation is generated in the
opposite path algebra by the quadratic zigzag relation space. -/
theorem quadraticDualIdeal_signlessPreprojectiveRelators :
    quadraticDualIdeal k (DoubledQuiver G)
        (Submodule.span k
          (Set.range fun v : DoubledQuiver G => signlessPreprojectiveRelator k v)) =
      TwoSidedIdeal.span (MulOpposite.op ''
        (quadraticZigzagRelations k G : Set (pathAlgebra k (DoubledQuiver G)))) := by
  rw [quadraticDualIdeal_eq_span, quadraticOrthogonal_signlessPreprojectiveRelators]

end TauCeti
