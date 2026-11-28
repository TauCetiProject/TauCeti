/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Presentation
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Components

/-!
# Connected components of real affine point spaces

The real points of a finite type affine scheme have finitely many connected components in the
evaluation topology. This gives the finiteness of the component group of the real points of an
affine algebraic group, independently of a matrix embedding.

It suffices that the coordinate algebra becomes finite type after base change to `ℝ`.
The homeomorphism `baseChangeHomeomorph` identifies the original real points with those after
base change. Over `ℝ`, `Algebra.Presentation.pointsHomeomorphZeroSet` realizes the points as the
zero set of a finite presentation. The theorem `IsSemialgebraic.finite_image_connectedComponentIn`
applies to this zero set, including when it is singular or empty.

## References

* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, §2.4.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, vol. 1,
  second edition, §3.1, Theorem 3.12.
-/

public section

open MvPolynomial
open scoped TensorProduct

namespace TauCeti.PointTopology

/-- The space of real points has finitely many connected components whenever the coordinate
algebra is finite type after extension of scalars to `ℝ`. -/
instance instFiniteConnectedComponentsRealPoints
    (k A : Type*) [CommSemiring k] [Algebra k ℝ] [CommSemiring A] [Algebra k A]
    [Algebra.FiniteType ℝ (ℝ ⊗[k] A)] : Finite (ConnectedComponents (A →ₐ[k] ℝ)) := by
  let B := ℝ ⊗[k] A
  have : Algebra.FinitePresentation ℝ B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let P := Algebra.Presentation.ofFinitePresentation ℝ B
  have h : IsSemialgebraic {y | (fun j ↦ eval y (P.relation j)) = 0} :=
    (isSemialgebraic_singleton (fun _ ↦ (0 : ℝ))).preimage_eval P.relation
  have := finite_connectedComponents_iff_finite_image_connectedComponentIn.2
    h.finite_image_connectedComponentIn
  let e := P.pointsHomeomorphZeroSet.symm.trans (baseChangeHomeomorph k ℝ A ℝ)
  exact e.continuous.finite_connectedComponents_of_surjective e.surjective

end TauCeti.PointTopology
