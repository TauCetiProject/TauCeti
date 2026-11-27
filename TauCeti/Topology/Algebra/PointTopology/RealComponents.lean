/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Presentation
public import Mathlib.RingTheory.FiniteStability
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Components
import TauCeti.Topology.Connected.FiniteComponents

/-!
# Connected components of real affine point spaces

The real points of a finite type affine scheme have finitely many connected components in the
evaluation topology. This gives the finiteness of the component group of the real points of an
affine algebraic group, independently of a matrix embedding.

It suffices that the coordinate algebra becomes finite type after base change to `ℝ`.
This follows from finite type over the original base by `Algebra.FiniteType.baseChange`.
Over `ℝ`, a finite presentation realizes the real points as the simultaneous
zero set of finitely many polynomials in finitely many variables. The component theorem for
semialgebraic sets applies to this zero set, including when it is singular or empty.

## References

* J. Bochnak, M. Coste and M.-F. Roy, *Real Algebraic Geometry*, §2.4.
* V. Platonov, A. Rapinchuk and I. Rapinchuk, *Algebraic Groups and Number Theory*, vol. 1,
  second edition, §3.1, Theorem 3.12.
-/

public section

open MvPolynomial
open scoped TensorProduct

namespace TauCeti.PointTopology

variable (k A : Type*) [CommSemiring k] [Algebra k ℝ] [CommSemiring A] [Algebra k A]
  [Algebra.FiniteType ℝ (ℝ ⊗[k] A)]

/-- The space of real points has finitely many connected components whenever the coordinate
algebra is finite type after extension of scalars to `ℝ`. -/
instance instFiniteConnectedComponentsRealPoints : Finite (ConnectedComponents (A →ₐ[k] ℝ)) := by
  let B := ℝ ⊗[k] A
  have : Algebra.FinitePresentation ℝ B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let P := Algebra.Presentation.ofFinitePresentation ℝ B
  have h : IsSemialgebraic {y | (fun j ↦ eval y (P.relation j)) = 0} := by
    simpa only [Set.iInter_ofPred, funext_iff, Pi.zero_apply] using
      IsSemialgebraic.iInter (fun j ↦ isSemialgebraic_eval_eq_zero (P.relation j))
  have := ConnectedComponents.finite_iff_finite_image_connectedComponentIn.2
    h.finite_image_connectedComponentIn
  let e := P.pointsHomeomorphZeroSet.symm.trans (baseChangeHomeomorph k ℝ A ℝ)
  exact Finite.of_surjective _ (e.continuous.connectedComponentsMap_surjective e.surjective)

/-- The convolution group of real points of a finite type affine group scheme has finitely
many components. The assertion on the convolution type already holds for any coordinate algebra. -/
instance instFiniteConnectedComponentsWithConvRealPoints :
    Finite (ConnectedComponents (WithConv (A →ₐ[k] ℝ))) :=
  let e := (isHomeomorph_ofConv (k := k) (A := A) (R := ℝ)).homeomorph.symm
  Finite.of_surjective _ (e.continuous.connectedComponentsMap_surjective e.surjective)

end TauCeti.PointTopology
