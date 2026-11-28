/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.HopfIdealPoints.Topology
public import TauCeti.Topology.Algebra.PointTopology.RealComponents
import TauCeti.Topology.ConnectedComponents

/-!
# Finitely many components of a real algebraic matrix group

The real matrices in a closed subgroup scheme of `GLₙ` have finitely many connected components
in their usual topology. Indeed, their space is homeomorphic to the real points of the quotient
coordinate algebra, which is finite type. This is the component assertion of Platonov, Rapinchuk
and Rapinchuk, *Algebraic Groups and Number Theory*, vol. 1, second edition, Theorem 3.12.
-/

public section

namespace TauCeti.GeneralLinear

/-- The real points of a closed subgroup scheme of `GLₙ` have finitely many connected components
in the subspace topology of `GLₙ(ℝ)`. -/
instance instFiniteConnectedComponentsHopfIdealPointsSubgroupReal
    {k : Type*} [CommRing k] [Algebra k ℝ] (n : ℕ) (I : HopfIdeal k (coordinateHopfAlgebra k n)) :
    Finite (ConnectedComponents (hopfIdealPointsSubgroup n I ℝ)) := by
  have h := isHomeomorph_hopfIdealPointsSubgroupMulEquiv (R := ℝ) n I
  exact h.continuous.finite_connectedComponents_of_surjective h.surjective

end TauCeti.GeneralLinear
