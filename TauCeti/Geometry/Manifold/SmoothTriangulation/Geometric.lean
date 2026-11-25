/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Geometric
public import TauCeti.Geometry.Manifold.SmoothTriangulation.StarImmersion

/-!
# Star immersions from geometric complexes

The comparison map from the realization of a geometric complex to its ambient normed space
is an injective star immersion of every class: it is injective and equals its secant map.
The facewise criteria for smooth triangulations from rectilinear complexes are in
`TauCeti.Geometry.Manifold.SmoothTriangulation.Rectilinear`.

## Main results

* `Geometry.SimplicialComplex.isStarImmersion_realizationToAmbient`: the comparison map is a
  star immersion of every class.
-/

public section

noncomputable section

open AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {K : SimplicialComplex ℝ V}
  {n : WithTop ℕ∞}

/-- The comparison map of a geometric complex is a star immersion of every class `Cⁿ`. -/
theorem isStarImmersion_realizationToAmbient :
    TauCeti.IsStarImmersion n K.realizationToAmbient := by
  have h := isStarImmersion_secantMap (n := n) (f := K.realizationToAmbient) (by
    rw [secantMap_realizationToAmbient]
    exact realizationToAmbient_injective)
  rwa [secantMap_realizationToAmbient] at h

end Geometry.SimplicialComplex
