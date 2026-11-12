/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Homotopy

/-!
# Local path-connectedness of weak realizations

The weak realization of an abstract simplicial complex is the quotient of the disjoint union of
its closed simplices (`AbstractSimplicialComplex.isQuotientMap_sigma_faceInclusion`). Since each
closed simplex is locally path-connected, this quotient presentation proves that every weak
realization is locally path-connected, without finiteness or local-finiteness assumptions on the
complex.

This is the local topological input used when a realization serves as the total space of a
covering.

## Main results

* `AbstractSimplicialComplex.instLocallyPathConnectedSpaceRealization`: every weak realization is
  locally path-connected.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- Every weak realization is locally path-connected, with no finiteness or local-finiteness
assumption on the complex. -/
instance instLocallyPathConnectedSpaceRealization (K : AbstractSimplicialComplex ι) :
    LocallyPathConnectedSpace (Realization K) :=
  (isQuotientMap_sigma_faceInclusion K).locallyPathConnectedSpace

end AbstractSimplicialComplex
