/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Topology.Order
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Weak realizations as quotients of their closed simplices

The weak topology on the realization of an abstract simplicial complex is the quotient topology
for the map from the disjoint union of its closed simplices. Since each closed simplex is locally
path-connected, this quotient presentation proves that every weak realization is locally
path-connected, without finiteness or local-finiteness assumptions on the complex.

This is the quotient-of-closed-simplices part of the weak-realization API. It is also the local
topological input used when a realization serves as the total space of a covering.

## Main definitions

* `AbstractSimplicialComplex.ClosedSimplexSum`: the disjoint union of all closed simplices.
* `AbstractSimplicialComplex.closedSimplexMap`: the canonical map to the weak realization.

## Main results

* `AbstractSimplicialComplex.isQuotientMap_closedSimplexMap`: the canonical map is a quotient map.
* `AbstractSimplicialComplex.instLocallyPathConnectedSpaceRealization`: every weak realization is
  locally path-connected.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2.
-/

public section

noncomputable section

open TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι : Type*}

/-- The disjoint union of the closed coordinate simplices of an abstract simplicial complex. -/
abbrev ClosedSimplexSum (K : AbstractSimplicialComplex ι) :=
  Σ σ : Face K, StandardSimplex σ.1

/-- The canonical map from the disjoint union of the closed simplices to the weak realization. -/
noncomputable def closedSimplexMap (K : AbstractSimplicialComplex ι) :
    ClosedSimplexSum K → Realization K :=
  fun x ↦ faceInclusion K x.1 x.2

/-- The closed-simplex map restricts to the face inclusion on each summand. -/
@[simp]
theorem closedSimplexMap_mk (K : AbstractSimplicialComplex ι) (σ : Face K)
    (x : StandardSimplex σ.1) : closedSimplexMap K ⟨σ, x⟩ = faceInclusion K σ x :=
  (rfl)

/-- Every realization point has a representative in its carrier simplex. -/
theorem surjective_closedSimplexMap (K : AbstractSimplicialComplex ι) :
    Function.Surjective (closedSimplexMap K) := by
  intro x
  refine ⟨⟨carrier K x, ⟨x.1, mem_convexHull_carrier K x⟩⟩, ?_⟩
  exact Subtype.ext (faceInclusion_val K (carrier K x) _)

/-- The weak realization is the quotient of the disjoint union of its closed simplices. -/
theorem isQuotientMap_closedSimplexMap (K : AbstractSimplicialComplex ι) :
    Topology.IsQuotientMap (closedSimplexMap K) := by
  refine ⟨⟨?_⟩, surjective_closedSimplexMap K⟩
  -- Expose the two final topologies so the coinduced-topology lattice laws can identify them.
  change (⨆ σ : Face K, TopologicalSpace.coinduced (faceInclusion K σ) inferInstance) =
    TopologicalSpace.coinduced (closedSimplexMap K)
      (⨆ σ : Face K, TopologicalSpace.coinduced (Sigma.mk σ) inferInstance)
  simp only [coinduced_iSup, coinduced_compose]
  rfl

/-- The map from the disjoint union of closed simplices is continuous. -/
theorem continuous_closedSimplexMap (K : AbstractSimplicialComplex ι) :
    Continuous (closedSimplexMap K) :=
  (isQuotientMap_closedSimplexMap K).continuous

/-- Every weak realization is locally path-connected, with no finiteness or local-finiteness
assumption on the complex. -/
instance instLocallyPathConnectedSpaceRealization (K : AbstractSimplicialComplex ι) :
    LocallyPathConnectedSpace (Realization K) :=
  (isQuotientMap_closedSimplexMap K).locallyPathConnectedSpace

end AbstractSimplicialComplex
