/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ZeroDimensional
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
public import TauCeti.Geometry.Manifold.PLGroupoid.Basic

/-!
# PL realizations of combinatorial zero-manifolds

The weak realization of a combinatorial zero-manifold is discrete: the void vertex links
force every face to be a singleton. Mathlib's discrete chart construction
`ChartedSpace.ofDiscreteTopology` therefore gives an atlas over any one-point real vector
space, such as the zero-dimensional Euclidean space. All its coordinate changes are PL.

This supplies the dimension-zero case of the passage from the combinatorial link condition
to PL manifolds, without requiring a nonempty, finite or countable vertex type. The PL
statement is about that concrete atlas, so its preferred chart at a point `x` is the constant
chart with source `{x}` (`chartedSpace_of_discreteTopology_chartAt`).

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapters 2--3 (PL structures and combinatorial manifolds).
-/

public section

open AbstractSimplicialComplex
open scoped Manifold

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι] {K : AbstractSimplicialComplex ι}

/-- The weak realization of a combinatorial zero-manifold has the discrete topology. -/
theorem IsCombinatorialManifold.discreteTopology_realization
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex 0) :
    DiscreteTopology (Realization K) := by
  obtain rfl := isCombinatorialManifold_zero_iff_eq_bot.mp h
  infer_instance

/-- On the weak realization of a combinatorial zero-manifold, the discrete atlas
`ChartedSpace.ofDiscreteTopology` over a one-point model is PL compatible. -/
theorem IsCombinatorialManifold.hasGroupoid_PLGroupoid_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Unique E]
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex 0) :
    letI := h.discreteTopology_realization
    letI := ChartedSpace.ofDiscreteTopology (M := Realization K) (H := E)
    HasGroupoid (Realization K) (TauCeti.PLGroupoid 𝓘(ℝ, E)) := by
  let := h.discreteTopology_realization
  let := ChartedSpace.ofDiscreteTopology (M := Realization K) (H := E)
  infer_instance

end PreAbstractSimplicialComplex
