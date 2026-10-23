/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.CombinatorialManifold.ZeroDimensional
public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic
public import TauCeti.Geometry.Manifold.PLGroupoid.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# PL realizations of combinatorial zero-manifolds

The weak realization of a combinatorial zero-manifold is discrete: the void vertex links
force every face to be a singleton. Mathlib's discrete chart construction therefore gives
an atlas over the zero-dimensional real vector space. All its coordinate changes are PL.

This supplies the dimension-zero case of the passage from the combinatorial link condition
to PL manifolds, without requiring a nonempty, finite or countable vertex type. The atlas
is the existing `ChartedSpace.ofDiscreteTopology`, so its preferred chart at each point has
that singleton as source.

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

/-- A combinatorial zero-manifold admits a PL atlas on its weak realization, modelled on
the zero-dimensional real vector space. -/
theorem IsCombinatorialManifold.exists_chartedSpace_hasGroupoid_zero
    (h : IsCombinatorialManifold K.toPreAbstractSimplicialComplex 0) :
    ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (Realization K),
      @HasGroupoid _ _ _ _ c (TauCeti.PLGroupoid 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))) := by
  let := h.discreteTopology_realization
  let := ChartedSpace.ofDiscreteTopology (M := Realization K)
    (H := EuclideanSpace ℝ (Fin 0))
  exact ⟨inferInstance, inferInstance⟩

end PreAbstractSimplicialComplex
