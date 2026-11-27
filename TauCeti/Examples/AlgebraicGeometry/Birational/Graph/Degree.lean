/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.Graph.Degree
public import TauCeti.Examples.AlgebraicGeometry.Birational.TopologicalDegree
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Regression examples: the degrees of the projections of the graph of `z ↦ z²`

For `f = (z ↦ z²)` on the affine line over a field `K`, with graph `Γ_f` and projections
`π_1 : Γ_f → 𝔸¹` and `π_2 : Γ_f → 𝔸¹`:

* `π_1` has topological degree `1`: it is an isomorphism over the domain of definition of `f`,
  which is the whole line;
* `π_2` has topological degree `2 = e(f)`, in every characteristic, although `π_1` is birational:
  the second projection computes the degree of `f`, not of the graph.

For the linear projection `𝔸² → 𝔸¹`, `π_2` is dominant with the junk degree `0`: it is not an
alteration, so the equal-dimension hypothesis of the alteration statement is needed.
-/

public section

open CategoryTheory AlgebraicGeometry Scheme.RationalMap

universe u

namespace TauCeti.GraphDegreeExamples

open TauCeti.TopologicalDegreeExamples

variable (K : Type u) [Field K]

/-- `z ↦ z²` is dominant: `MvPolynomial.expand 2` is injective. -/
instance isDominant_squareMap : IsDominant (squareMap K) :=
  ⟨RingHom.denseRange_comap_of_injective _ <| MvPolynomial.expand_injective two_pos⟩

/-- The first projection of the graph of `z ↦ z²` has topological degree `1`. -/
theorem topologicalDegree_graphFst_squareMap :
    (graphFst (squareMap K).toRationalMap).toRationalMap.topologicalDegree = 1 :=
  topologicalDegree_graphFst _

/-- The second projection of the graph of `z ↦ z²` has topological degree `2 = e(f)`. -/
theorem topologicalDegree_graphSnd_squareMap :
    (graphSnd (squareMap K).toRationalMap).toRationalMap.topologicalDegree = 2 := by
  rw [topologicalDegree_graphSnd, topologicalDegree_squareMap]

-- In characteristic `2` as well, where `K(z) / K(z²)` is purely inseparable.
example : (graphSnd (squareMap (ZMod 2)).toRationalMap).toRationalMap.topologicalDegree = 2 :=
  topologicalDegree_graphSnd_squareMap _

/-- For the linear projection `𝔸² → 𝔸¹`, `(x, y) ↦ x`, the second projection of the graph has
the junk topological degree `0` of the projection itself: `π_2` is dominant but not generically
finite, so the equal-dimension hypothesis is needed for `π_2` to be an alteration. -/
theorem topologicalDegree_graphSnd_projection :
    (graphSnd (projection K).toRationalMap).toRationalMap.topologicalDegree = 0 := by
  rw [topologicalDegree_graphSnd, Scheme.RationalMap.topologicalDegree_eq_zero_iff K,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_Spec_mvPolynomial,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_Spec_mvPolynomial, ringKrullDim_eq_zero_of_field]
  norm_num

end TauCeti.GraphDegreeExamples
