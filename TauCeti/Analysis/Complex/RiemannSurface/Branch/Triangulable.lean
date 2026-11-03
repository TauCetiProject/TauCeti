/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
public import TauCeti.Geometry.Manifold.Triangulation.Puncture
public import TauCeti.Topology.Triangulable.FiniteCWType
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# The branched-cover Euler formula for triangulable surfaces

Finite triangulations supply finite CW models for compact Riemann surfaces and for their
complements of finite sets. Consequently the topological branched-cover formula holds for
triangulable compact connected Riemann surfaces without separate finite-CW hypotheses for
the surfaces or for the complement of the branch values.

This applies the fibre-counting and covering calculation in `Branch.EulerCharacteristic`;
it neither constructs surface triangulations nor defines genus.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §17 (the topological proof of
  Riemann–Hurwitz).
-/

public section

open scoped Manifold

universe u v w

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace X] [PreconnectedSpace Y]

/-- The topological branched-cover formula for triangulable compact connected Riemann
surfaces: `χ(X) = degree(f) * χ(Y) - ramificationDegree(f)`. Finite CW type of the
surfaces and of the punctured target is derived from their triangulations. Compactness of the
target follows from surjectivity of the finite holomorphic map. -/
theorem eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_isTriangulable
    (f : FiniteHolomorphicMap X Y) (hX : IsTriangulable.{v} X) (hY : IsTriangulable.{w} Y) :
    haveI : CompactSpace Y := f.surjective.compactSpace f.holomorphic.continuous
    haveI := hX.finiteCWType
    haveI := hY.finiteCWType
    eulerChar X = degree f * eulerChar Y - ramificationDegree f := by
  obtain ⟨x, _, _⟩ := f.nonconstant
  have : ConnectedSpace X := ⟨⟨x⟩⟩
  have : ConnectedSpace Y := ⟨⟨f x⟩⟩
  have : CompactSpace Y := f.surjective.compactSpace f.holomorphic.continuous
  have : IsManifold 𝓘(ℝ, ℂ) 2 Y :=
    (inferInstance : IsManifold 𝓘(ℂ) 1 Y).restrictScalars_of_ne_zero 2 (by norm_num)
  have := hX.finiteCWType
  have := hY.finiteCWType
  have := f.finite_branchValues.finiteCWType_compl_of_isTriangulable (E := ℂ)
    (by rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]; norm_num) hY
  exact f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree

end TauCeti.RiemannSurface.FiniteHolomorphicMap
