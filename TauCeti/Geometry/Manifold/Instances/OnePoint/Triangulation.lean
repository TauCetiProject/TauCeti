/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.Triangulation.Puncture
public import TauCeti.Topology.Triangulable.Sphere
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.Complex.Analytic

/-!
# Finite punctures of the triangulated Riemann sphere

The Riemann sphere `OnePoint ℂ` is triangulated by the boundary of a tetrahedron
(`TauCeti.isTriangulable_onePoint`). As a compact connected triangulable surface it therefore
keeps finite CW type after deleting any finite set
(`Set.Finite.finiteCWType_compl_of_isTriangulable`). This supplies the finite CW models of the
punctured Riemann sphere used in the branched-cover formula for maps onto it.

## Main results

* `TauCeti.RiemannSurface.finiteCWType_compl_onePoint`: the Riemann sphere minus finitely many
  points has finite CW type.
-/

public section

open scoped Manifold

namespace TauCeti.RiemannSurface

/-- The Riemann sphere minus finitely many points has finite CW type: the sphere is triangulated
by the boundary of a tetrahedron, and finite punctures of a compact triangulable surface have
finite CW type. -/
instance finiteCWType_compl_onePoint {S : Set (OnePoint ℂ)} [Finite S] : FiniteCWType ↥Sᶜ := by
  have : IsManifold 𝓘(ℝ, ℂ) 2 (OnePoint ℂ) :=
    (inferInstance : IsManifold 𝓘(ℂ) 1 (OnePoint ℂ)).restrictScalars_of_ne_zero 2 (by norm_num)
  exact S.toFinite.finiteCWType_compl_of_isTriangulable (E := ℂ) (by simp)
    (isTriangulable_onePoint.{0, 0})

end TauCeti.RiemannSurface
