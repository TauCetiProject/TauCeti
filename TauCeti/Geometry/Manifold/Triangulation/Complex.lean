/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.Triangulation.Puncture
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Topology.Triangulable.Sphere

/-!
# Finite punctures of triangulable Riemann surfaces

A Riemann surface is a real `C²` surface, so deleting finitely many points from a compact
connected triangulable Riemann surface leaves a space of finite CW type
(`Set.Finite.finiteCWType_compl_of_isTriangulable_complex`), by the real-manifold result in
`Triangulation.Puncture`. The Riemann sphere `OnePoint ℂ` is triangulable
(`TauCeti.isTriangulable_onePoint`), so the complement of every finite set of its points has
finite CW type (`Set.Finite.finiteCWType_compl_onePoint_complex`). These are stated as theorems
rather than instances, since the finite set is a hypothesis and not part of the type.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (punctured surfaces in the topological proof of Riemann–Hurwitz).
-/

public section

open scoped Manifold

universe u w

namespace Set.Finite

open TauCeti

/-- Deleting finitely many points from a compact connected triangulable Riemann surface leaves a
space of finite CW type. -/
theorem finiteCWType_compl_of_isTriangulable_complex {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y] [T2Space Y] [ConnectedSpace Y] [CompactSpace Y]
    {S : Set Y} (hS : S.Finite) (hY : IsTriangulable.{w} Y) : FiniteCWType ↥Sᶜ := by
  have : IsManifold 𝓘(ℝ, ℂ) 2 Y :=
    (inferInstance : IsManifold 𝓘(ℂ) 1 Y).restrictScalars_of_ne_zero 2 (by norm_num)
  exact hS.finiteCWType_compl_of_isTriangulable (E := ℂ)
    (by rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]; norm_num) hY

/-- **Punctured Riemann spheres have finite CW type.** The complement of a finite set of points
of the Riemann sphere `OnePoint ℂ` has finite CW type. -/
theorem finiteCWType_compl_onePoint_complex {S : Set (OnePoint ℂ)} (hS : S.Finite) :
    FiniteCWType ↥Sᶜ :=
  hS.finiteCWType_compl_of_isTriangulable_complex isTriangulable_onePoint.{0, 0}

end Set.Finite
