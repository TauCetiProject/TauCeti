/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Torsion-free covariant derivatives

This file names the pointwise torsion-free condition for a covariant derivative on the tangent
bundle.  When the bundled torsion tensor is available, `isTorsionFree_iff_torsion_eq_zero`
identifies this condition with its vanishing. The condition is available without finite
dimensionality or completeness, supporting the first Bianchi identity in
`TauCetiRoadmap/GeometricTopology/README.md`, Layer 7, “Curvature”.
-/

public section

open Bundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- A covariant derivative on the tangent bundle is torsion-free when it evaluates the Lie
bracket of differentiable vector fields as the difference of their two covariant derivatives. -/
@[expose] def IsTorsionFree
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop :=
  ∀ {X Y : Π x : M, TangentSpace I x} {x : M},
    MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] [IsManifold I 2 M]

/-- The named torsion-free condition is equivalent to vanishing of the bundled torsion tensor. -/
theorem isTorsionFree_iff_torsion_eq_zero
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) :
    cov.IsTorsionFree ↔ cov.torsion = 0 :=
  cov.torsion_eq_zero_iff.symm

end CovariantDerivative
