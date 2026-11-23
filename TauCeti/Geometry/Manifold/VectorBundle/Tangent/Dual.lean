/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Nontriviality and separating duals of tangent spaces

The tangent space `TangentSpace I x` of a manifold modelled on `I : ModelWithCorners 𝕜 E H` is the
model space `E`, so it is nontrivial when `E` is, a subsingleton when `E` is, and its points are
separated by continuous linear forms when those of `E` are. These instances let typeclass
inference see the cotangent space `TangentSpace I x →L[𝕜] 𝕜` without unfolding `TangentSpace`: it
contains a nonzero covector in positive dimension over `ℝ` or `ℂ`
(`SeparatingDual.instNontrivialContinuousLinearMapIdOfContinuousSMul`), and it is the zero space in
dimension zero.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A tangent space of a manifold modelled on a nontrivial space is nontrivial. -/
instance [Nontrivial E] (x : M) : Nontrivial (TangentSpace I x) :=
  inferInstanceAs (Nontrivial E)

/-- A tangent space of a manifold modelled on the zero space is the zero space. -/
instance [Subsingleton E] (x : M) : Subsingleton (TangentSpace I x) :=
  inferInstanceAs (Subsingleton E)

/-- Continuous linear forms separate the points of a tangent space whenever they separate the
points of the model space, as they do over `ℝ` and `ℂ` by the Hahn–Banach theorem. -/
instance [SeparatingDual 𝕜 E] (x : M) : SeparatingDual 𝕜 (TangentSpace I x) :=
  inferInstanceAs (SeparatingDual 𝕜 E)

end TauCeti
