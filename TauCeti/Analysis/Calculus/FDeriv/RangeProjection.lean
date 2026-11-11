/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import TauCeti.MeasureTheory.Function.SpecialFunctions.Projection

/-!
# Measurable projections onto derivative ranges

For a map from a finite-dimensional real or complex normed space to a separable Hilbert space,
the orthogonal projection onto its derivative range is Borel measurable. The map itself need
not be measurable or differentiable everywhere, and the derivative may change rank. At a
nondifferentiability point Mathlib's derivative is zero, and the resulting projection is zero.

On the regular points of a Lipschitz parametrization these projections describe the candidate
tangent planes. Measurability here is on the parameter space; identifying planes on overlapping
charts and descending them to the image are separate geometric statements.

The proof combines Mathlib's `measurable_fderiv` with measurability of finite-rank range
projections.
-/

public section

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F]

/-- The orthogonal projections onto the ranges of the derivative are measurable, including
where the derivative changes rank or the original function is not differentiable. -/
@[fun_prop]
theorem measurable_starProjection_range_fderiv (f : E → F) :
    Measurable fun x ↦ (fderiv 𝕜 f x).range.starProjection :=
  (measurable_fderiv 𝕜 f).starProjection_range

end TauCeti
