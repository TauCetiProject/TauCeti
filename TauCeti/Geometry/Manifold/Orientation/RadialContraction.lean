/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import TauCeti.Analysis.InnerProductSpace.Euclidean.RadialContraction
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Radial contractions preserve orientation at their centre

A radial contraction of a finite-dimensional real normed space `E` fixes its centre, and its
derivative there is the identity. So it preserves every orientation of `E` at its centre
(`TauCeti.isOrientationPreservingAt_radialContraction_self`).

## Main results

* `TauCeti.isOrientationPreservingAt_radialContraction_self`: a radial contraction preserves every
  orientation of `E` at its centre.
-/

public section

open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

/-- A radial contraction preserves every orientation of `E` at its centre. -/
theorem isOrientationPreservingAt_radialContraction_self
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (c : E) (κ : ℝ) :
    o.IsOrientationPreservingAt o (radialContraction c κ) c := by
  -- It fixes its centre, and its derivative there is the identity.
  refine Manifold.Orientation.isOrientationPreservingAt_of_apply_eq_of_mfderiv_eq_id o
    (radialContraction_self c κ) ?_
  rw [mfderiv_eq_fderiv, (hasFDerivAt_radialContraction_self c κ).fderiv]
  -- `mfderiv_eq_fderiv` conjugates by `NormedSpace.fromTangentSpace`, which is the identity of
  -- `E` by definition.
  ext v
  rfl

end TauCeti
