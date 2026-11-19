/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Smooth periodic functions on the circle

A `p`-periodic function `f : ℝ → F` descends to the function `Function.Periodic.lift` on the
circle `AddCircle p`. Since the projection `ℝ → AddCircle p` is a surjective smooth local
diffeomorphism (`AddCircle.isLocalDiffeomorph_coe`), the lift is `C^n` exactly when `f` is
(`Function.Periodic.contMDiff_lift_iff`). For instance `cos` and `sin` descend to smooth functions
on `AddCircle (2 * π)`, the coordinate functions of the angle.
-/

public section

open scoped Manifold ContDiff

namespace Function.Periodic

variable {p : ℝ} [Fact (0 < p)] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : ℝ → F} {n : WithTop ℕ∞}

/-- **Smooth periodic functions.** The lift to the circle `AddCircle p` of a `p`-periodic function
`f : ℝ → F` is `C^n` exactly when `f` is `C^n`. -/
theorem contMDiff_lift_iff (hf : Periodic f p) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, F) n hf.lift ↔ ContDiff ℝ n f := by
  rw [← (AddCircle.isLocalDiffeomorph_coe p n).contMDiff_comp_iff
    QuotientAddGroup.mk_surjective le_rfl, contMDiff_iff_contDiff]
  exact Iff.of_eq (congrArg _ (funext hf.lift_coe))

/-- The lift to the circle `AddCircle p` of a `C^n` `p`-periodic function is `C^n`. -/
theorem contMDiff_lift (hf : Periodic f p) (hf' : ContDiff ℝ n f) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, F) n hf.lift :=
  hf.contMDiff_lift_iff.2 hf'

end Function.Periodic
