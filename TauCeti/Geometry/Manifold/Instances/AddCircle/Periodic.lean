/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.AddCircle
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Smooth periodic functions as functions on the circle

A `p`-periodic function `f : ℝ → F` descends to the function `Function.Periodic.lift` on the
circle `ℝ / pℤ`. Since the projection `ℝ → ℝ / pℤ` is a surjective analytic local diffeomorphism
(`AddCircle.isLocalDiffeomorph_coe`), the descended function is `C^n` exactly when `f` is
(`Function.Periodic.contMDiff_lift_iff`). For instance the cosine and sine descend to smooth
functions on `ℝ / 2πℤ`.
-/

public section

open scoped Manifold ContDiff

namespace Function.Periodic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ} [Fact (0 < p)]
  {f : ℝ → F} {n : ℕ∞ω}

/-- **Smooth periodic functions.** A `p`-periodic function on `ℝ` descends to a `C^n` function on
the circle `ℝ / pℤ` exactly when it is `C^n`. -/
theorem contMDiff_lift_iff (hf : Periodic f p) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, F) n (hf.lift : AddCircle p → F) ↔ ContDiff ℝ n f := by
  rw [← (AddCircle.isLocalDiffeomorph_coe p n).contMDiff_comp_iff
    QuotientAddGroup.mk_surjective le_rfl, ← contMDiff_iff_contDiff]
  exact iff_of_eq (congrArg _ (funext hf.lift_coe))

end Function.Periodic
