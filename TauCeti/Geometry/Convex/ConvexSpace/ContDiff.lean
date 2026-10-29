/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Smooth ambient maps of barycentric weights

The map of standard simplices induced by a map of finite index sets extends to a smooth
map of their ambient real weight spaces. This extension allows precomposition of locally
smoothly extendible maps, including at faces and corners of a simplex.
-/

public section

open scoped ContDiff

namespace Convexity.StdSimplex

variable {X Y : Type*} [Fintype X] [DecidableEq Y]

/-- The ambient push-forward of barycentric weights, summing over each fibre. -/
def weightMap (f : X → Y) (w : X → ℝ) (j : Y) : ℝ :=
  ∑ i with f i = j, w i

@[simp]
theorem weightMap_apply (f : X → Y) (w : X → ℝ) (j : Y) :
    weightMap f w j = ∑ i with f i = j, w i :=
  (rfl)

/-- The push-forward of ambient weights is smooth. -/
theorem contDiff_weightMap [Fintype Y] (f : X → Y) : ContDiff ℝ ∞ (weightMap f) := by
  apply contDiff_pi.mpr
  intro j
  exact ContDiff.sum fun i _ ↦ contDiff_apply ℝ (fun _ : X ↦ ℝ) i

/-- The ambient push-forward restricts to the usual map of standard simplices. -/
theorem weightMap_weights (f : X → Y) (x : StdSimplex ℝ X) :
    weightMap f x.weights = (x.map f).weights := by
  ext j
  exact (weights_map_apply f x j).symm

end Convexity.StdSimplex
