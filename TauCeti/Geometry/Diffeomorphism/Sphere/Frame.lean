/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Geometry.Manifold.Instances.Sphere.Frame
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The frame of a diffeomorphism of a sphere

The frame `TauCeti.sphereFrame p f` of a self-map `f` of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` at a point `p`
is defined in `TauCeti.Geometry.Manifold.Instances.Sphere.Frame`. This file specializes its general
properties to the group `Diff(Sⁿ)` of `C^m` diffeomorphisms, `1 ≤ m`, with its weak Whitney
topology.

## Main results

* `TauCeti.linearIndependent_sphereFrame_diffeomorph`: the frame of a diffeomorphism is a basis.
* `TauCeti.continuous_sphereFrame_diffeomorph`: the frame depends continuously on the
  diffeomorphism.
-/

public section

open Metric
open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {n : ℕ} {m : ℕ∞ω} (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The frame of a `C^m` diffeomorphism of the sphere, `1 ≤ m`, is linearly independent. -/
theorem linearIndependent_sphereFrame_diffeomorph (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    LinearIndependent ℝ (sphereFrame p f) :=
  linearIndependent_sphereFrame p (f.isInvertible_mfderiv (zero_lt_one.trans_le hm).ne').injective

/-- The frame at `p` of a `C^m` diffeomorphism of the sphere, `1 ≤ m`, depends continuously on the
diffeomorphism for the weak Whitney topology. -/
theorem continuous_sphereFrame_diffeomorph (hm : 1 ≤ m) :
    Continuous fun f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m ↦
      sphereFrame p f :=
  (continuous_sphereFrame p hm).comp Diffeomorph.continuous_toContMDiffMap

end TauCeti
