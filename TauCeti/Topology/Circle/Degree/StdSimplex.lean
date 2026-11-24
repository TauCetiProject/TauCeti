/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.Topology
public import TauCeti.Topology.Circle.Degree
import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
import TauCeti.Geometry.Convex.ConvexSpace.LocallyPathConnectedSpaceStdSimplex

/-!
# Angles swept around the boundary of the standard `2`-simplex

A continuous map `g` from the standard `2`-simplex to the circle sweeps no total angle around the
boundary of the simplex: the alternating sum of the angles `Circle.sweptAngle` swept by `g` along
the three edges, each parametrized by the unit interval through `Convexity.StdSimplex.homeomorphI`
and included by `Convexity.StdSimplex.faceInclusion`, vanishes
(`Circle.sum_sweptAngle_faceInclusion_eq_zero`). Since the simplex is simply connected and locally
path connected, `g` lifts through `Circle.exp` to a continuous real function, and the angles swept
along the edges are differences of its values at the vertices, which cancel.
-/

public section

open Convexity
open scoped unitInterval

namespace Circle

/-- **A map from the `2`-simplex sweeps no angle around its boundary.** For a continuous map `g`
from the standard `2`-simplex to the circle, the alternating sum of the angles swept by `g` along
the edges `t ↦ faceInclusion i (homeomorphI.symm t)` vanishes. -/
theorem sum_sweptAngle_faceInclusion_eq_zero (g : C(StdSimplex ℝ (Fin 3), Circle)) :
    ∑ i : Fin 3, (-1 : ℝ) ^ (i : ℕ) *
      sweptAngle (fun t ↦ g (StdSimplex.faceInclusion i (StdSimplex.homeomorphI.symm t))) = 0 := by
  obtain ⟨G, ⟨-, hG⟩, -⟩ := isCoveringMap_exp.existsUnique_continuousMap_lifts g
    (StdSimplex.single 0) (Complex.arg (g (StdSimplex.single 0))) (exp_arg _)
  have hface (i : Fin 3) :
      sweptAngle (fun t ↦ g (StdSimplex.faceInclusion i (StdSimplex.homeomorphI.symm t))) =
      G (StdSimplex.single (i.succAbove 1)) - G (StdSimplex.single (i.succAbove 0)) := by
    have hc : Continuous fun t ↦ StdSimplex.faceInclusion i (StdSimplex.homeomorphI.symm t) :=
      (StdSimplex.faceInclusion i).continuous.comp StdSimplex.homeomorphI.symm.continuous
    rw [sweptAngle_eq_sub (w := fun t ↦ g _) (g.continuous.comp hc) (θ := fun t ↦ G _)
      (G.continuous.comp hc) fun t ↦ congr_fun hG _]
    simp [StdSimplex.homeomorphI_symm_one, StdSimplex.homeomorphI_symm_zero, StdSimplex.map_single]
  simp only [Fin.sum_univ_three, hface]
  simp [Fin.succAbove]

end Circle
