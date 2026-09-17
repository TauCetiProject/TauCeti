/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex

/-!
# Vertices of the topological simplices, and their contractibility

The topological `n`-simplex is a standard simplex on a finite nonempty type, up to a universe
lift, hence contractible and in particular simply connected.  This file also names its initial
vertex.
-/

public section

open CategoryTheory Convexity

universe u

namespace SimplexCategory

instance contractibleSpace (n : SimplexCategory) : ContractibleSpace (toTop.{u}.obj n) :=
  (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).contractibleSpace

/-- The initial vertex of the topological `n`-simplex: the universe lift of the standard-simplex
vertex `StdSimplex.single 0`. -/
@[expose]
noncomputable def toTopInitialVertex (n : SimplexCategory) : toTop.{u}.obj n :=
  ULift.up (StdSimplex.single 0)

@[simp]
lemma toTopInitialVertex_down (n : SimplexCategory) :
    (toTopInitialVertex.{u} n).down = StdSimplex.single 0 := rfl

end SimplexCategory
