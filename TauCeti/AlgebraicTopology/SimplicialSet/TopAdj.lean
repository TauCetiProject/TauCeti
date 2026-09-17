/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# Naturality of singular vertices

The identification of points with singular zero-simplices commutes with continuous maps.
-/

public section

open CategoryTheory Simplicial

universe u

namespace TauCeti.TopCat

/-- Mapping the singular vertex of a point gives the singular vertex of its image. -/
@[simp]
lemma toSSet_map_app_toSSetObj₀Equiv_symm {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map f).app (Opposite.op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm (f x) := rfl

end TauCeti.TopCat
