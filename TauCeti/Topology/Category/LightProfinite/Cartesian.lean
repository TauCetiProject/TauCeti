/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.LightProfinite.Cartesian

/-!
# Points of products of light profinite sets

The cartesian monoidal structure on light profinite sets is the product of spaces, so a point
of `S ⊗ T` is a pair and whiskering acts on the corresponding coordinate.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace LightProfinite

/-- Left whiskering by `S` applies a map of light profinite sets to the second coordinate. -/
@[simp]
lemma whiskerLeft_apply (S : LightProfinite.{u}) {T T' : LightProfinite.{u}} (f : T ⟶ T')
    (p : (S ⊗ T : LightProfinite.{u})) :
    (S ◁ f) p = (p.1, f p.2) := rfl

end LightProfinite
