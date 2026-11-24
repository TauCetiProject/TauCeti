/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.LightProfinite.Cartesian

/-!
# Evaluation in the cartesian monoidal structure on light profinite sets

Left whiskering acts on the second coordinate of the type-theoretic product.
-/

public section

universe u

open CategoryTheory MonoidalCategory

namespace LightProfinite

/-- Left whiskering applies the given morphism to the second coordinate. -/
lemma whiskerLeft_apply (S : LightProfinite.{u}) {T U : LightProfinite.{u}}
    (f : T ⟶ U) (x : S) (y : T) : (S ◁ f) (x, y) = (x, f y) := by
  rfl

end LightProfinite
