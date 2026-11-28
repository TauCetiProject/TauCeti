/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Continuous maps on products

Precomposition with a cast between equal tuple lengths preserves a continuous map up to
heterogeneous equality.
-/

public section

namespace ContinuousMap

/-- Precomposing with the cast between equal tuple lengths preserves the continuous map
up to heterogeneous equality. -/
theorem comp_precomp_fin_cast_heq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {i j : ℕ} (f : C(Fin j → X, Y)) (e : i = j) :
    HEq (f.comp (precomp (X := fun _ ↦ X) (Fin.cast e.symm))) f := by
  subst e
  -- Casting along reflexivity acts as the identity on tuples.
  rfl

end ContinuousMap
