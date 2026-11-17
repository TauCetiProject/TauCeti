/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# A deformation starting at a map, as a homotopy

A map `H : I × X → Y` which is `f` at time zero is a homotopy from `f` to its time-one map
`H.curry 1` (`ContinuousMap.Homotopy.ofApplyZero`). This packages a deformation, given as a bare
continuous map together with its value at time zero, for the results which take a homotopy.
-/

public section

open scoped unitInterval

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)}

/-- A map `H : I × X → Y` which is `f` at time zero, as a homotopy from `f` to its time-one map
`H.curry 1`. -/
def ofApplyZero (H : C(I × X, Y)) (hH : ∀ x, H (0, x) = f x) : f.Homotopy (H.curry 1) where
  toContinuousMap := H
  map_zero_left := hH
  map_one_left x := (H.curry_apply 1 x).symm

@[simp]
theorem ofApplyZero_apply (H : C(I × X, Y)) (hH : ∀ x, H (0, x) = f x) (p : I × X) :
    ofApplyZero H hH p = H p :=
  (rfl)

end ContinuousMap.Homotopy
