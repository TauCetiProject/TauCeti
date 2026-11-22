/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Covering families on sites of open subsets

This file extends Mathlib's API for the Grothendieck topology on the category of open subsets of a
topological space (`Opens.grothendieckTopology`), recording that pulling back a covering family of
opens along a continuous map produces a covering family.

## Main results

* `TopologicalSpace.Opens.coversTop_map`: pulling back a covering family of opens along a
  continuous map `f : X ⟶ Y` preserves the `CoversTop` property.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace TopologicalSpace.Opens

/-- Pulling back a covering family of opens along a continuous map `f : X ⟶ Y` gives a covering
family of opens of `X`. -/
theorem coversTop_map {X Y : TopCat.{u}} (f : X ⟶ Y) {ι : Type*} {V : ι → Opens Y}
    (hV : (Opens.grothendieckTopology Y).CoversTop V) :
    (Opens.grothendieckTopology X).CoversTop (fun i ↦ (Opens.map f).obj (V i)) := by
  rw [Opens.coversTop_iff] at hV ⊢
  rw [IsOpenCover, ← Function.comp_def, ← Opens.map_iSup, hV.iSup_eq_top, Opens.map_top]

end TopologicalSpace.Opens
