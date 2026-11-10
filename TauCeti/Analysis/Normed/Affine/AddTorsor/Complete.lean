/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Completeness of normed affine spaces

A normed affine space whose space of translations is complete is complete, since it is isometric
to its space of translations.

## Main results

* `completeSpace_of_normedAddTorsor`: a normed affine space over a complete normed group is
  complete.
-/

public section

/-- A normed affine space over a complete normed group is complete. -/
theorem completeSpace_of_normedAddTorsor (V : Type*) {P : Type*} [NormedAddCommGroup V]
    [CompleteSpace V] [MetricSpace P] [NormedAddTorsor V P] : CompleteSpace P :=
  (IsometryEquiv.vaddConst (Classical.arbitrary P)).symm.completeSpace
