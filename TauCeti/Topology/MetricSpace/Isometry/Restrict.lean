/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Restricting distance-preserving maps to subtypes

If a distance-preserving map `f : X → Y` maps `s` into `t`, then its restriction
`Set.MapsTo.restrict f s t : s → t` preserves distances (`Isometry.mapsToRestrict`). Together with
`Isometry.mapsTo_eball`, this restricts a distance-preserving map to finite-distance components.
-/

public section

/-- The restriction of a distance-preserving map to subtypes it maps between preserves
distances. -/
theorem Isometry.mapsToRestrict {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    {f : X → Y} (hf : Isometry f) {s : Set X} {t : Set Y} (h : Set.MapsTo f s t) :
    Isometry (h.restrict f s t) :=
  fun x y ↦ hf.edist_eq x y
