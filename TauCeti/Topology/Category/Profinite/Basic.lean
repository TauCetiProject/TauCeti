/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.Profinite.Basic

/-!
# Finite sets as compact Hausdorff spaces

A finite set, regarded as a compact Hausdorff space through `FintypeCat.toProfinite` and
`profiniteToCompHaus`, is discrete.
-/

public section

universe u

/-- A finite set, regarded as a compact Hausdorff space, is discrete. -/
instance FintypeCat.discreteTopology_profiniteToCompHaus_obj (T : FintypeCat.{u}) :
    DiscreteTopology (profiniteToCompHaus.obj (FintypeCat.toProfinite.obj T)) :=
  inferInstanceAs (DiscreteTopology (FintypeCat.toProfinite.obj T))
