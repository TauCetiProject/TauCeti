/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.Profinite.Basic

/-!
# Finite profinite sets

A finite set, regarded as a compact Hausdorff space through `FintypeCat.toProfinite` and
`profiniteToCompHaus`, is discrete.

A profinite set `S` with a `Fintype` structure is isomorphic to its image
`FintypeCat.toProfinite.obj (FintypeCat.of S)` under the inclusion of finite sets: both have
carrier `S`, the topology on `S` is discrete because `S` is finite and Hausdorff, and the
topology on the right is discrete by construction. The isomorphism
`Profinite.isoToProfiniteOfFintype` is the identity on points in both directions.
-/

public section

universe u

open CategoryTheory

/-- A finite set, regarded as a compact Hausdorff space, is discrete. -/
instance FintypeCat.discreteTopology_profiniteToCompHaus_obj (T : FintypeCat.{u}) :
    DiscreteTopology (profiniteToCompHaus.obj (FintypeCat.toProfinite.obj T)) :=
  inferInstanceAs (DiscreteTopology (FintypeCat.toProfinite.obj T))

namespace Profinite

/-- A profinite set `S` with a `Fintype` structure is isomorphic to its image under
`FintypeCat.toProfinite`. Both sides have carrier `S` by definition and both topologies are
discrete, so the maps in both directions are the identity. -/
def isoToProfiniteOfFintype (S : Profinite.{u}) [Fintype S] :
    S ≅ FintypeCat.toProfinite.obj (FintypeCat.of S) :=
  haveI : DiscreteTopology (FintypeCat.toProfinite.obj (FintypeCat.of S)) := ⟨rfl⟩
  CompHausLike.isoOfHomeo
    { Equiv.refl S with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- The forward map of `isoToProfiniteOfFintype S` is the identity on points. -/
@[simp]
theorem isoToProfiniteOfFintype_hom_apply (S : Profinite.{u}) [Fintype S] (x : S) :
    (isoToProfiniteOfFintype S).hom x = x :=
  (rfl)

/-- The inverse map of `isoToProfiniteOfFintype S` is the identity on points. -/
@[simp]
theorem isoToProfiniteOfFintype_inv_apply (S : Profinite.{u}) [Fintype S]
    (x : FintypeCat.toProfinite.obj (FintypeCat.of S)) :
    (isoToProfiniteOfFintype S).inv x = x :=
  (rfl)

end Profinite
