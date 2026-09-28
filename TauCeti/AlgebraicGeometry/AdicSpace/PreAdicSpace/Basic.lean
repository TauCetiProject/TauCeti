/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Algebra.Category.Ring.Colimits
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Basic

/-!
# Pre-adic spaces

A pre-adic space has a presheaf of complete separated topological rings, local ring stalks,
and a valuation on the residue field at every point. The valuation is a point of the valuation
spectrum, so it is specified only up to equivalence. Stalks and residue fields are taken after
forgetting the topology on the rings; no topology is imposed on a stalk.

This is the object-level input for morphisms of pre-adic spaces and for the sheafy full
subcategory.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

universe u

/-- A topological space with a presheaf of complete separated topological commutative rings,
local stalks, and a valuation on each stalk's residue field. Stalks are formed after forgetting
the topology on sections. -/
structure PreAdicSpace where
  /-- The underlying presheafed space of complete separated topological rings. -/
  toPresheafedSpace : AlgebraicGeometry.PresheafedSpace
    CompleteSeparatedTopCommRingCat.{u}
  /-- Every stalk of the underlying ring presheaf is local. -/
  isLocalRing : ∀ x : toPresheafedSpace,
    IsLocalRing (((TopCommRingCat.isCompleteSeparated.ι ⋙
      forget₂ TopCommRingCat CommRingCat).mapPresheaf.obj toPresheafedSpace).presheaf.stalk x)
  /-- The valuation of the residue field at each point. -/
  valuation : ∀ x : toPresheafedSpace,
    letI := isLocalRing x
    ValuationSpectrum (IsLocalRing.ResidueField
      (((TopCommRingCat.isCompleteSeparated.ι ⋙
        forget₂ TopCommRingCat CommRingCat).mapPresheaf.obj toPresheafedSpace).presheaf.stalk x))

namespace PreAdicSpace

/-- The underlying topological space of a pre-adic space. -/
abbrev toTopCat (X : PreAdicSpace.{u}) : TopCat := X.toPresheafedSpace.carrier

/-- Points of a pre-adic space are points of its underlying topological space. -/
instance : CoeSort PreAdicSpace.{u} (Type u) := ⟨fun X => X.toTopCat⟩

/-- The presheafed space obtained by forgetting the topology on the sections. -/
noncomputable abbrev toRingPresheafedSpace (X : PreAdicSpace.{u}) :
    AlgebraicGeometry.PresheafedSpace CommRingCat.{u} :=
  (TopCommRingCat.isCompleteSeparated.ι ⋙
    forget₂ TopCommRingCat CommRingCat).mapPresheaf.obj X.toPresheafedSpace

/-- The underlying ring presheaf has local stalks. -/
instance (X : PreAdicSpace.{u}) (x : X) :
    IsLocalRing (X.toRingPresheafedSpace.presheaf.stalk x) := X.isLocalRing x

end PreAdicSpace

end TauCeti

end
