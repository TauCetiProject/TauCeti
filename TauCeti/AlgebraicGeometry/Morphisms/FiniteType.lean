/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import TauCeti.Topology.JacobsonSpace

/-!
# Closed points in the image of a finite-type morphism

A morphism locally of finite type into a Jacobson scheme maps closed points to closed
points. Conversely, every closed point in its image lifts to a closed point of the source:
the nonempty closed fiber contains a closed point in the Jacobson source. Thus its image
on closed points is exactly the closed-point part of its full topological image.

This complements Mathlib's `Scheme.Hom.closedPoints_subset_preimage_closedPoints` with the
lifting direction, needed to compare rational and topological orbit images.

## References

* The Stacks Project, Tag 01TB, morphisms locally of finite type into Jacobson schemes.
-/

public section

open Topology

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [JacobsonSpace Y]

/-- The image on closed points is exactly the intersection of the full image with the
closed points of the target. -/
theorem image_closedPoints_eq_range_inter_closedPoints :
    f '' closedPoints X = Set.range f ∩ closedPoints Y := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, f.closedPoints_subset_preimage_closedPoints hx⟩
  · rintro ⟨hyf, hy⟩
    obtain ⟨x, hx, rfl⟩ := f.continuous.exists_isClosed_singleton_of_mem_range hy hyf
    exact ⟨x, hx, rfl⟩

end AlgebraicGeometry.Scheme.Hom
