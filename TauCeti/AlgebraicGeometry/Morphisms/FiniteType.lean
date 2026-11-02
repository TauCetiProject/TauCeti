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

The file also records the affine charts of a morphism `X ⟶ Spec A` locally of finite type:
every point lies in an affine open `Spec R ⟶ X` with `R` of finite type over `A`
(`Scheme.Hom.exists_isOpenImmersion_finiteType`).

This complements Mathlib's `Scheme.Hom.closedPoints_subset_preimage_closedPoints` with the
lifting direction, needed to compare rational and topological orbit images.

## References

* The Stacks Project, Tag 01TB, morphisms locally of finite type into Jacobson schemes.
-/

public section

open CategoryTheory Topology

namespace AlgebraicGeometry.Scheme.Hom

universe u

section Chart

variable {X : Scheme.{u}} {A : CommRingCat.{u}} (f : X ⟶ Spec A) [LocallyOfFiniteType f]

/-- Every point of the source of a morphism `f : X ⟶ Spec A` locally of finite type lies in the
image of an affine open immersion `g : Spec R ⟶ X` such that `g ≫ f` is induced by a ring map
`A ⟶ R` of finite type. -/
theorem exists_isOpenImmersion_finiteType (x : X) :
    ∃ (R : CommRingCat.{u}) (g : Spec R ⟶ X) (_ : IsOpenImmersion g) (y : Spec R)
      (φ : A ⟶ R) (_ : Spec.map φ = g ≫ f), g y = x ∧ φ.hom.FiniteType := by
  obtain ⟨R, g, _, ⟨y, rfl⟩, -⟩ :=
    X.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) (by simp)
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = g ≫ f := ⟨_, Spec.map_preimage _⟩
  exact ⟨R, g, inferInstance, y, φ, hφ, rfl,
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)⟩

end Chart

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
