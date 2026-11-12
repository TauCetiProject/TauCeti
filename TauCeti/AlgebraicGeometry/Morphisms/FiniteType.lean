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
(`Scheme.Hom.exists_isOpenImmersion_finiteType`), and the sections over every affine open are of
finite type over `A` (`Scheme.Hom.finiteType_ΓSpecIso_inv_comp_appLE`). For `X` locally of finite
type over `Spec k`, the algebra `B` of a chart `Spec B ⟶ X` over `Spec k` that is locally of finite
type (for instance an open immersion) is of finite type over `k`
(`Scheme.Hom.finiteType_of_comp_eq_algebraMap`).

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

/-- On an affine open `U` of the source of a morphism `f : X ⟶ Spec A` locally of finite type,
the ring map `A ⟶ Γ(X, U)` induced by `f` is of finite type. -/
theorem finiteType_ΓSpecIso_inv_comp_appLE {U : X.Opens} (hU : IsAffineOpen U) :
    ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top).hom.FiniteType :=
  (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (.of_surjective _ (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.surjective)

/-- If `f : X ⟶ Spec k` is locally of finite type and `i : Spec B ⟶ X` is a morphism locally of
finite type (for instance an open immersion) whose composite with `f` is the structure morphism of
the `k`-algebra `B`, then `B` is of finite type over `k`. -/
theorem finiteType_of_comp_eq_algebraMap {k : Type u} [CommRing k] (g : X ⟶ Spec (.of k))
    [LocallyOfFiniteType g] (B : Type u) [CommRing B] [Algebra k B] (i : Spec (.of B) ⟶ X)
    [LocallyOfFiniteType i] (hi : i ≫ g = Spec.algebraMap k B) :
    Algebra.FiniteType k B := by
  have : LocallyOfFiniteType (Spec.algebraMap k B) := hi ▸ inferInstance
  exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp this)

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
    obtain ⟨x, hx, rfl⟩ := f.continuous.exists_isClosed_singleton_of_mem_range
      (IsClosed.isLocallyClosed hy) hyf
    exact ⟨x, hx, rfl⟩

end AlgebraicGeometry.Scheme.Hom
