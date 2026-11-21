/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Groupoid.Basic
public import TauCeti.Topology.CategoryTheory.FullSubcategory
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory
public import TauCeti.Topology.CategoryTheory.Prod
public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Basic
public import TauCeti.Topology.CategoryTheory.Comma

/-!
# Restrictions, products, comma categories and action examples of topological groupoids

Full restriction to any predicate on objects, binary products, and comma categories (weak fiber
products over a groupoid) preserve the topological-groupoid axioms, using the existing subspace,
product, and comma topologies on objects and total arrows. No openness of the restricted object set
or transversality of the functors is necessary. The native action groupoid of a continuous action
of a topological group is a topological groupoid, retaining every group label, including
ineffective isotropy.

The continuity proofs and topologies are those of `FullSubcategory`, `Prod`, `Comma`, and
`ActionGroupoid.Basic`; this module packages them through `IsTopologicalGroupoid`.
-/

public section

open CategoryTheory

namespace TauCeti

/-- Full restriction of a topological groupoid, with the subspace topologies on objects and
arrows, is a topological groupoid. -/
instance IsTopologicalGroupoid.fullSubcategory {C : Type*} [Category C] [IsGroupoid C]
    [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)] [IsTopologicalGroupoid C]
    (P : ObjectProperty C) : IsTopologicalGroupoid P.FullSubcategory where
  continuous_source := continuous_source_fullSubcategory IsTopologicalGroupoid.continuous_source
  continuous_target := continuous_target_fullSubcategory IsTopologicalGroupoid.continuous_target
  continuous_unit := continuous_unit_fullSubcategory IsTopologicalGroupoid.continuous_unit
  continuous_inverse := by
    let := Groupoid.ofIsGroupoid (C := C)
    convert continuous_inverse_fullSubcategory (P := P)
      IsTopologicalGroupoid.continuous_inverse using 1
    funext a
    congr 1
    exact ObjectProperty.hom_ext _ (ObjectProperty.hom_inv a.hom)
  continuous_comp := by
    simpa only [Quiver.Total.comp_def] using continuous_comp_fullSubcategory (P := P)
      (by simpa only [Quiver.Total.comp_def] using
        (IsTopologicalGroupoid.continuous_comp (C := C)))

/-- The product of topological groupoids uses the product topologies on objects and arrows. -/
instance IsTopologicalGroupoid.prod {C D : Type*} [Category C] [IsGroupoid C]
    [Category D] [IsGroupoid D]
    [TopologicalSpace C] [TopologicalSpace D]
    [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]
    [IsTopologicalGroupoid C] [IsTopologicalGroupoid D] : IsTopologicalGroupoid (C × D) where
  continuous_source := continuous_source_prod IsTopologicalGroupoid.continuous_source
    IsTopologicalGroupoid.continuous_source
  continuous_target := continuous_target_prod IsTopologicalGroupoid.continuous_target
    IsTopologicalGroupoid.continuous_target
  continuous_unit := continuous_unit_prod IsTopologicalGroupoid.continuous_unit
    IsTopologicalGroupoid.continuous_unit
  continuous_inverse := by
    let := Groupoid.ofIsGroupoid (C := C)
    let := Groupoid.ofIsGroupoid (C := D)
    exact continuous_inverse_prod IsTopologicalGroupoid.continuous_inverse
      IsTopologicalGroupoid.continuous_inverse
  continuous_comp := by
    simpa only [Quiver.Total.comp_def] using continuous_comp_prod
      (by simpa only [Quiver.Total.comp_def] using
        (IsTopologicalGroupoid.continuous_comp (C := C)))
      (by simpa only [Quiver.Total.comp_def] using
        (IsTopologicalGroupoid.continuous_comp (C := D)))

/-- The comma category `Comma L R` of two functors out of topological groupoids `A` and `B` into a
category `T` with topologized total arrows is a topological groupoid. Over a groupoid `T`, this
packages the weak fiber product of `L` and `R` as a topological groupoid without any continuity or
transversality assumption on `L`, `R`, or `T`. -/
instance IsTopologicalGroupoid.comma {A B T : Type*} [Category A] [IsGroupoid A]
    [Category B] [IsGroupoid B] [Category T] {L : A ⥤ T} {R : B ⥤ T}
    [TopologicalSpace A] [TopologicalSpace (Quiver.Total A)] [IsTopologicalGroupoid A]
    [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)] [IsTopologicalGroupoid B]
    [TopologicalSpace (Quiver.Total T)] : IsTopologicalGroupoid (Comma L R) where
  continuous_source := Comma.continuous_source
  continuous_target := Comma.continuous_target
  continuous_unit := Comma.continuous_unit IsTopologicalGroupoid.continuous_unit
    IsTopologicalGroupoid.continuous_unit
  continuous_inverse := Comma.continuous_inverse IsTopologicalGroupoid.continuous_inverse
    IsTopologicalGroupoid.continuous_inverse
  continuous_comp := by
    simpa only [Quiver.Total.comp_def] using Comma.continuous_comp (L := L) (R := R)
      (by simpa only [Quiver.Total.comp_def] using
        (IsTopologicalGroupoid.continuous_comp (C := A)))
      (by simpa only [Quiver.Total.comp_def] using
        (IsTopologicalGroupoid.continuous_comp (C := B)))

/-- A continuous group action gives a topological groupoid with arrow space homeomorphic
to `G × X`, not a discretization of that space. -/
instance ActionGroupoid.isTopologicalGroupoid (G X : Type*) [Group G] [MulAction G X]
    [TopologicalSpace G] [TopologicalSpace X] [IsTopologicalGroup G] [ContinuousSMul G X] :
    IsTopologicalGroupoid (ActionCategory G X) where
  continuous_source := ActionGroupoid.continuous_source G X
  continuous_target := ActionGroupoid.continuous_target G X
  continuous_unit := ActionGroupoid.continuous_unit G X
  continuous_inverse := ActionGroupoid.continuous_inverse G X
  continuous_comp := ActionGroupoid.continuous_comp G X

end TauCeti
