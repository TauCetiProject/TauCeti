/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Closed subgroup schemes

This file defines closed subgroup schemes of a group scheme over an arbitrary base scheme. A
closed subgroup scheme is a categorical subobject whose representative arrow is a closed
immersion on underlying schemes. Pulling the closed-immersion property back through the two
forgetful functors makes the condition independent of the chosen representative.

Neither the base nor the group scheme is required to be affine. Affineness enters only in
specialized constructions that import this generic API.

## Main declarations

* `TauCeti.closedSubgroupMorphismProperty`: the closed-immersion property for morphisms of group
  schemes.
* `TauCeti.ClosedSubgroupScheme`: closed subgroup subobjects of a group scheme.
* `TauCeti.ClosedSubgroupScheme.mk`: the closed subgroup represented by a closed immersion.
* `TauCeti.ClosedSubgroupScheme.mkIso`: the canonical isomorphism of that closed subgroup with the
  source of the immersion.
* `TauCeti.ClosedSubgroupScheme.mapIso`: transport of closed subgroups along an isomorphism of
  ambient group schemes.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

open AlgebraicGeometry

/-- The property of a morphism of group schemes that its underlying scheme morphism is a closed
immersion. Pulling the property back along the two forgetful functors makes its invariance under
isomorphisms available from the generic morphism-property API. -/
def closedSubgroupMorphismProperty (X : Scheme.{u}) :
    MorphismProperty (Grp (Over X)) :=
  MorphismProperty.inverseImage (@IsClosedImmersion) (Grp.forget _ ⋙ Over.forget _)

/-- The underlying closed-immersion property is invariant under isomorphisms of group schemes. -/
instance closedSubgroupMorphismProperty_respectsIso (X : Scheme.{u}) :
    (closedSubgroupMorphismProperty X).RespectsIso := by
  unfold closedSubgroupMorphismProperty
  let _ : MorphismProperty.RespectsIso (@IsClosedImmersion) :=
    AlgebraicGeometry.IsClosedImmersion.respectsIso
  exact MorphismProperty.RespectsIso.inverseImage (@IsClosedImmersion)
    (Grp.forget _ ⋙ Over.forget _)

/-- A group-scheme morphism whose underlying scheme morphism is a closed immersion is a
monomorphism. -/
instance (priority := 900) mono_of_isClosedImmersion_underlying {X : Scheme.{u}}
    {G K : Grp (Over X)} (f : G ⟶ K) [IsClosedImmersion f.hom.hom.left] : Mono f := by
  apply (Grp.forget _ ⋙ Over.forget _).mono_of_mono_map
  -- The composite forgetful functor maps `f` to `f.hom.hom.left`; its source and target are
  -- definitionally the underlying schemes, so the dependent `Mono` proposition needs this
  -- conversion after reflecting monomorphisms.
  change Mono f.hom.hom.left
  infer_instance

/-- A morphism has `closedSubgroupMorphismProperty` exactly when its underlying scheme morphism is
a closed immersion. -/
@[simp]
lemma closedSubgroupMorphismProperty_iff (X : Scheme.{u})
    {G K : Grp (Over X)} (f : G ⟶ K) :
    closedSubgroupMorphismProperty X f ↔ IsClosedImmersion f.hom.hom.left := by
  unfold closedSubgroupMorphismProperty MorphismProperty.inverseImage
  rfl

/-- A closed subgroup scheme of `G` is a categorical subobject represented by a closed immersion
on underlying schemes. The use of `Subobject` identifies presentations isomorphic over `G`. -/
abbrev ClosedSubgroupScheme {X : Scheme.{u}} (G : Grp (Over X)) : Type _ :=
  {P : Subobject G // closedSubgroupMorphismProperty X P.arrow}

namespace ClosedSubgroupScheme

variable {X : Scheme.{u}} {G : Grp (Over X)}

/-- Construct a closed subgroup scheme from a morphism whose underlying scheme morphism is a
closed immersion. -/
noncomputable def mk {K : Grp (Over X)} (i : K ⟶ G)
    [IsClosedImmersion i.hom.hom.left] : ClosedSubgroupScheme G :=
  ⟨Subobject.mk i, by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk i,
      (closedSubgroupMorphismProperty X).cancel_left_of_respectsIso]
    exact (closedSubgroupMorphismProperty_iff X i).2 inferInstance⟩

/-- The subobject underlying a closed subgroup scheme constructed from an explicit arrow is the
subobject represented by that arrow. -/
@[simp]
lemma coe_mk {K : Grp (Over X)} (i : K ⟶ G)
    [IsClosedImmersion i.hom.hom.left] :
    (mk i).1 = Subobject.mk i :=
  by
    unfold mk
    rfl

/-- The closed subgroup represented by a closed immersion is canonically isomorphic to the source
of that immersion. -/
noncomputable def mkIso {K : Grp (Over X)} (i : K ⟶ G)
    [IsClosedImmersion i.hom.hom.left] :
    ((mk i).1 : Grp (Over X)) ≅ K :=
  eqToIso (congrArg (fun P : Subobject G => (P : Grp (Over X))) (coe_mk i)) ≪≫
    Subobject.underlyingIso i

/-- The canonical parametrization of a closed subgroup followed by its inclusion is the closed
immersion representing it. -/
@[simp]
lemma mkIso_inv_comp_arrow {K : Grp (Over X)} (i : K ⟶ G)
    [IsClosedImmersion i.hom.hom.left] :
    (mkIso i).inv ≫ (mk i).1.arrow = i := by
  have harrow :
      (eqToIso (congrArg (fun P : Subobject G => (P : Grp (Over X))) (coe_mk i))).inv ≫
          (mk i).1.arrow =
        (Subobject.mk i).arrow :=
    Subobject.arrow_congr (Subobject.mk i) (mk i).1 (coe_mk i).symm
  rw [mkIso, Iso.trans_inv, Category.assoc, harrow, Subobject.underlyingIso_arrow]

/-- Transporting a subobject along an isomorphism of ambient group schemes preserves the
closed-immersion property of its representing arrow. -/
private lemma closedSubgroupMorphismProperty_map_arrow {H : Grp (Over X)} (e : G ≅ H)
    {P : Subobject G} (hP : closedSubgroupMorphismProperty X P.arrow) :
    closedSubgroupMorphismProperty X ((Subobject.map e.hom).obj P).arrow := by
  induction P using Subobject.ind with
  | _ f =>
    rw [← Subobject.underlyingIso_hom_comp_eq_mk f,
      (closedSubgroupMorphismProperty X).cancel_left_of_respectsIso] at hP
    rw [Subobject.map_mk, ← Subobject.underlyingIso_hom_comp_eq_mk (f ≫ e.hom),
      (closedSubgroupMorphismProperty X).cancel_left_of_respectsIso,
      (closedSubgroupMorphismProperty X).cancel_right_of_respectsIso]
    exact hP

/-- Mathlib's `Subobject.mapIsoToOrderIso_symm_apply` is stated for `RelIso.symm`, which does not
match the `OrderIso.symm` of `Subobject.mapIsoToOrderIso` syntactically; this restates it. -/
private lemma mapIsoToOrderIso_symm_apply {H : Grp (Over X)} (e : G ≅ H) (P : Subobject H) :
    (Subobject.mapIsoToOrderIso e).symm P = (Subobject.map e.inv).obj P :=
  Subobject.mapIsoToOrderIso_symm_apply e P

/-- Closed subgroups are transported along an isomorphism of ambient group schemes by
postcomposing their representing arrows with the isomorphism. -/
noncomputable def mapIso {H : Grp (Over X)} (e : G ≅ H) :
    ClosedSubgroupScheme G ≃o ClosedSubgroupScheme H where
  toFun P := ⟨Subobject.mapIsoToOrderIso e P.1, by
    rw [Subobject.mapIsoToOrderIso_apply]
    exact closedSubgroupMorphismProperty_map_arrow e P.2⟩
  invFun P := ⟨(Subobject.mapIsoToOrderIso e).symm P.1, by
    rw [mapIsoToOrderIso_symm_apply]
    exact closedSubgroupMorphismProperty_map_arrow e.symm P.2⟩
  left_inv P := Subtype.ext ((Subobject.mapIsoToOrderIso e).symm_apply_apply P.1)
  right_inv P := Subtype.ext ((Subobject.mapIsoToOrderIso e).apply_symm_apply P.1)
  map_rel_iff' := (Subobject.mapIsoToOrderIso e).map_rel_iff

/-- The subobject underlying a transported closed subgroup is the transported subobject. -/
@[simp]
lemma coe_mapIso {H : Grp (Over X)} (e : G ≅ H) (P : ClosedSubgroupScheme G) :
    (mapIso e P).1 = Subobject.mapIsoToOrderIso e P.1 := by
  -- `mapIso` is not exposed, so it is unfolded first; its `toFun` is this subobject by definition.
  unfold mapIso
  rfl

/-- Postcomposing a closed immersion with an isomorphism of group schemes gives a closed
immersion. -/
instance isClosedImmersion_comp_iso_hom {H K : Grp (Over X)} (i : K ⟶ G)
    [IsClosedImmersion i.hom.hom.left] (e : G ≅ H) :
    IsClosedImmersion (i ≫ e.hom).hom.hom.left := by
  rw [← closedSubgroupMorphismProperty_iff,
    (closedSubgroupMorphismProperty X).cancel_right_of_respectsIso,
    closedSubgroupMorphismProperty_iff]
  infer_instance

/-- Transporting the closed subgroup represented by a closed immersion along an isomorphism gives
the closed subgroup represented by the composite. -/
@[simp]
lemma mapIso_mk {H K : Grp (Over X)} (e : G ≅ H) (i : K ⟶ G)
    [IsClosedImmersion i.hom.hom.left] :
    mapIso e (mk i) = mk (i ≫ e.hom) :=
  Subtype.ext (by
    rw [coe_mapIso, coe_mk, coe_mk, Subobject.mapIsoToOrderIso_apply, Subobject.map_mk])

/-- The subobject underlying a closed subgroup transported back along an isomorphism is the
subobject transported back along it. -/
@[simp]
lemma coe_mapIso_symm {H : Grp (Over X)} (e : G ≅ H) (P : ClosedSubgroupScheme H) :
    ((mapIso e).symm P).1 = (Subobject.mapIsoToOrderIso e).symm P.1 := by
  -- `mapIso` is not exposed, so it is unfolded first; its `invFun` is this subobject by
  -- definition.
  unfold mapIso
  rfl

/-- Postcomposing a closed immersion with the inverse of an isomorphism of group schemes gives a
closed immersion. -/
instance isClosedImmersion_comp_iso_inv {H K : Grp (Over X)} (i : K ⟶ H)
    [IsClosedImmersion i.hom.hom.left] (e : G ≅ H) :
    IsClosedImmersion (i ≫ e.inv).hom.hom.left :=
  isClosedImmersion_comp_iso_hom i e.symm

/-- Transporting the closed subgroup represented by a closed immersion back along an isomorphism
gives the closed subgroup represented by the composite with the inverse. -/
@[simp]
lemma mapIso_symm_mk {H K : Grp (Over X)} (e : G ≅ H) (i : K ⟶ H)
    [IsClosedImmersion i.hom.hom.left] :
    (mapIso e).symm (mk i) = mk (i ≫ e.inv) :=
  Subtype.ext (by
    rw [coe_mapIso_symm, coe_mk, coe_mk, mapIsoToOrderIso_symm_apply, Subobject.map_mk])

end ClosedSubgroupScheme

end TauCeti
