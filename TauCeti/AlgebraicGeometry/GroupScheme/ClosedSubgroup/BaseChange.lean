/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.Basic
public import TauCeti.CategoryTheory.Comma.Over

/-!
# Base change of closed subgroup schemes

Let `G` be a group scheme over `X` and `s : Y ⟶ X` a morphism of schemes. The base change of `G`
to `Y` is the group scheme `(Over.pullback s).mapGrp.obj G` over `Y`. This file shows that a closed
subgroup scheme `P` of `G` base-changes to a closed subgroup scheme of the base change of `G`: the
base change of a closed immersion of group schemes is again a closed immersion, since its
underlying morphism is the pullback of the original one along the projection
`G ×_X Y ⟶ G`.

Base change of closed subgroup schemes is compatible with identity morphisms
(`Grp.pullbackIdIso`), composition (`Grp.pullbackCompIso`), and equality of base morphisms
(`Grp.pullbackCongrIso`), so the two pullbacks of `baseChange p P` to the self-fibre product
`Y ×_X Y` correspond under the canonical overlap isomorphism `Grp.pullbackOverlapIso p G`
(`mapIso_pullbackOverlapIso_baseChange`).

## Main declarations

* `TauCeti.ClosedSubgroupScheme.baseChange s P`: the base change of a closed subgroup scheme `P`
  of `G` along `s`, a closed subgroup scheme of the base change of `G`.
* `TauCeti.ClosedSubgroupScheme.baseChange_mk`: the base change of the closed subgroup scheme
  represented by a closed immersion `i` is represented by the base change of `i`.
* `TauCeti.ClosedSubgroupScheme.baseChange_mono`: base change preserves inclusions of closed
  subgroup schemes.
* `TauCeti.ClosedSubgroupScheme.baseChangeCarrierIso` and
  `TauCeti.ClosedSubgroupScheme.isPullback_baseChange_hom`: the scheme underlying `baseChange s P`
  is isomorphic to the pullback of the scheme underlying `P` along `s`.
* `TauCeti.ClosedSubgroupScheme.mapIso_pullbackIdIso_baseChange`,
  `TauCeti.ClosedSubgroupScheme.mapIso_pullbackCompIso_baseChange`,
  `TauCeti.ClosedSubgroupScheme.mapIso_pullbackCongrIso_baseChange`,
  `TauCeti.ClosedSubgroupScheme.mapIso_pullbackOverlapIso_baseChange`: `@[simp]` transport lemmas
  relating `baseChange` to the canonical pullback isomorphisms of `CategoryTheory.Grp`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.ClosedSubgroupScheme

universe u

variable {X Y : Scheme.{u}} (s : Y ⟶ X) {G K : Grp (Over X)}

/-- The base change of a closed immersion of group schemes is a closed immersion. -/
instance isClosedImmersion_pullback_mapGrp_map (i : K ⟶ G) [IsClosedImmersion i.hom.hom.left] :
    IsClosedImmersion ((Over.pullback s).mapGrp.map i).hom.hom.left :=
  MorphismProperty.of_isPullback (Over.isPullback_pullback_map_left s i.hom.hom).flip
    inferInstance

/-- The **base change of a closed subgroup scheme** `P` of `G` along `s : Y ⟶ X`: the closed
subgroup scheme of the base change `(Over.pullback s).mapGrp.obj G` represented by the base change
of the inclusion of `P`. -/
noncomputable def baseChange (P : ClosedSubgroupScheme G) :
    ClosedSubgroupScheme ((Over.pullback s).mapGrp.obj G) :=
  mk ((Over.pullback s).mapGrp.map P.1.arrow)

/-- The base change of `P` is represented by the base change of the inclusion of `P`. -/
theorem baseChange_def (P : ClosedSubgroupScheme G) :
    baseChange s P = mk ((Over.pullback s).mapGrp.map P.1.arrow) :=
  (rfl)

/-- The base change of the closed subgroup scheme represented by a closed immersion `i` is
represented by the base change of `i`. -/
@[simp]
theorem baseChange_mk (i : K ⟶ G) [IsClosedImmersion i.hom.hom.left] :
    baseChange s (mk i) = mk ((Over.pullback s).mapGrp.map i) := by
  refine Subtype.ext ?_
  rw [coe_mk, baseChange_def, coe_mk]
  refine Subobject.mk_eq_mk_of_comm _ _ ((Over.pullback s).mapGrp.mapIso (mkIso i)) ?_
  rw [Functor.mapIso_hom, ← Functor.map_comp, ← (Iso.inv_comp_eq _).1 (mkIso_inv_comp_arrow i)]

/-- Base change preserves inclusions of closed subgroup schemes. -/
theorem baseChange_mono : Monotone (baseChange (G := G) s) := by
  intro P Q h
  refine Subtype.coe_le_coe.1 ?_
  rw [baseChange_def, baseChange_def, coe_mk, coe_mk]
  exact Subobject.mk_le_mk_of_comm
    ((Over.pullback s).mapGrp.map (Subobject.ofLE _ _ (Subtype.coe_le_coe.2 h)))
    (by rw [← Functor.map_comp, Subobject.ofLE_arrow])

/-- The canonical isomorphism between the group scheme underlying `baseChange s P` and the
base-changed group scheme `(Over.pullback s).mapGrp.obj (P.1 : Grp (Over X))`. -/
noncomputable def baseChangeCarrierIso (P : ClosedSubgroupScheme G) :
    ((baseChange s P).1 : Grp (Over Y)) ≅ (Over.pullback s).mapGrp.obj (P.1 : Grp (Over X)) :=
  mkIso ((Over.pullback s).mapGrp.map P.1.arrow)

/-- The inverse of `baseChangeCarrierIso` intertwines the inclusion of `baseChange s P` with the
base-changed inclusion of `P`. -/
@[simp]
theorem baseChangeCarrierIso_inv_comp_arrow (P : ClosedSubgroupScheme G) :
    (baseChangeCarrierIso s P).inv ≫ (baseChange s P).1.arrow =
      (Over.pullback s).mapGrp.map P.1.arrow :=
  mkIso_inv_comp_arrow ((Over.pullback s).mapGrp.map P.1.arrow)

/-- The structure morphism to `Y` of `baseChange s P` factors through the second pullback
projection via `baseChangeCarrierIso s P`. -/
@[reassoc]
theorem baseChangeCarrierIso_hom_left_snd (P : ClosedSubgroupScheme G) :
    (baseChangeCarrierIso s P).hom.hom.hom.left ≫ pullback.snd (P.1 : Grp (Over X)).X.hom s =
      ((baseChange s P).1 : Grp (Over Y)).X.hom :=
  Over.w (baseChangeCarrierIso s P).hom.hom.hom

/-- `baseChangeCarrierIso s P` exhibits the structure morphism to `Y` of `baseChange s P` as a
pullback of the structure morphism to `X` of `P` along `s`. -/
theorem isPullback_baseChange_hom (P : ClosedSubgroupScheme G) :
    IsPullback ((baseChange s P).1 : Grp (Over Y)).X.hom
      ((baseChangeCarrierIso s P).hom.hom.hom.left ≫ pullback.fst (P.1 : Grp (Over X)).X.hom s)
      s (P.1 : Grp (Over X)).X.hom := by
  let e : ((baseChange s P).1 : Grp (Over Y)).X.left ≅ pullback (P.1 : Grp (Over X)).X.hom s :=
    (Grp.forget (Over Y) ⋙ Over.forget Y).mapIso (baseChangeCarrierIso s P)
  exact (IsPullback.of_hasPullback (P.1 : Grp (Over X)).X.hom s).flip.of_iso
    e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      rw [Iso.refl_hom, Category.comp_id, ← baseChangeCarrierIso_hom_left_snd]
      exact (e.inv_hom_id_assoc _).symm)
    (by rw [Iso.refl_hom, Category.comp_id]; exact (e.inv_hom_id_assoc _).symm)
    (by simp) (by simp)

section Functoriality

/-- Base change along the identity morphism fixes every closed subgroup scheme under
`Grp.pullbackIdIso`. -/
@[simp]
theorem mapIso_pullbackIdIso_baseChange (P : ClosedSubgroupScheme G) :
    mapIso (Grp.pullbackIdIso G) (baseChange (𝟙 X) P) = P := by
  refine Subtype.ext ?_
  rw [baseChange_def, mapIso_mk, coe_mk]
  exact (Subobject.mk_eq_mk_of_comm _ _ (Grp.pullbackIdIso (P.1 : Grp (Over X)))
    (Grp.pullbackIdIso_hom_naturality P.1.arrow).symm).trans (Subobject.mk_arrow P.1)

/-- Iterated base change of a closed subgroup scheme agrees with base change along the composite
morphism under `Grp.pullbackCompIso`. -/
@[simp]
theorem mapIso_pullbackCompIso_baseChange {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X)
    (P : ClosedSubgroupScheme G) :
    mapIso (Grp.pullbackCompIso t s G) (baseChange t (baseChange s P)) = baseChange (t ≫ s) P := by
  refine Subtype.ext ?_
  rw [baseChange_def s P, baseChange_mk, mapIso_mk, baseChange_def, coe_mk, coe_mk]
  exact Subobject.mk_eq_mk_of_comm _ _ (Grp.pullbackCompIso t s (P.1 : Grp (Over X)))
    (Grp.pullbackCompIso_hom_naturality t s P.1.arrow).symm

/-- Transporting `baseChange s₁ P` along `Grp.pullbackCongrIso h G` yields `baseChange s₂ P`. -/
@[simp]
theorem mapIso_pullbackCongrIso_baseChange {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂)
    (P : ClosedSubgroupScheme G) :
    mapIso (Grp.pullbackCongrIso h G) (baseChange s₁ P) = baseChange s₂ P := by
  subst h
  ext1
  simp [Subobject.map_id]

/-- The two pullbacks to `Y ×_X Y` of the base change `baseChange p P` of any closed subgroup
scheme `P` of `G` agree under `Grp.pullbackOverlapIso p G`. -/
@[simp]
theorem mapIso_pullbackOverlapIso_baseChange (p : Y ⟶ X) (P : ClosedSubgroupScheme G) :
    mapIso (Grp.pullbackOverlapIso p G) (baseChange (pullback.fst p p) (baseChange p P)) =
      baseChange (pullback.snd p p) (baseChange p P) := by
  refine Subtype.ext ?_
  rw [baseChange_def p P, baseChange_mk, baseChange_mk, mapIso_mk, coe_mk, coe_mk]
  exact Subobject.mk_eq_mk_of_comm _ _ (Grp.pullbackOverlapIso p (P.1 : Grp (Over X)))
    (Grp.pullbackOverlapIso_hom_naturality p P.1.arrow).symm

end Functoriality

end TauCeti.ClosedSubgroupScheme
