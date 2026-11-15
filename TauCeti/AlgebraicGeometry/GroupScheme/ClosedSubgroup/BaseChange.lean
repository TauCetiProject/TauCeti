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
import TauCeti.CategoryTheory.Limits.Shapes.Pullback.EqToHom

/-!
# Base change of closed subgroup schemes

Let `G` be a group scheme over `X` and `s : Y ⟶ X` a morphism of schemes. The base change of `G`
to `Y` is the group scheme `(Over.pullback s).mapGrp.obj G` over `Y`. This file shows that a closed
subgroup scheme `P` of `G` base-changes to a closed subgroup scheme of the base change of `G`: the
base change of a closed immersion of group schemes is again a closed immersion, since its
underlying morphism is the pullback of the original one along the projection
`G ×_X Y ⟶ G`.

Base change of closed subgroup schemes is compatible with identity morphisms (`pullbackIdIso`),
composition (`pullbackCompIso`), and equality of base morphisms (`congrIso`), so the two pullbacks
of `baseChange p P` to the self-fibre product `Y ×_X Y` correspond under the canonical overlap
isomorphism `overlapIso p G` (`mapIso_overlapIso_baseChange`).

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
* `TauCeti.ClosedSubgroupScheme.pullbackIdIso`, `TauCeti.ClosedSubgroupScheme.pullbackCompIso`,
  `TauCeti.ClosedSubgroupScheme.congrIso`, `TauCeti.ClosedSubgroupScheme.overlapIso`: canonical
  group-scheme isomorphisms witnessing functoriality of base change and overlap compatibility on
  `Y ×_X Y`, with `@[simp]` transport lemmas for `ClosedSubgroupScheme.mapIso`.
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

/-- The canonical isomorphism `(Over.pullback (𝟙 X)).mapGrp.obj G ≅ G` of group schemes over `X`. -/
noncomputable def pullbackIdIso (G : Grp (Over X)) :
    (Over.pullback (𝟙 X)).mapGrp.obj G ≅ G :=
  (Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso).app G

/-- Base change along the identity morphism fixes every closed subgroup scheme under
`pullbackIdIso`. -/
@[simp]
theorem mapIso_pullbackIdIso_baseChange (P : ClosedSubgroupScheme G) :
    mapIso (pullbackIdIso G) (baseChange (𝟙 X) P) = P := by
  refine Subtype.ext ?_
  rw [baseChange_def, mapIso_mk, coe_mk]
  exact (Subobject.mk_eq_mk_of_comm _ _ (pullbackIdIso (P.1 : Grp (Over X)))
    (by simp [pullbackIdIso])).trans (Subobject.mk_arrow P.1)

/-- The canonical isomorphism comparing iterated base change of a group scheme along `s : Y ⟶ X`
and `t : Z ⟶ Y` with base change along `t ≫ s`. -/
noncomputable def pullbackCompIso {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X) (G : Grp (Over X)) :
    (Over.pullback t).mapGrp.obj ((Over.pullback s).mapGrp.obj G) ≅
      (Over.pullback (t ≫ s)).mapGrp.obj G :=
  ((Functor.mapGrpNatIso (Over.pullbackComp t s) ≪≫ Functor.mapGrpCompIso).symm).app G

/-- Iterated base change of a closed subgroup scheme agrees with base change along the composite
morphism under `pullbackCompIso`. -/
@[simp]
theorem mapIso_pullbackCompIso_baseChange {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X)
    (P : ClosedSubgroupScheme G) :
    mapIso (pullbackCompIso t s G) (baseChange t (baseChange s P)) = baseChange (t ≫ s) P := by
  refine Subtype.ext ?_
  rw [baseChange_def s P, baseChange_mk, mapIso_mk, baseChange_def, coe_mk, coe_mk]
  have hnat :=
    ((Functor.mapGrpNatIso (Over.pullbackComp t s) ≪≫ Functor.mapGrpCompIso).symm).hom.naturality
      P.1.arrow
  exact Subobject.mk_eq_mk_of_comm _ _ (pullbackCompIso t s (P.1 : Grp (Over X)))
    (by simpa [pullbackCompIso] using hnat.symm)

/-- The canonical isomorphism between base changes of `G` along two equal morphisms `s₁ = s₂`. -/
noncomputable def congrIso {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂) (G : Grp (Over X)) :
    (Over.pullback s₁).mapGrp.obj G ≅ (Over.pullback s₂).mapGrp.obj G :=
  eqToIso (by subst h; rfl)

private theorem congrIso_hom_hom_hom {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂) (G : Grp (Over X)) :
    (congrIso h G).hom.hom.hom =
      eqToHom (congrArg (fun f ↦ (Over.pullback f).obj G.X) h) := by
  subst h
  simp only [congrIso, eqToIso.hom, eqToHom_refl]
  rfl

/-- Transporting `baseChange s₁ P` along `congrIso h G` yields `baseChange s₂ P`. -/
@[simp]
theorem mapIso_congrIso_baseChange {s₁ s₂ : Y ⟶ X} (h : s₁ = s₂)
    (P : ClosedSubgroupScheme G) :
    mapIso (congrIso h G) (baseChange s₁ P) = baseChange s₂ P := by
  subst h
  ext1
  simp [congrIso, Subobject.map_id]

/-- The canonical overlap isomorphism on `Y ×_X Y` between the two pullbacks of the base-changed
group scheme `(Over.pullback p).mapGrp.obj G` along `pullback.fst p p` and `pullback.snd p p`. -/
noncomputable def overlapIso (p : Y ⟶ X) (G : Grp (Over X)) :
    (Over.pullback (pullback.fst p p)).mapGrp.obj ((Over.pullback p).mapGrp.obj G) ≅
      (Over.pullback (pullback.snd p p)).mapGrp.obj ((Over.pullback p).mapGrp.obj G) :=
  pullbackCompIso (pullback.fst p p) p G ≪≫ congrIso pullback.condition G ≪≫
    (pullbackCompIso (pullback.snd p p) p G).symm

private theorem pullbackCompIso_hom_hom_hom {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X)
    (G : Grp (Over X)) :
    (pullbackCompIso t s G).hom.hom.hom = (Over.pullbackComp t s).inv.app G.X := by
  simp only [pullbackCompIso]
  exact Category.id_comp _

private theorem pullbackCompIso_inv_hom_hom {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X)
    (G : Grp (Over X)) :
    (pullbackCompIso t s G).inv.hom.hom = (Over.pullbackComp t s).hom.app G.X := by
  simp only [pullbackCompIso]
  exact Category.comp_id _

private theorem pullbackComp_hom_fst_fst {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X) (A : Over X) :
    ((Over.pullbackComp t s).hom.app A).left ≫
        pullback.fst ((Over.pullback s).obj A).hom t ≫ pullback.fst A.hom s =
      pullback.fst A.hom (t ≫ s) := by
  simp [Over.pullbackComp]

private theorem pullbackComp_hom_fst_snd {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X) (A : Over X) :
    ((Over.pullbackComp t s).hom.app A).left ≫
        pullback.fst ((Over.pullback s).obj A).hom t ≫ pullback.snd A.hom s =
      pullback.snd A.hom (t ≫ s) ≫ t := by
  simp [Over.pullbackComp]

private theorem pullbackComp_inv_fst {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X) (A : Over X) :
    ((Over.pullbackComp t s).inv.app A).left ≫ pullback.fst A.hom (t ≫ s) =
      pullback.fst ((Over.pullback s).obj A).hom t ≫ pullback.fst A.hom s := by
  simp [Over.pullbackComp]

@[reassoc]
private theorem pullbackComp_inv_snd {Z : Scheme.{u}} (t : Z ⟶ Y) (s : Y ⟶ X) (A : Over X) :
    ((Over.pullbackComp t s).inv.app A).left ≫ pullback.snd A.hom (t ≫ s) =
      pullback.snd ((Over.pullback s).obj A).hom t := by
  simp [Over.pullbackComp]

private theorem overlapOver_left_fst (p : Y ⟶ X) (A : Over X) :
    (((Over.pullbackComp (pullback.fst p p) p).inv.app A).left ≫
        eqToHom (congrArg (fun f ↦ pullback A.hom f) (pullback.condition (f := p) (g := p))) ≫
        ((Over.pullbackComp (pullback.snd p p) p).hom.app A).left) ≫
      pullback.fst ((Over.pullback p).obj A).hom (pullback.snd p p) =
      pullback.lift
        (pullback.fst ((Over.pullback p).obj A).hom (pullback.fst p p) ≫ pullback.fst A.hom p)
        (pullback.snd ((Over.pullback p).obj A).hom (pullback.fst p p) ≫ pullback.snd p p)
        (by
          rw [Category.assoc, pullback.condition, ← Over.pullback_obj_hom p A,
            pullback.condition_assoc, pullback.condition, Category.assoc]) := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullback.lift_fst, Category.assoc, Category.assoc, Category.assoc,
      pullbackComp_hom_fst_fst,
      eqToHom_comp_pullback_fst A.hom (pullback.condition (f := p) (g := p)),
      pullbackComp_inv_fst]
  · rw [pullback.lift_snd, Category.assoc, Category.assoc, Category.assoc,
      pullbackComp_hom_fst_snd,
      eqToHom_comp_pullback_snd_assoc A.hom (pullback.condition (f := p) (g := p)),
      pullbackComp_inv_snd_assoc]

/-- On underlying schemes, `overlapIso p G` sends `((g, y₁), (y₁, y₂))` in
`(G ×_X Y) ×_Y (Y ×_X Y)` to `((g, y₂), (y₁, y₂))`: its first projection to `G ×_X Y` pairs the
`G`-coordinate `g` with the second `Y`-coordinate `y₂`. -/
@[reassoc]
theorem overlapIso_hom_left_fst (p : Y ⟶ X) (G : Grp (Over X)) :
    (overlapIso p G).hom.hom.hom.left ≫
        pullback.fst ((Over.pullback p).obj G.X).hom (pullback.snd p p) =
      pullback.lift
        (pullback.fst ((Over.pullback p).obj G.X).hom (pullback.fst p p) ≫
          pullback.fst G.X.hom p)
        (pullback.snd ((Over.pullback p).obj G.X).hom (pullback.fst p p) ≫
          pullback.snd p p)
        (by
          rw [Category.assoc, pullback.condition, ← Over.pullback_obj_hom p G.X,
            pullback.condition_assoc, pullback.condition, Category.assoc]) := by
  have hhom : (overlapIso p G).hom.hom.hom =
      (Over.pullbackComp (pullback.fst p p) p).inv.app G.X ≫
        eqToHom (congrArg (fun f ↦ (Over.pullback f).obj G.X)
          (pullback.condition (f := p) (g := p))) ≫
        (Over.pullbackComp (pullback.snd p p) p).hom.app G.X := by
    simp only [overlapIso, Iso.trans_hom, Iso.symm_hom, Grp.comp', Mon.comp_hom',
      pullbackCompIso_hom_hom_hom, congrIso_hom_hom_hom, pullbackCompIso_inv_hom_hom]
    rfl
  have hleft : (overlapIso p G).hom.hom.hom.left =
      ((Over.pullbackComp (pullback.fst p p) p).inv.app G.X).left ≫
        eqToHom (congrArg (fun f ↦ pullback G.X.hom f)
          (pullback.condition (f := p) (g := p))) ≫
        ((Over.pullbackComp (pullback.snd p p) p).hom.app G.X).left := by
    refine (congrArg Over.Hom.left hhom).trans ?_
    simp only [Over.comp_left, Over.eqToHom_left]
    rfl
  exact (congrArg (· ≫ pullback.fst ((Over.pullback p).obj G.X).hom (pullback.snd p p))
    hleft).trans (overlapOver_left_fst p G.X)

/-- The two pullbacks to `Y ×_X Y` of the base change `baseChange p P` of any closed subgroup
scheme `P` of `G` agree under `overlapIso p G`. -/
@[simp]
theorem mapIso_overlapIso_baseChange (p : Y ⟶ X) (P : ClosedSubgroupScheme G) :
    mapIso (overlapIso p G) (baseChange (pullback.fst p p) (baseChange p P)) =
      baseChange (pullback.snd p p) (baseChange p P) := by
  apply (mapIso (pullbackCompIso (pullback.snd p p) p G)).injective
  rw [overlapIso, mapIso_trans, mapIso_trans, ← mapIso_trans _ _ (mapIso _ _), Iso.symm_self_id,
    mapIso_pullbackCompIso_baseChange, mapIso_congrIso_baseChange,
    mapIso_pullbackCompIso_baseChange]
  ext1
  simp [Subobject.map_id]

end Functoriality

end TauCeti.ClosedSubgroupScheme
