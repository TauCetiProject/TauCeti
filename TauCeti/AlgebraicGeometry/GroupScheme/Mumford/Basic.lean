/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Mumford.Class
public import TauCeti.AlgebraicGeometry.LineBundle.Rigidified.Basic
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms

/-!
# The normalized Mumford line bundle

For a monoid scheme `G` over `S` with unit section `e` and a line bundle `L` on `G`, the normalized
Mumford line bundle on `G ×_S G` is `(m^*L ⊗ π^*e^*L) ⊗ (p₁^*L⁻¹ ⊗ p₂^*L⁻¹)`. Here `m` is
multiplication, `p₁` and `p₂` are the projections, and `π` is the structure morphism of the
product. The base correction gives evaluation trivializations along both embeddings of `G`
obtained by inserting the unit. Normalize the second by a scalar from the base so that they agree
when restricted to `(e, e)`.

For an abelian scheme this is the bundle used to define the Mumford map to the dual abelian
scheme. Its construction here uses only the monoid structure.

## References

* G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Chapter I, §1.
* B. Conrad, *Polarizations*, Example 2.2.
-/

public section

open CategoryTheory CartesianMonoidalCategory MonoidalCategory MonObj AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open InvertibleSheaf

universe u

namespace TauCeti.GroupScheme

noncomputable section

variable {S : Scheme.{u}} (G : Over S) [MonObj G]

/-- The normalized Mumford line bundle `(m^*L ⊗ π^*e^*L) ⊗ (p₁^*L⁻¹ ⊗ p₂^*L⁻¹)` on the product of
`G` with itself over the base. The second factor is the pullback of the fibre of `L` at the unit. -/
def mumfordLineBundle (L : InvertibleSheaf G.left) : InvertibleSheaf (G ⊗ G).left :=
  (((pullback μ[G].left).obj L) ⊗ ((pullback (toUnit (G ⊗ G) ≫ η[G]).left).obj L)) ⊗
    (((pullback (fst G G).left).obj L.dual) ⊗ ((pullback (snd G G).left).obj L.dual))

/-- The class of the normalized Mumford line bundle in the Picard group of the product. -/
@[simp]
theorem mk_mumfordLineBundle (L : InvertibleSheaf G.left) :
    LineBundleClass.mk (mumfordLineBundle G L) = mumfordClass G (LineBundleClass.mk L) := by
  simp only [mumfordClass_apply, mumfordLineBundle, LineBundleClass.mk_tensorObj,
    ← LineBundleClass.pullback_mk, ← LineBundleClass.inv_mk, LineBundleClass.pullback_inv,
    div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- Pulling back the Mumford line bundle along `i` gives the four factors pulled back along
the corresponding composites with `i`. -/
def pullbackMumfordLineBundleIso {T : Scheme.{u}} (i : T ⟶ (G ⊗ G).left)
    (L : InvertibleSheaf G.left) :
    (pullback i).obj (mumfordLineBundle G L) ≅
      (((pullback (i ≫ μ[G].left)).obj L) ⊗
        ((pullback (i ≫ (toUnit (G ⊗ G) ≫ η[G]).left)).obj L)) ⊗
      (((pullback (i ≫ (fst G G).left)).obj L.dual) ⊗
        ((pullback (i ≫ (snd G G).left)).obj L.dual)) := by
  let F := pullback i
  let A := (pullback μ[G].left).obj L
  let B := (pullback (toUnit (G ⊗ G) ≫ η[G]).left).obj L
  let C := (pullback (fst G G).left).obj L.dual
  let D := (pullback (snd G G).left).obj L.dual
  exact (Functor.Monoidal.μIso F (A ⊗ B) (C ⊗ D)).symm ≪≫
    (((Functor.Monoidal.μIso F A B).symm ≪≫
      ((pullbackComp i μ[G].left).app L ⊗ᵢ
        (pullbackComp i (toUnit (G ⊗ G) ≫ η[G]).left).app L)) ⊗ᵢ
      ((Functor.Monoidal.μIso F C D).symm ≪≫
        ((pullbackComp i (fst G G).left).app L.dual ⊗ᵢ
          (pullbackComp i (snd G G).left).app L.dual)))

/-- The evaluation trivialization that pairs `L` and the constant pullback of its fibre
at the unit with their respective duals. -/
def mumfordAxisEvaluation (L : InvertibleSheaf G.left) :
    ((pullback (𝟙 G.left)).obj L ⊗ (pullback (toUnit G ≫ η[G]).left).obj L) ⊗
      ((pullback (𝟙 G.left)).obj L.dual ⊗ (pullback (toUnit G ≫ η[G]).left).obj L.dual) ≅
      𝟙_ (InvertibleSheaf G.left) := by
  let F := pullback (toUnit G ≫ η[G]).left
  let A := (pullback (𝟙 G.left)).obj L
  let C := (pullback (𝟙 G.left)).obj L.dual
  let evaluation :=
    (tensorProductIsoTensor L L.dual).symm ≪≫ tensorDualIso L ≪≫ trivialIsoTensorUnit G.left
  exact
    (Functor.Monoidal.μIso (tensor (InvertibleSheaf G.left)) (A, F.obj L) (C, F.obj L.dual)) ≪≫
      ((((pullbackId G.left).app L ⊗ᵢ (pullbackId G.left).app L.dual) ≪≫
        evaluation) ⊗ᵢ
        (Functor.Monoidal.μIso F L L.dual ≪≫ F.mapIso evaluation ≪≫
          (Functor.Monoidal.εIso F).symm)) ≪≫ λ_ _

private def mumfordLineBundleFstEvaluation (L : InvertibleSheaf G.left) :
    (pullback (lift (𝟙 G) (toUnit G ≫ η[G])).left).obj (mumfordLineBundle G L) ≅
      𝟙_ (InvertibleSheaf G.left) :=
  pullbackMumfordLineBundleIso G _ L ≪≫
    eqToIso (by simp only [← Over.comp_left, lift_comp_one_right, lift_fst, lift_snd,
      comp_toUnit_assoc, Over.id_left]) ≪≫ mumfordAxisEvaluation G L

private def mumfordLineBundleSndEvaluation (L : InvertibleSheaf G.left) :
    (pullback (lift (toUnit G ≫ η[G]) (𝟙 G)).left).obj (mumfordLineBundle G L) ≅
      𝟙_ (InvertibleSheaf G.left) :=
  pullbackMumfordLineBundleIso G _ L ≪≫
    eqToIso (by simp only [← Over.comp_left, lift_comp_one_left, lift_fst, lift_snd,
      comp_toUnit_assoc, Over.id_left]) ≪≫
    (Iso.refl _ ⊗ᵢ (β_ _ _)) ≪≫ mumfordAxisEvaluation G L

open AlgebraicGeometry.Scheme.Modules

/-- The rigidification along `x ↦ (x, 1)` pairs `L` and its fibre at the unit with
their respective duals. -/
def mumfordLineBundleFstRigidification (L : InvertibleSheaf G.left) :
    (Scheme.Modules.pullback (lift (𝟙 G) (toUnit G ≫ η[G])).left).obj
      (mumfordLineBundle G L).obj ≅ 𝟙_ G.left.Modules :=
  (eqToIso (InvertibleSheaf.pullback_obj_obj (lift (𝟙 G) (toUnit G ≫ η[G])).left _)).symm ≪≫
    (SheafOfModules.isInvertible G.left).ι.mapIso (mumfordLineBundleFstEvaluation G L)

/-- On the first axis, the four pullback factors are identified with the factors of the
axis evaluation trivialization. -/
theorem mumfordLineBundleFstRigidification_def (L : InvertibleSheaf G.left) :
    mumfordLineBundleFstRigidification G L =
      (eqToIso (InvertibleSheaf.pullback_obj_obj (lift (𝟙 G) (toUnit G ≫ η[G])).left _)).symm ≪≫
        (SheafOfModules.isInvertible G.left).ι.mapIso
          (pullbackMumfordLineBundleIso G _ L ≪≫
            eqToIso (by simp only [← Over.comp_left, lift_comp_one_right, lift_fst, lift_snd,
              comp_toUnit_assoc, Over.id_left]) ≪≫ mumfordAxisEvaluation G L) :=
  (rfl)

private def mumfordLineBundleSndEval (L : InvertibleSheaf G.left) :
    (Scheme.Modules.pullback (lift (toUnit G ≫ η[G]) (𝟙 G)).left).obj
      (mumfordLineBundle G L).obj ≅ 𝟙_ G.left.Modules :=
  (eqToIso (InvertibleSheaf.pullback_obj_obj (lift (toUnit G ≫ η[G]) (𝟙 G)).left _)).symm ≪≫
    (SheafOfModules.isInvertible G.left).ι.mapIso (mumfordLineBundleSndEvaluation G L)

private lemma unit_comp_mumfordAxes :
    η[G].left ≫ (lift (toUnit G ≫ η[G]) (𝟙 G)).left =
      η[G].left ≫ (lift (𝟙 G) (toUnit G ≫ η[G])).left := by
  simp only [← Over.comp_left, comp_lift, Category.comp_id, comp_toUnit_assoc, toUnit_unit,
    Category.id_comp]

private def mumfordFstAtUnit (L : InvertibleSheaf G.left) :
    (Scheme.Modules.pullback η[G].left).obj
      ((Scheme.Modules.pullback (lift (toUnit G ≫ η[G]) (𝟙 G)).left).obj
        (mumfordLineBundle G L).obj) ≅ 𝟙_ S.Modules :=
  RigidifiedLineBundle.pullbackRigidification (unit_comp_mumfordAxes G)
    (mumfordLineBundle G L).obj (mumfordLineBundleFstRigidification G L)

private def mumfordSndEvalAtUnit (L : InvertibleSheaf G.left) :
    (Scheme.Modules.pullback η[G].left).obj
      ((Scheme.Modules.pullback (lift (toUnit G ≫ η[G]) (𝟙 G)).left).obj
        (mumfordLineBundle G L).obj) ≅ 𝟙_ S.Modules :=
  (Scheme.Modules.pullback η[G].left).mapIso (mumfordLineBundleSndEval G L) ≪≫
    pullbackObjUnitIso η[G].left

/-- The global unit on the base that changes the second-axis evaluation at the common unit
into the first-axis rigidification there. -/
def mumfordAxisCorrection (L : InvertibleSheaf G.left) : Γ(S, ⊤)ˣ :=
  (unitsGlobalSectionsMulEquivAut (𝟙_ S.Modules)).symm
    (Aut.of ((mumfordSndEvalAtUnit G L).symm ≪≫ mumfordFstAtUnit G L))

private lemma mumfordSndEvalAtUnit_hom_comp_globalSectionsSmul (L : InvertibleSheaf G.left) :
    (mumfordSndEvalAtUnit G L).hom ≫
      globalSectionsSmul (𝟙_ S.Modules) (mumfordAxisCorrection G L : Γ(S, ⊤)) =
      (mumfordFstAtUnit G L).hom := by
  simp only [mumfordAxisCorrection, globalSectionsSmul_unitsGlobalSectionsMulEquivAut_symm,
    Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- The rigidification along `x ↦ (1, x)`, given by evaluation and normalized by a scalar from
the base to agree with the first rigidification at the unit. -/
def mumfordLineBundleSndRigidification (L : InvertibleSheaf G.left) :
    (Scheme.Modules.pullback (lift (toUnit G ≫ η[G]) (𝟙 G)).left).obj
      (mumfordLineBundle G L).obj ≅ 𝟙_ G.left.Modules :=
  let u := Units.map (G.hom.appTop.hom : Γ(S, ⊤) →* Γ(G.left, ⊤)) (mumfordAxisCorrection G L)
  mumfordLineBundleSndEval G L ≪≫ asIso (globalSectionsSmul (𝟙_ G.left.Modules) ↑u)

/-- On the second axis, the dual factors are swapped before evaluation, and the resulting
trivialization is multiplied by the pullback of the base correction unit. -/
theorem mumfordLineBundleSndRigidification_def (L : InvertibleSheaf G.left) :
    mumfordLineBundleSndRigidification G L =
      let u :=
        Units.map (G.hom.appTop.hom : Γ(S, ⊤) →* Γ(G.left, ⊤)) (mumfordAxisCorrection G L)
      haveI := isIso_globalSectionsSmul_units (𝟙_ G.left.Modules) u
      ((eqToIso (InvertibleSheaf.pullback_obj_obj (lift (toUnit G ≫ η[G]) (𝟙 G)).left _)).symm ≪≫
        (SheafOfModules.isInvertible G.left).ι.mapIso
          (pullbackMumfordLineBundleIso G _ L ≪≫
            eqToIso (by simp only [← Over.comp_left, lift_comp_one_left, lift_fst, lift_snd,
              comp_toUnit_assoc, Over.id_left]) ≪≫
            (Iso.refl _ ⊗ᵢ (β_ _ _)) ≪≫ mumfordAxisEvaluation G L)) ≪≫
        asIso (globalSectionsSmul (𝟙_ G.left.Modules) ↑u) :=
  (rfl)

/-- The two axis rigidifications agree at the common unit of the factors. -/
theorem mapIso_mumfordLineBundleSndRigidification_trans_pullbackObjUnitIso
    (L : InvertibleSheaf G.left) :
    (Scheme.Modules.pullback η[G].left).mapIso (mumfordLineBundleSndRigidification G L) ≪≫
      pullbackObjUnitIso η[G].left =
      RigidifiedLineBundle.pullbackRigidification (g := η[G].left)
        (by exact unit_comp_mumfordAxes G)
        (mumfordLineBundle G L).obj (mumfordLineBundleFstRigidification G L) := by
  have h : η[G].left.appTop (G.hom.appTop (mumfordAxisCorrection G L : Γ(S, ⊤))) =
      (mumfordAxisCorrection G L : Γ(S, ⊤)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w η[G], Over.tensorUnit_hom,
      Scheme.Hom.id_appTop, CommRingCat.id_apply]
  ext1
  simp only [mumfordLineBundleSndRigidification, Functor.mapIso_hom, Iso.trans_hom, asIso_hom,
    Functor.map_comp, Units.coe_map, MonoidHom.coe_ofClass, Category.assoc,
    pullback_map_globalSectionsSmul, h]
  rw [globalSectionsSmul_naturality, ← Category.assoc]
  simpa only [Over.tensorUnit_left, mumfordSndEvalAtUnit, mumfordFstAtUnit, Iso.trans_hom,
    Functor.mapIso_hom] using
    mumfordSndEvalAtUnit_hom_comp_globalSectionsSmul G L

end

end TauCeti.GroupScheme
