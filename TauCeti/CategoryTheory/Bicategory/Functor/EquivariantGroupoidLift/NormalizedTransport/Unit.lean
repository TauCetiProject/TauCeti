/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Normalized
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Hom.Equivalence
public import TauCeti.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Cat

/-!
# Comparing a lift with the reconstruction of its normalization

The inverse fiber equivalences identify the reconstructed joint pseudofunctor with the original
one. The comparison along a joint arrow first removes the target fiber equivalence, commutes
the source inverse equivalence with the prescribed action, and uses the original compositor.
These comparisons preserve the prescribed actions, giving the lift morphism
`normalizationInv`. It uses the original chosen inverse fiber functors and original
counits, for arbitrary parameter categories and monoid actions. Since morphisms of lifts are
equivalences, its inverse gives `normalizationEquivalence` from the original lift to
the reconstruction of its normalization, with compatible unit and counit modifications.

This is the objectwise component of the normalization unit. Naturality of these equivalences
in lift morphisms is a separate construction.

The coherence conventions are those of Johnson–Yau, *2-Dimensional Categories*, Chapter 4.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (L : EquivariantGroupoidLift Γ actions)

/-- The canonical comparison along a joint arrow, with inverse fiber equivalences as components.
It removes the target comparison, commutes the source inverse with the action, and recombines
the two factors of the joint arrow through the original pseudofunctor compositor. -/
noncomputable def normalizationJointIso {X Y : Γ × SingleObj H} (f : X ⟶ Y) :
    L.normalizedTransport.jointFunctor f ⋙ (L.fiberEquivalence Y.1).inverse ≅
      (L.fiberEquivalence X.1).inverse ⋙ (L.joint.map f.toLoc).toFunctor :=
  Functor.isoWhiskerLeft
      (act actions X.1 f.2 ⋙ (L.fiberEquivalence X.1).inverse ⋙ L.jointMap f.1)
      (L.fiberEquivalence Y.1).unitIso.symm ≪≫
    Functor.rightUnitor _ ≪≫
    Functor.isoWhiskerRight (L.actInverseIso X.1 f.2) (L.jointMap f.1) ≪≫
    Functor.isoWhiskerLeft (L.fiberEquivalence X.1).inverse
      (Cat.Hom.toNatIso (L.joint.mapComp' (𝟙 X.1 ×ₘ f.2).toLoc
        (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc f.toLoc
        (by
          apply congrArg Quiver.Hom.toLoc
          exact Prod.ext (Category.id_comp _) (Category.comp_id _))).symm)

-- Keep component expansions named: expanding them before generic inverse cancellation
-- destroys the bundled-isomorphism normal form in importing modules.
lemma normalizationJointIso_hom_app {X Y : Γ × SingleObj H} (f : X ⟶ Y)
    (x : fiber actions X.1) :
    (L.normalizationJointIso f).hom.app x =
      (L.fiberEquivalence Y.1).unitInv.app
          ((L.jointMap f.1).obj ((L.fiberEquivalence X.1).inverse.obj
            ((act actions X.1 f.2).obj x))) ≫
        (L.jointMap f.1).map ((L.actInverseIso X.1 f.2).hom.app x) ≫
          (L.joint.mapComp' (𝟙 X.1 ×ₘ f.2).toLoc
            (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc f.toLoc
            (by
              apply congrArg Quiver.Hom.toLoc
              exact Prod.ext (Category.id_comp _) (Category.comp_id _))).inv.toNatTrans.app
              ((L.fiberEquivalence X.1).inverse.obj x) := by
  -- Present the comparison in the original target fiber before simplifying its unitors.
  change _ ≫ 𝟙 _ ≫ _ ≫ _ = _
  simp only [Category.id_comp]
  rfl

lemma normalizationJointIso_inv_app {X Y : Γ × SingleObj H} (f : X ⟶ Y)
    (x : fiber actions X.1) :
    (L.normalizationJointIso f).inv.app x =
      (L.joint.mapComp' (𝟙 X.1 ×ₘ f.2).toLoc
        (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc f.toLoc
        (by
          apply congrArg Quiver.Hom.toLoc
          exact Prod.ext (Category.id_comp _) (Category.comp_id _))).hom.toNatTrans.app
            ((L.fiberEquivalence X.1).inverse.obj x) ≫
        (L.jointMap f.1).map ((L.actInverseIso X.1 f.2).inv.app x) ≫
          (L.fiberEquivalence Y.1).unit.app
            ((L.jointMap f.1).obj ((L.fiberEquivalence X.1).inverse.obj
              ((act actions X.1 f.2).obj x))) := by
  -- The intermediate right unitor has identity components in the original joint fiber.
  change ((_ ≫ (L.jointMap f.1).map ((L.actInverseIso X.1 f.2).inv.app x)) ≫ 𝟙 _) ≫ _ = _
  simp only [Category.comp_id, Category.assoc]
  rfl

private lemma joint_mapId_hom_app (p : Γ) (z : L.jointFiber p) :
    (L.joint.mapId ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app z =
      (L.jointMapId p).hom.app z := by
  simp only [jointMapId_hom_app, ← prod_id, Quiver.Hom.id_toLoc,
    Pseudofunctor.mapId'_eq_mapId]

private lemma normalizationJointIso_id (p : Γ) (x : fiber actions p) :
    (L.normalizationJointIso (𝟙 (p, SingleObj.star H))).hom.app x ≫
        (L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj x) =
      (L.fiberEquivalence p).inverse.map
        ((L.normalizedTransport.jointId (p, SingleObj.star H)).hom.app x) := by
  simp only [normalizationJointIso_hom_app, NormalizedTransport.jointId_hom_app,
    normalizedTransport_transportId, transportId_hom_app, prod_id_fst, prod_id_snd]
  -- State both sides in the original joint fiber. The reconstructed functor's dependent
  -- endpoints otherwise prevent rewriting its component maps.
  change
    ((L.fiberEquivalence p).unitInv.app
        ((L.jointMap (𝟙 p)).obj ((L.fiberEquivalence p).inverse.obj
          ((act actions p (𝟙 (SingleObj.star H))).obj x))) ≫
      (L.jointMap (𝟙 p)).map ((L.actInverseIso p (𝟙 (SingleObj.star H))).hom.app x) ≫
      (L.joint.mapComp' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc
        (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 (p, SingleObj.star H)).toLoc
        (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app
          ((L.fiberEquivalence p).inverse.obj x)) ≫
      (L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj x) =
    (L.fiberEquivalence p).inverse.map
      ((L.fiberEquivalence p).functor.map
          ((L.jointMap (𝟙 p)).map ((L.fiberEquivalence p).inverse.map
            ((actId actions p).hom.app x))) ≫
        (L.fiberEquivalence p).functor.map
          ((L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj x)) ≫
        (L.fiberEquivalence p).counit.app x)
  simp only [Functor.map_comp, Category.assoc]
  erw [Pseudofunctor.mapComp'_comp_id_inv_app]
  rw [L.joint_mapId_hom_app]
  erw [(L.jointMapId p).hom.naturality_assoc]
  simp only [Functor.id_map]
  rw [L.actInverseIso_actId]
  simp [Equivalence.inv_fun_map]

private lemma normalizationJointFactorization {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (a b : SingleObj.star H ⟶ SingleObj.star H) (y : L.jointFiber p) :
    (L.jointMap (g ≫ h)).map ((L.jointActComp p a b (a ≫ b) rfl).hom.app y) ≫
      (L.jointMapComp g h (g ≫ h) rfl).hom.app ((L.jointAct p b).obj ((L.jointAct p a).obj y)) ≫
      (L.jointMap h).map ((L.jointActCommIso g b).hom.app ((L.jointAct p a).obj y)) ≫
      (L.joint.mapComp' (𝟙 q ×ₘ b).toLoc (h ×ₘ 𝟙 _).toLoc (h ×ₘ b).toLoc
        (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app
        ((L.jointMap g).obj ((L.jointAct p a).obj y)) ≫
      (L.joint.map (h ×ₘ b).toLoc).toFunctor.map
        ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 _).toLoc (g ×ₘ a).toLoc
          (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app y) =
    (L.joint.mapComp' (𝟙 p ×ₘ (a ≫ b)).toLoc ((g ≫ h) ×ₘ 𝟙 _).toLoc
      ((g ≫ h) ×ₘ (a ≫ b)).toLoc
        (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app y ≫
      (L.joint.mapComp' (g ×ₘ a).toLoc (h ×ₘ b).toLoc ((g ≫ h) ×ₘ (a ≫ b)).toLoc
        (by simp [← Quiver.Hom.comp_toLoc])).hom.toNatTrans.app y := by
  simp only [jointActComp_hom_app, jointMapComp_hom_app, jointActCommIso_hom_app,
    Functor.map_comp, Category.assoc, jointMap, jointAct]
  erw [L.joint.mapComp'_hom_naturality_assoc]
  rw [← Functor.map_comp_assoc]
  -- Regroup the source action factors and then the two parameter arrows.
  rw [← L.joint.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app
    (𝟙 p ×ₘ a).toLoc (𝟙 p ×ₘ b).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (𝟙 p ×ₘ (a ≫ b)).toLoc (g ×ₘ b).toLoc (g ×ₘ (a ≫ b)).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc])]
  simp only [Functor.map_comp, Category.assoc]
  rw [← L.joint.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc
    (𝟙 p ×ₘ (a ≫ b)).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (h ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ (a ≫ b)).toLoc
    ((g ≫ h) ×ₘ 𝟙 (SingleObj.star H)).toLoc ((g ≫ h) ×ₘ (a ≫ b)).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc])]
  -- Interchange the middle action and parameter factors through the commuting square.
  rw [L.joint.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    (𝟙 p ×ₘ a).toLoc (g ×ₘ b).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (g ×ₘ (a ≫ b)).toLoc ((g ≫ h) ×ₘ b).toLoc ((g ≫ h) ×ₘ (a ≫ b)).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc])]
  rw [L.joint.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 q ×ₘ b).toLoc
    (h ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ b).toLoc (h ×ₘ b).toLoc
    ((g ≫ h) ×ₘ b).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc])]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rw [L.joint.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc
    (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ b).toLoc
    (g ×ₘ a).toLoc ((g ≫ h) ×ₘ b).toLoc ((g ≫ h) ×ₘ (a ≫ b)).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) (by simp [← Quiver.Hom.comp_toLoc])
    (by simp [← Quiver.Hom.comp_toLoc])]
  simp [← Functor.map_comp]

-- The middle fiber comparison cancels with the mate defining the commuting transport cell.
private lemma unit_inverse_map_transportCommIso_hom_app_comp {p q : Γ} (g : p ⟶ q)
    (b : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (L.fiberEquivalence q).unit.app
        ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj ((act actions p b).obj x))) ≫
      (L.fiberEquivalence q).inverse.map ((L.transportCommIso g b).hom.app x) ≫
      (L.actInverseIso q b).hom.app ((L.transport g).obj x) ≫
      (L.jointAct q b).map ((L.fiberEquivalence q).unitInv.app
        ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj x))) =
    (L.jointMap g).map ((L.actInverseIso p b).hom.app x) ≫
      (L.jointActCommIso g b).hom.app ((L.fiberEquivalence p).inverse.obj x) := by
  rw [transportCommIso_hom_app]
  dsimp only [transport_obj, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc,
    inverse_map_comparisonNaturality_hom_app_comp, Equivalence.inv_fun_map,
    Iso.hom_inv_id_app_assoc, Equivalence.unitIso_hom_inv_id_app, Category.comp_id]

private lemma normalizationJointComp_hom_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (a b : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (L.normalizedTransport.jointComp (g ×ₘ a) (h ×ₘ b)
      ((g ≫ h) ×ₘ (a ≫ b)) (by simp)).hom.app x =
    (L.fiberEquivalence r).functor.map
      ((L.jointMap (g ≫ h)).map ((L.fiberEquivalence p).inverse.map
          ((actComp actions p a b (a ≫ b) rfl).hom.app x)) ≫
        (L.jointMapComp g h (g ≫ h) rfl).hom.app
          ((L.fiberEquivalence p).inverse.obj
            ((act actions p b).obj ((act actions p a).obj x))) ≫
        (L.jointMap h).map ((L.fiberEquivalence q).unit.app
          ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj
            ((act actions p b).obj ((act actions p a).obj x))))) ≫
        (L.jointMap h).map ((L.fiberEquivalence q).inverse.map
          ((L.transportCommIso g b).hom.app ((act actions p a).obj x)))) := by
  simp only [NormalizedTransport.jointComp_hom_app, normalizedTransport_transportComp,
    normalizedTransport_transportCommIso, transportComp_inv_app]
  -- Fix the actual prescribed fibers before collecting the three functor images.
  change (L.fiberEquivalence r).functor.map _ ≫
    (L.fiberEquivalence r).functor.map (_ ≫ _) ≫
      (L.fiberEquivalence r).functor.map
        ((L.jointMap h).map ((L.fiberEquivalence q).inverse.map _)) = _
  simp only [Functor.map_comp, Category.assoc]
  rfl

private lemma normalizationJointIso_comp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (a b : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (L.normalizationJointIso ((g ≫ h) ×ₘ (a ≫ b))).hom.app x ≫
        (L.joint.mapComp' (g ×ₘ a).toLoc (h ×ₘ b).toLoc
          ((g ≫ h) ×ₘ (a ≫ b)).toLoc
            (by simp [← Quiver.Hom.comp_toLoc])).hom.toNatTrans.app
          ((L.fiberEquivalence p).inverse.obj x) =
      (L.fiberEquivalence r).inverse.map
          ((L.normalizedTransport.jointComp (g ×ₘ a) (h ×ₘ b)
            ((g ≫ h) ×ₘ (a ≫ b)) (by simp)).hom.app x) ≫
        (L.normalizationJointIso (h ×ₘ b)).hom.app
          ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) ≫
        (L.joint.map (h ×ₘ b).toLoc).toFunctor.map
          ((L.normalizationJointIso (g ×ₘ a)).hom.app x) := by
  let y := (L.fiberEquivalence p).inverse.obj ((act actions p a).obj x)
  rw [L.normalizationJointComp_hom_app]
  simp only [normalizationJointIso_hom_app]
  let c₀ := L.joint.mapComp' (𝟙 p ×ₘ (a ≫ b)).toLoc
    ((g ≫ h) ×ₘ 𝟙 (SingleObj.star H)).toLoc ((g ≫ h) ×ₘ (a ≫ b)).toLoc
    (by simp [← Quiver.Hom.comp_toLoc])
  let c₁ := L.joint.mapComp' (𝟙 p ×ₘ a).toLoc
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
    (by simp [← Quiver.Hom.comp_toLoc])
  let c₂ := L.joint.mapComp' (𝟙 q ×ₘ b).toLoc
    (h ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ b).toLoc
    (by simp [← Quiver.Hom.comp_toLoc])
  let c₃ := L.joint.mapComp' (g ×ₘ a).toLoc (h ×ₘ b).toLoc
    ((g ≫ h) ×ₘ (a ≫ b)).toLoc (by simp [← Quiver.Hom.comp_toLoc])
  -- Name the compositor data so simplification retains their original arrow carriers.
  change
    ((L.fiberEquivalence r).unitInv.app
        ((L.jointMap (g ≫ h)).obj ((L.fiberEquivalence p).inverse.obj
          ((act actions p (a ≫ b)).obj x))) ≫
      (L.jointMap (g ≫ h)).map ((L.actInverseIso p (a ≫ b)).hom.app x) ≫
      c₀.inv.toNatTrans.app ((L.fiberEquivalence p).inverse.obj x)) ≫
        c₃.hom.toNatTrans.app ((L.fiberEquivalence p).inverse.obj x) =
    (L.fiberEquivalence r).inverse.map ((L.fiberEquivalence r).functor.map _) ≫
      ((L.fiberEquivalence r).unitInv.app
        ((L.jointMap h).obj ((L.fiberEquivalence q).inverse.obj
          ((act actions q b).obj ((L.fiberEquivalence q).functor.obj
            ((L.jointMap g).obj y))))) ≫
        (L.jointMap h).map ((L.actInverseIso q b).hom.app
          ((L.fiberEquivalence q).functor.obj ((L.jointMap g).obj y))) ≫
        c₂.inv.toNatTrans.app ((L.fiberEquivalence q).inverse.obj
          ((L.fiberEquivalence q).functor.obj ((L.jointMap g).obj y)))) ≫
      (L.joint.map (h ×ₘ b).toLoc).toFunctor.map
        ((L.fiberEquivalence q).unitInv.app ((L.jointMap g).obj y) ≫
          (L.jointMap g).map ((L.actInverseIso p a).hom.app x) ≫
          c₁.inv.toNatTrans.app ((L.fiberEquivalence p).inverse.obj x))
  dsimp only [transport_obj, Functor.comp_obj]
  repeat rw [Category.assoc]
  -- Cancel the outer comparison at the target before examining the intermediate fiber.
  erw [(L.fiberEquivalence r).unitInv_naturality_assoc]
  apply congrArg ((L.fiberEquivalence r).unitInv.app _ ≫ ·)
  simp only [Functor.map_comp, Category.assoc]
  -- Naturality of the original joint compositor brings the middle fiber unit next to its mate.
  erw [← c₂.inv.toNatTrans.naturality_assoc]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, Functor.id_obj]
  repeat rw [← Functor.map_comp_assoc (L.jointMap h)]
  simp only [Category.assoc]
  erw [L.unit_inverse_map_transportCommIso_hom_app_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [← c₂.inv.toNatTrans.naturality_assoc]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  erw [← Functor.map_comp_assoc (L.jointMap h)
    ((L.jointActCommIso g b).hom.app y)]
  erw [← (L.jointActCommIso g b).hom.naturality]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  erw [← (L.jointMapComp g h (g ≫ h) rfl).hom.naturality_assoc]
  erw [← (L.jointMapComp g h (g ≫ h) rfl).hom.naturality_assoc]
  -- The remaining source-action comparisons combine by the existing product law.
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc,
    L.actInverseIso_actComp]
  simp only [Functor.map_comp, Category.assoc]
  apply congrArg ((L.jointMap (g ≫ h)).map
    ((L.actInverseIso p (a ≫ b)).hom.app x) ≫ ·)
  -- Only the four-arrow factorization of the original joint pseudofunctor remains.
  exact (L.normalizationJointFactorization g h a b
    ((L.fiberEquivalence p).inverse.obj x)).symm

/-- The inverse fiber equivalences compare the reconstructed joint pseudofunctor with the
original joint pseudofunctor, coherently along both parameter and action arrows. -/
-- The literal component functors are needed for the characteristic naturality equations.
@[expose] noncomputable def normalizationJointInv : L.normalizedTransport.joint ⟶ L.joint where
  app X := (L.fiberEquivalence X.as.1).inverse.toCatHom
  naturality f := Cat.Hom.isoMk (L.normalizationJointIso f.as)
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete
      L.normalizedTransport.joint L.joint
      (fun X ↦ (L.fiberEquivalence X.as.1).inverse.toCatHom)
      (fun f ↦ Cat.Hom.isoMk (L.normalizationJointIso f.as)) η
  naturality_id X := by
    obtain ⟨p, a⟩ := X
    cases a
    ext x
    -- The source object is the prescribed fiber through the reconstructed presentation.
    change fiber actions p at x
    -- Cat unitors have identity components; display the remaining actual fiber maps.
    change (L.normalizationJointIso (𝟙 (p, SingleObj.star H))).hom.app x ≫
        (L.joint.mapId ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app
          ((L.fiberEquivalence p).inverse.obj x) =
      (L.fiberEquivalence p).inverse.map
        ((L.normalizedTransport.joint.mapId ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app x) ≫
          𝟙 _ ≫ 𝟙 _
    rw [Category.comp_id, Category.comp_id]
    erw [NormalizedTransport.joint_mapId_hom_app]
    have h := L.normalizationJointIso_id p x
    rw [L.joint_mapId_hom_app]
    exact h
  naturality_comp f g := by
    rename_i X Y Z
    ext x
    -- Use the prescribed category for the component argument of the reconstructed source.
    change fiber actions X.as.1 at x
    -- Associators of Cat have identity components; all substantive cells are the joint ones.
    change (L.normalizationJointIso (f ≫ g).as).hom.app x ≫
        (L.joint.mapComp f g).hom.toNatTrans.app
          ((L.fiberEquivalence _).inverse.obj x) =
      (L.fiberEquivalence _).inverse.map
        ((L.normalizedTransport.joint.mapComp f g).hom.toNatTrans.app x) ≫
          𝟙 _ ≫ (L.normalizationJointIso g.as).hom.app
            ((L.normalizedTransport.joint.map f).toFunctor.obj x) ≫
          𝟙 _ ≫ (L.joint.map g).toFunctor.map
            ((L.normalizationJointIso f.as).hom.app x) ≫ 𝟙 _
    rw [Category.id_comp, Category.id_comp]
    erw [Category.comp_id, NormalizedTransport.joint_mapComp_hom_app]
    have h := L.normalizationJointIso_comp f.as.1 g.as.1 f.as.2 g.as.2 x
    erw [Pseudofunctor.mapComp'_eq_mapComp] at h
    exact h

-- These characteristic equations preserve the original fibers; simplification through the
-- reconstructed dependent object carriers is not stable in importing modules.
lemma normalizationJointInv_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    L.normalizationJointInv.app X = (L.fiberEquivalence X.as.1).inverse.toCatHom :=
  (rfl)

-- These equations retain the prescribed object carriers; simplifier matching through the
-- reconstructed dependent category presentation is not stable for arbitrary importing clients.
lemma normalizationJointInv_naturality_hom_app {X Y : LocallyDiscrete (Γ × SingleObj H)}
    (f : X ⟶ Y) (x : fiber actions X.as.1) :
    (L.normalizationJointInv.naturality f).hom.toNatTrans.app x =
      (L.normalizationJointIso f.as).hom.app x :=
  (rfl)

lemma normalizationJointInv_naturality_inv_app {X Y : LocallyDiscrete (Γ × SingleObj H)}
    (f : X ⟶ Y) (x : fiber actions X.as.1) :
    (L.normalizationJointInv.naturality f).inv.toNatTrans.app x =
      (L.normalizationJointIso f.as).inv.app x :=
  (rfl)

private lemma normalizationJointIso_fiber (p : Γ)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (L.fiberEquivalence p).functor.map
        ((L.normalizationJointIso (𝟙 p ×ₘ a)).hom.app x) ≫
      (L.comparisonNaturality p a).hom.app ((L.fiberEquivalence p).inverse.obj x) ≫
        (act actions p a).map ((L.fiberEquivalence p).counit.app x) =
      (L.fiberEquivalence p).counit.app
          ((L.normalizedTransport.jointFunctor (𝟙 p ×ₘ a)).obj x) ≫
        (L.transportId p).hom.app ((act actions p a).obj x) := by
  rw [normalizationJointIso_hom_app, transportId_hom_app]
  -- The normalized identity transport has its original joint-fiber presentation.
  change (L.fiberEquivalence p).functor.map (_ ≫ _ ≫ _) ≫ _ ≫ _ =
    (L.fiberEquivalence p).counit.app
      ((L.fiberEquivalence p).functor.obj
        ((L.jointMap (𝟙 p)).obj ((L.fiberEquivalence p).inverse.obj
          ((act actions p a).obj x)))) ≫ _ ≫ _
  simp only [Functor.map_comp, Category.assoc]
  erw [Pseudofunctor.mapComp'_comp_id_inv_app]
  rw [L.joint_mapId_hom_app]
  rw [← Functor.map_comp_assoc (L.fiberEquivalence p).functor
    ((L.jointMap (𝟙 p)).map ((L.actInverseIso p a).hom.app x))]
  erw [(L.jointMapId p).hom.naturality]
  simp only [Functor.id_map, Functor.map_comp, Category.assoc]
  rw [L.functor_map_actInverseIso_hom_app_comp_assoc]
  erw [← (L.fiberEquivalence p).counit_app_functor]
  simp [← Functor.map_comp]

/-- The comparison of reconstructed and original joint pseudofunctors preserves each prescribed
fiber action. Its components are the counits of the original fiber equivalences. -/
noncomputable def normalizationJointInvFiberIso (p : Γ) :
    (Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeft L.normalizationJointInv ≫
        L.comparison p ≅ L.normalizedTransport.comparison p :=
  Pseudofunctor.StrongTrans.isoMk
    (fun _ ↦ Cat.Hom.isoMk (L.fiberEquivalence p).counitIso) (fun f ↦ by
      ext x
      -- Both restricted source objects are the prescribed fiber category.
      change fiber actions p at x
      -- The outer whiskerings evaluate to the counit and its action image.
      change (L.fiberEquivalence p).counit.app
          ((L.normalizedTransport.jointFunctor (𝟙 p ×ₘ f.as)).obj x) ≫
          ((L.normalizedTransport.comparison p).naturality f).hom.toNatTrans.app x =
        (((Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeft L.normalizationJointInv ≫
          L.comparison p).naturality f).hom.toNatTrans.app x ≫
            (act actions p f.as).map ((L.fiberEquivalence p).counit.app x)
      erw [Pseudofunctor.StrongTrans.comp_naturality_hom_app]
      rw [NormalizedTransport.comparison_naturality_hom_app]
      rw [normalizedTransport_transportId]
      erw [Category.assoc]
      have h := (L.normalizationJointIso_fiber p f.as x).symm
      rw [comparisonNaturality_hom_app] at h
      exact h)

lemma normalizationJointInvFiberIso_hom_as_app (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (L.normalizationJointInvFiberIso p).hom.as.app a =
      (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).hom :=
  (rfl)

lemma normalizationJointInvFiberIso_inv_as_app (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (L.normalizationJointInvFiberIso p).inv.as.app a =
      (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).inv :=
  (rfl)

/-- The morphism of lifts from reconstructed normalized transport to the original lift.
Its joint components are the inverse fiber equivalences, and its fiber isomorphisms are
their action-compatible counits. -/
-- The joint component carriers identify the counit maps in the fiber equations below.
@[expose] noncomputable def normalizationInv : L.normalizedTransport.toLift ⟶ L where
  joint := L.normalizationJointInv
  fiberIso := L.normalizationJointInvFiberIso

@[simp]
lemma normalizationInv_joint :
    L.normalizationInv.joint = L.normalizationJointInv :=
  (rfl)

lemma normalizationInv_jointFunctor (p : Γ) :
    L.normalizationInv.jointFunctor p = (L.fiberEquivalence p).inverse :=
  (rfl)

lemma normalizationInv_fiberIso_hom_as_app (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (L.normalizationInv.fiberIso p).hom.as.app a =
      (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).hom :=
  (rfl)

lemma normalizationInv_fiberIso_inv_as_app (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (L.normalizationInv.fiberIso p).inv.as.app a =
      (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).inv :=
  (rfl)

/-- A lift is equivalent to the reconstruction of its normalized transport. The inverse
morphism uses the original inverse fiber equivalences and their counits; the forward morphism
uses chosen quasi-inverses of those component functors. Both preserve the prescribed actions. -/
@[expose] noncomputable def normalizationEquivalence : L ≌ L.normalizedTransport.toLift :=
  L.normalizationInv.equivalence.symm

@[simp]
lemma normalizationEquivalence_hom :
    L.normalizationEquivalence.hom = L.normalizationInv.equivalence.inv :=
  (rfl)

-- Keep these dependent modification equations named: importing simp has unstable carriers.
lemma normalizationEquivalence_unit :
    L.normalizationEquivalence.unit = L.normalizationInv.equivalence.counit.symm :=
  (rfl)

lemma normalizationEquivalence_counit :
    L.normalizationEquivalence.counit = L.normalizationInv.equivalence.unit.symm :=
  Bicategory.Equivalence.symm_counit _

@[simp]
lemma normalizationEquivalence_inv : L.normalizationEquivalence.inv = L.normalizationInv :=
  Hom.equivalence_hom L.normalizationInv

end TauCeti.EquivariantGroupoidLift
