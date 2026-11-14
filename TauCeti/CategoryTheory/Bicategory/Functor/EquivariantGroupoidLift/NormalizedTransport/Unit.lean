/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Hom.Equivalence
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Functor
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Reconstruction
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

For any morphism of lifts `φ : L ⟶ L'`, the inverse-fiber comparisons `φ.inverseFiberIso p` define a
compatible invertible modification `φ.normalizationInvCompIso` between `L.normalizationInv ≫ φ` and
`φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv`. Taking its inverse supplies the
naturality cells of the strong transformation `normalizationUnitInv actions` from normalization
followed by reconstruction to the identity pseudofunctor on `EquivariantGroupoidLift Γ actions`;
the remaining strong-transformation axioms are automatic because compatible modifications between
parallel lift morphisms form a subsingleton. Upgrading `normalizationUnitInv actions` via
`Pseudofunctor.StrongTrans.equivalenceMk` and symmetry of bicategorical equivalences yields the unit
equivalence
`normalizationUnitEquiv actions :
  Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions)`
and its underlying forward strong transformation `normalizationUnitHom actions`.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.normalizationInv`: morphism of lifts from the reconstruction of
  `L.normalizedTransport` back to `L`;
* `TauCeti.EquivariantGroupoidLift.normalizationEquivalence`: pointwise equivalence between `L` and
  `L.normalizedTransport.toLift`;
* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvCompIso`: pseudonaturality isomorphism of
  `normalizationInv` with respect to a morphism of lifts `φ : L ⟶ L'`;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`: inverse and forward strong transformations
  comparing the identity pseudofunctor on lifts with normalization followed by reconstruction;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the unit adjoint equivalence of
  pseudofunctors.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: strong transformations,
  modifications, and pointwise equivalences in pseudofunctor bicategories.
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
  obtain ⟨p, ⟨⟩⟩ := X
  obtain ⟨q, ⟨⟩⟩ := Y
  -- Normalize the implicit reconstructed source carrier before simplifying the comparison.
  dsimp only [normalizationJointIso, NormalizedTransport.jointFunctor,
    normalizedTransport, transport]
  simp

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
  obtain ⟨p, ⟨⟩⟩ := X
  obtain ⟨q, ⟨⟩⟩ := Y
  dsimp only [normalizationJointIso, NormalizedTransport.jointFunctor,
    normalizedTransport, transport]
  simp

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
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport, transport_obj,
    Functor.comp_obj]
  simp only [normalizationJointIso_hom_app, NormalizedTransport.jointId_hom_app,
    transportId_hom_app, prod_id_fst, prod_id_snd]
  simp only [Category.assoc]
  simp only [← prod_id, Quiver.Hom.id_toLoc]
  rw [Pseudofunctor.mapComp'_comp_id_inv_app]
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
      (L.actInverseIso q b).hom.app ((L.fiberEquivalence q).functor.obj
        ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj x))) ≫
      (L.joint.map (𝟙 q ×ₘ b).toLoc).toFunctor.map ((L.fiberEquivalence q).unitInv.app
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
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport, transport_obj,
    Functor.comp_obj]
  simp only [NormalizedTransport.jointComp_hom_app, transportComp_inv_app, transport_map]
  dsimp only [normalizedTransport, transport_obj, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]

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
  rw [L.normalizationJointComp_hom_app]
  simp only [normalizationJointIso_hom_app]
  let c₂ := L.joint.mapComp' (𝟙 q ×ₘ b).toLoc
    (h ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ b).toLoc
    (by simp [← Quiver.Hom.comp_toLoc])
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport,
    transport_obj, Functor.comp_obj]
  repeat rw [Category.assoc]
  -- Cancel the outer comparison at the target before examining the intermediate fiber.
  rw [(L.fiberEquivalence r).unitInv_naturality_assoc]
  apply congrArg ((L.fiberEquivalence r).unitInv.app _ ≫ ·)
  simp only [Functor.map_comp, Category.assoc]
  -- Naturality of the original joint compositor brings the middle fiber unit next to its mate.
  rw [← c₂.inv.toNatTrans.naturality_assoc]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, Functor.id_obj]
  repeat rw [← Functor.map_comp_assoc (L.jointMap h)]
  simp only [Category.assoc]
  -- The mate cancellation uses the original joint-action carrier in its implicit endpoints.
  erw [L.unit_inverse_map_transportCommIso_hom_app_comp g b ((act actions p a).obj x)]
  simp only [Functor.map_comp, Category.assoc]
  rw [← c₂.inv.toNatTrans.naturality_assoc]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  rw [← Functor.map_comp_assoc (L.jointMap h)
    ((L.jointActCommIso g b).hom.app
      ((L.fiberEquivalence p).inverse.obj ((act actions p a).obj x)))]
  have hb := (L.jointActCommIso g b).hom.naturality ((L.actInverseIso p a).hom.app x)
  dsimp only [Functor.comp_map, Functor.comp_obj, jointAct] at hb
  rw [← hb]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.comp_map (L.jointMap g) (L.jointMap h)]
  rw [← (L.jointMapComp g h (g ≫ h) rfl).hom.naturality_assoc]
  rw [← (L.jointMapComp g h (g ≫ h) rfl).hom.naturality_assoc]
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
    refine Cat.comp_whiskerLeft_eq_whiskerRight_comp_leftUnitor_hom_comp_rightUnitor_inv
      _ _ _ (fun (x : fiber actions p) ↦ ?_)
    erw [NormalizedTransport.joint_mapId_hom_app]
    have h := L.normalizationJointIso_id p x
    erw [L.joint_mapId_hom_app]
    exact h
  naturality_comp f g := by
    refine Cat.comp_whiskerLeft_eq_whiskerRight_comp_associators
      _ _ _ _ _ (fun (x : fiber actions _) ↦ ?_)
    erw [NormalizedTransport.joint_mapComp_hom_app]
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
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport, transport_obj,
    Functor.comp_obj]
  rw [normalizationJointIso_hom_app, transportId_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← prod_id, Quiver.Hom.id_toLoc]
  rw [Pseudofunctor.mapComp'_comp_id_inv_app]
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
    (fun _ ↦ Cat.Hom.isoMk (L.fiberEquivalence p).counitIso) (fun {a b} f ↦ by
      obtain ⟨⟨⟩⟩ := a
      obtain ⟨⟨⟩⟩ := b
      refine Cat.whiskerLeft_comp_eq_comp_whiskerRight
        _ _ _ _ (fun (x : fiber actions p) ↦ ?_)
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

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

namespace Hom

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L')

private noncomputable def normalizationInvCompJointAppIso
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (L.normalizationInv.joint ≫ φ.joint).app X ≅
      (φ.normalizedTransportHom.toLiftHom.joint ≫ L'.normalizationInv.joint).app X :=
  match X with
  | ⟨(p, ⟨⟩)⟩ =>
    Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫ (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm

private lemma normalizationInvCompJointAppIso_hom_app (p : Γ) (x : fiber actions p) :
    (normalizationInvCompJointAppIso φ ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app x =
      (φ.inverseFiberIso p).hom.app x := by
  have h : normalizationInvCompJointAppIso φ ⟨(p, SingleObj.star H)⟩ =
      Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫ (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm :=
    rfl
  simp [h]
  rfl

private lemma joint_naturality_factor {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H)
    (hf : (𝟙 p ×ₘ a).toLoc ≫ (g ×ₘ 𝟙 (SingleObj.star H)).toLoc = (g ×ₘ a).toLoc)
    (y : L.jointFiber p) :
    (φ.jointMapIso g).hom.app ((L.jointAct p a).obj y) ≫
        (L'.jointMap g).map ((φ.jointActIso p a).hom.app y) ≫
        (L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
          (g ×ₘ a).toLoc hf).inv.toNatTrans.app ((φ.jointFunctor p).obj y) =
      (φ.jointFunctor q).map
          ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
            (g ×ₘ a).toLoc hf).inv.toNatTrans.app y) ≫
        (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app y := by
  have hcomp := φ.joint.naturality_comp'_hom_app
    (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc hf y
  rw [← cancel_epi ((φ.jointFunctor q).map
    ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (g ×ₘ a).toLoc hf).hom.toNatTrans.app y))]
  rw [← Functor.map_comp_assoc, Cat.Hom.hom_inv_id_toNatTrans_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simpa only [jointMapIso_hom_app, jointActIso_hom_app, jointMap, jointAct,
    jointFunctor, Category.assoc, Category.id_comp, Category.comp_id] using hcomp.symm

private lemma normalizationInvComp_naturality {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (φ.inverseFiberIso q).hom.app ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) ≫
        (((φ.normalizedTransportHom.toLiftHom.joint ≫ L'.normalizationInv.joint).naturality
          (g ×ₘ a).toLoc).hom.toNatTrans.app x) =
      (((L.normalizationInv.joint ≫ φ.joint).naturality (g ×ₘ a).toLoc).hom.toNatTrans.app x) ≫
        (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map ((φ.inverseFiberIso p).hom.app x) := by
  have hf : (𝟙 p ×ₘ a).toLoc ≫ (g ×ₘ 𝟙 (SingleObj.star H)).toLoc = (g ×ₘ a).toLoc := by
    apply congrArg Quiver.Hom.toLoc
    exact Prod.ext (Category.id_comp _) (Category.comp_id _)
  let cL' := L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc hf
  erw [Pseudofunctor.StrongTrans.comp_naturality_hom_app,
    Pseudofunctor.StrongTrans.comp_naturality_hom_app,
    NormalizedTransport.Hom.jointHom_naturality_hom_app,
    L'.normalizationJointInv_naturality_hom_app (g ×ₘ a).toLoc x,
    L.normalizationJointInv_naturality_hom_app (g ×ₘ a).toLoc x]
  -- Display the components over the prescribed fiber and joint-fiber categories so rewriting
  -- does not abstract through the reconstructed lift's dependent object carrier.
  change (φ.inverseFiberIso q).hom.app ((L.transport g).obj ((act actions p a).obj x)) ≫
      ((L'.fiberEquivalence q).inverse.map
          ((φ.normalizedTransportHom.transportIso g).hom.app ((act actions p a).obj x)) ≫
        (L'.normalizationJointIso (g ×ₘ a)).hom.app x) =
    ((φ.jointFunctor q).map ((L.normalizationJointIso (g ×ₘ a)).hom.app x) ≫
        (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app
          ((L.fiberEquivalence p).inverse.obj x)) ≫
      (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map ((φ.inverseFiberIso p).hom.app x)
  simp only [normalizedTransportHom_transportIso, transportIso_hom_app,
    normalizationJointIso_hom_app]
  dsimp only [normalizedTransport, transport_obj, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  -- Cancel the target fiber equivalence with its inverse at `q` via `unitInv_naturality`.
  have hq₁ := (L'.fiberEquivalence q).unitInv_naturality
    ((φ.jointMapIso g).hom.app ((L.fiberEquivalence p).inverse.obj ((act actions p a).obj x)) ≫
      (L'.jointMap g).map ((φ.inverseFiberIso p).hom.app ((act actions p a).obj x)))
  simp only [Functor.map_comp, Category.assoc] at hq₁
  erw [reassoc_of% hq₁, φ.inverseFiberIso_hom_app_comp_unitInv_assoc]
  -- Commute the source inverse-fiber comparison past the prescribed action of `a`.
  rw [← (L'.jointMap g).map_comp_assoc, ← φ.inverseFiberIso_actInverseIso p a x]
  simp only [Functor.map_comp, Category.assoc]
  have hg := (φ.jointMapIso g).hom.naturality ((L.actInverseIso p a).hom.app x)
  dsimp only [Functor.comp_map] at hg
  rw [← reassoc_of% hg]
  -- Move the remaining source comparison across the target compositor `cL'.inv`.
  have hc' := cL'.inv.toNatTrans.naturality ((φ.inverseFiberIso p).hom.app x)
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hc'
  erw [hc', reassoc_of% joint_naturality_factor φ g a hf ((L.fiberEquivalence p).inverse.obj x)]

private lemma normalizationInvComp_fiber_compatibility {A B C C' : Cat.{v, w}}
    {I : A ⟶ C} {P : C ⟶ C'} {I' : A ⟶ C'}
    {E : C ⟶ B} {E' : C' ⟶ B} {U : A ⟶ B}
    (m : I ≫ P ⟶ 𝟙 A ≫ I') (ε' : I' ≫ E' ⟶ U) (u : 𝟙 A ≫ U ⟶ U)
    (f : P ≫ E' ⟶ E) (ε : I ≫ E ⟶ U)
    (h : ∀ x : A, E'.toFunctor.map (m.toNatTrans.app x) ≫
        ε'.toNatTrans.app x ≫ u.toNatTrans.app x =
      f.toNatTrans.app (I.toFunctor.obj x) ≫ ε.toNatTrans.app x) :
    m ▷ E' ≫ ((α_ (𝟙 A) I' E').hom ≫ 𝟙 A ◁ ε' ≫ u) =
      (α_ I P E').hom ≫ I ◁ f ≫ ε := by
  ext x
  simpa using h x

/-- Applying a morphism of lifts `φ : L ⟶ L'` after `L.normalizationInv` is canonically isomorphic
to applying the reconstructed normalized comparison `φ.normalizedTransportHom.toLiftHom` and then
`L'.normalizationInv`. Its joint components are the inverse-fiber comparisons
`φ.inverseFiberIso p`. -/
noncomputable def normalizationInvCompIso :
    L.normalizationInv ≫ φ ≅ φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv :=
  isoMk
    (Pseudofunctor.StrongTrans.isoMk (normalizationInvCompJointAppIso φ) fun {X Y} f ↦ by
      obtain ⟨p, ⟨⟩⟩ := X
      obtain ⟨q, ⟨⟩⟩ := Y
      obtain ⟨g, a⟩ := f
      refine Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun (x : fiber actions p) ↦ ?_
      erw [normalizationInvCompJointAppIso_hom_app φ q, normalizationInvCompJointAppIso_hom_app φ p]
      exact normalizationInvComp_naturality φ g a x)
    fun p a ↦ by
      obtain ⟨⟨⟩⟩ := a
      simp only [EquivariantGroupoidLift.comp_fiberIso, comp_fiberIso_hom_as_app]
      refine normalizationInvComp_fiber_compatibility _ _ _ _ _ fun x ↦ ?_
      erw [normalizationInvCompJointAppIso_hom_app φ p x,
        L'.normalizationInv_fiberIso_hom_as_app p ⟨SingleObj.star H⟩,
        NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app,
        L.normalizationInv_fiberIso_hom_as_app p ⟨SingleObj.star H⟩,
        ← φ.fiberFunctorIso_hom_app p ((L.fiberEquivalence p).inverse.obj x)]
      rw [Cat.leftUnitor_hom_toNatTrans]
      erw [Functor.leftUnitor_hom_app, Category.comp_id]
      exact φ.functor_map_inverseFiberIso_hom_app_comp_counit p x

@[simp]
lemma normalizationInvCompIso_hom_joint_as_app_star (p : Γ) :
    (normalizationInvCompIso φ).hom.joint.as.app ⟨(p, SingleObj.star H)⟩ =
      (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
        (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm).hom := by
  simp only [normalizationInvCompIso, isoMk_hom_joint]
  rfl

@[simp]
lemma normalizationInvCompIso_inv_joint_as_app_star (p : Γ) :
    (normalizationInvCompIso φ).inv.joint.as.app ⟨(p, SingleObj.star H)⟩ =
      (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
        (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm).inv := by
  simp only [normalizationInvCompIso, isoMk_inv_joint]
  rfl

end Hom

section Unit

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- The strong transformation from normalization followed by reconstruction to the identity
pseudofunctor on equivariant lifts, with components `L.normalizationInv` and naturality cells
`(Hom.normalizationInvCompIso φ).symm`. -/
-- Expose the component projections so the unit and counit equations retain their lift endpoints.
@[expose] noncomputable def normalizationUnitInv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ⟶
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) where
  app L := L.normalizationInv
  naturality φ := (Hom.normalizationInvCompIso φ).symm
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitInv_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitInv actions).app L = L.normalizationInv :=
  (rfl)

@[simp]
lemma normalizationUnitInv_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitInv actions).naturality φ = (Hom.normalizationInvCompIso φ).symm :=
  (rfl)

/-- The identity pseudofunctor on equivariant lifts is equivalent to normalization followed by
reconstruction, by upgrading `normalizationUnitInv` via the pointwise equivalences
`L.normalizationInv.equivalence` and inverting. -/
-- Expose the record projections so its unit and counit component equations can be stated.
@[expose] noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) :=
  ((normalizationUnitInv actions).equivalenceMk
    (fun L ↦ L.normalizationInv.equivalence.inv)
    (fun L ↦ L.normalizationInv.equivalence.unit)
    (fun L ↦ L.normalizationInv.equivalence.counit)
    (fun L ↦ L.normalizationInv.equivalence.left_triangle)).symm

/-- The forward strong transformation from the identity pseudofunctor on equivariant lifts to
normalization followed by reconstruction, with components `L.normalizationInv.equivalence.inv`. -/
-- Expose the underlying transformation so component equations of `normalizationUnitEquiv` hold.
@[expose] noncomputable def normalizationUnitHom :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ⟶
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) :=
  (normalizationUnitEquiv actions).hom

@[simp]
lemma normalizationUnitHom_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitHom actions).app L = L.normalizationInv.equivalence.inv :=
  (rfl)

@[simp]
lemma normalizationUnitHom_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitHom actions).naturality φ =
      (L.normalizationInv.equivalence.mateIsoEquiv L'.normalizationInv.equivalence
        (Hom.normalizationInvCompIso φ).symm).symm :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_hom :
    (normalizationUnitEquiv actions).hom = normalizationUnitHom actions :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_inv :
    (normalizationUnitEquiv actions).inv = normalizationUnitInv actions :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_unit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.hom.as.app L =
      L.normalizationInv.equivalence.counit.inv :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_unit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.inv.as.app L =
      L.normalizationInv.equivalence.counit.hom :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_counit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.hom.as.app L =
      L.normalizationInv.equivalence.unit.inv :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_counit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.inv.as.app L =
      L.normalizationInv.equivalence.unit.hom :=
  (rfl)

end Unit

end TauCeti.EquivariantGroupoidLift
