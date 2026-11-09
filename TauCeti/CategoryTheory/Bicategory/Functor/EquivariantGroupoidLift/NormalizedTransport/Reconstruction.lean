/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Hom
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Isomorphism

/-!
# Reconstructing morphisms of equivariant lifts

A coherent comparison of normalized transports determines a strong transformation of their
joint pseudofunctors. Its components on the prescribed categories are identity functors, and
its cell at `(g, a)` is the transport comparison at `g`, whiskered by the action of `a`.
The mixed equivariance square is precisely what makes these cells respect joint composition.
The unit equation then supplies an invertible modification on each prescribed fiber, giving
a morphism of the reconstructed equivariant lifts. Canonical identity and composition
modifications assemble these constructions into `reconstructionPseudofunctor`, from the
locally discrete bicategory of normalized transports to the bicategory of lifts.

This construction uses `NormalizedTransport.joint`, the identity-component comparison lemmas
in `TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat`, and the native
strong-transformation and modification constructors. It follows the conventions of Johnson–Yau,
*2-Dimensional Categories*, Chapter 4, for strong transformations and modifications.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.NormalizedTransport.Hom

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {N N' N'' : NormalizedTransport Γ actions} (φ : N ⟶ N')

/-- Compare the joint functors by whiskering the transport comparison with the action. -/
noncomputable def jointIso {X Y : Γ × SingleObj H} (f : X ⟶ Y) :
    N.jointFunctor f ≅ N'.jointFunctor f :=
  Functor.isoWhiskerLeft (act actions X.1 f.2) (φ.transportIso f.1)

@[simp]
lemma jointIso_hom_app {X Y : Γ × SingleObj H} (f : X ⟶ Y) (x : fiber actions X.1) :
    (φ.jointIso f).hom.app x = (φ.transportIso f.1).hom.app ((act actions X.1 f.2).obj x) :=
  (rfl)

@[simp]
lemma jointIso_inv_app {X Y : Γ × SingleObj H} (f : X ⟶ Y) (x : fiber actions X.1) :
    (φ.jointIso f).inv.app x = (φ.transportIso f.1).inv.app ((act actions X.1 f.2).obj x) :=
  (rfl)

/-- The joint comparison preserves the joint unit. -/
@[reassoc]
lemma jointIso_hom_app_comp_jointId (X : Γ × SingleObj H) (x : fiber actions X.1) :
    (φ.jointIso (𝟙 X)).hom.app x ≫ (N'.jointId X).hom.app x =
      (N.jointId X).hom.app x := by
  simp only [jointIso_hom_app, jointId_hom_app, prod_id_fst, prod_id_snd]
  rw [← (φ.transportIso (𝟙 X.1)).hom.naturality_assoc]
  simp only [Functor.id_obj, φ.transportIso_unit]

@[reassoc]
private lemma transportIso_hom_app_comp_transportComp_inv_app {p q r : Γ}
    (g : p ⟶ q) (h : q ⟶ r) (gh : p ⟶ r) (hgh : g ≫ h = gh) (x : fiber actions p) :
    (φ.transportIso gh).hom.app x ≫ (N'.transportComp g h gh hgh).inv.app x =
      (N.transportComp g h gh hgh).inv.app x ≫
        (φ.transportIso h).hom.app ((N.transport g).obj x) ≫
          (N'.transport h).map ((φ.transportIso g).hom.app x) := by
  rw [← cancel_epi ((N.transportComp g h gh hgh).hom.app x)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [φ.transportIso_comp_assoc]
  simp

/-- The mixed square and parameter composition equation together imply joint composition
coherence. -/
@[reassoc]
lemma jointIso_hom_app_comp_jointComp {X Y Z : Γ × SingleObj H}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : f ≫ g = fg) (x : fiber actions X.1) :
    (φ.jointIso fg).hom.app x ≫ (N'.jointComp f g fg hfg).hom.app x =
      (N.jointComp f g fg hfg).hom.app x ≫
        (φ.jointIso g).hom.app ((N.jointFunctor f).obj x) ≫
          (N'.jointFunctor g).map ((φ.jointIso f).hom.app x) := by
  simp only [jointIso_hom_app, jointComp_hom_app, Category.assoc, Functor.comp_obj,
    Functor.comp_map]
  rw [← (φ.transportIso fg.1).hom.naturality_assoc]
  rw [φ.transportIso_hom_app_comp_transportComp_inv_app_assoc]
  rw [← Functor.map_comp, ← φ.transportIso_comm, Functor.map_comp]
  rw [← (φ.transportIso g.1).hom.naturality_assoc]
  rfl

/-- Reconstruct a strong transformation of joint pseudofunctors. Its fiber components are
identities, not independently chosen equivalences. -/
-- Expose the identity components so the naturality equations retain their literal endpoints.
@[expose] noncomputable def jointHom : N.joint ⟶ N'.joint where
  app _ := 𝟙 _
  naturality f := ρ_ _ ≪≫ Cat.Hom.isoMk (φ.jointIso f.as) ≪≫ (λ_ _).symm
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete N.joint N'.joint (fun _ ↦ 𝟙 _)
      (fun f ↦ ρ_ _ ≪≫ Cat.Hom.isoMk (φ.jointIso f.as) ≪≫ (λ_ _).symm) η
  naturality_id X :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_id _ _ _
      (φ.jointIso_hom_app_comp_jointId X.as)
  naturality_comp f g :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _ _
      (φ.jointIso_hom_app_comp_jointComp f.as g.as (f.as ≫ g.as) rfl)

@[simp]
lemma jointHom_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    φ.jointHom.app X = 𝟙 (fiber actions X.as.1) := (rfl)

@[simp]
lemma jointHom_naturality_hom_app {X Y : LocallyDiscrete (Γ × SingleObj H)}
    (f : X ⟶ Y) (x : fiber actions X.as.1) :
    (φ.jointHom.naturality f).hom.toNatTrans.app x =
      (φ.transportIso f.as.1).hom.app ((act actions X.as.1 f.as.2).obj x) :=
  Cat.rightUnitor_trans_leftUnitor_symm_hom_app _ _

@[simp]
lemma jointHom_naturality_inv_app {X Y : LocallyDiscrete (Γ × SingleObj H)}
    (f : X ⟶ Y) (x : fiber actions X.as.1) :
    (φ.jointHom.naturality f).inv.toNatTrans.app x =
      (φ.transportIso f.as.1).inv.app ((act actions X.as.1 f.as.2).obj x) :=
  Cat.rightUnitor_trans_leftUnitor_symm_inv_app _ _

/-- The reconstructed joint transformation respects the prescribed fiber comparisons. The
components of this invertible modification are the canonical left unitors. -/
noncomputable def jointHomFiberIso (p : Γ) :
    (Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeft φ.jointHom ≫ N'.comparison p ≅
      N.comparison p :=
  Pseudofunctor.StrongTrans.isoMk (fun _ ↦ λ_ (𝟙 (fiber actions p))) (fun f ↦ by
    ext x
    -- Fiber restriction and whiskering have the prescribed categories only after unfolding;
    -- on components every unitor and associator is an identity.
    simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app]
    rw [Pseudofunctor.StrongTrans.comp_naturality_hom_app]
    change 𝟙 _ ≫ (N.transportId p).hom.app ((act actions p f.as).obj x) =
      (((𝟙 _ ≫ (φ.transportIso (𝟙 p)).hom.app ((act actions p f.as).obj x) ≫ 𝟙 _) ≫
        (N'.transportId p).hom.app ((act actions p f.as).obj x)) ≫
          (act actions p f.as).map (𝟙 x))
    -- Apply the identity-map law as a term: the identity in the displayed goal carries
    -- the definitionally equal category structure from the restricted joint fiber.
    have hmap : (act actions p f.as).map (𝟙 x) = 𝟙 _ := (act actions p f.as).map_id x
    rw [hmap]
    simpa using (φ.transportIso_unit p ((act actions p f.as).obj x)).symm)

/-- A coherent comparison of normalized transports gives a morphism of the reconstructed
lifts, including compatibility with their prescribed action comparisons. -/
-- Expose the joint transformation for the component equations below.
@[expose] noncomputable def toLiftHom : N.toLift.Hom N'.toLift where
  joint := φ.jointHom
  fiberIso := φ.jointHomFiberIso

@[simp]
lemma toLiftHom_joint : φ.toLiftHom.joint = φ.jointHom := (rfl)

@[simp]
lemma toLiftHom_fiberIso_hom_as_app (p : Γ) (a : LocallyDiscrete (SingleObj H)) :
    (φ.toLiftHom.fiberIso p).hom.as.app a = (λ_ (𝟙 (fiber actions p))).hom := (rfl)

@[simp]
lemma toLiftHom_fiberIso_inv_as_app (p : Γ) (a : LocallyDiscrete (SingleObj H)) :
    (φ.toLiftHom.fiberIso p).inv.as.app a = (λ_ (𝟙 (fiber actions p))).inv := (rfl)

/-- Reconstruction preserves the identity comparison up to a compatible invertible
modification with identity components. -/
noncomputable def toLiftHomIdIso (N : NormalizedTransport Γ actions) :
    (𝟙 N : N ⟶ N).toLiftHom ≅ EquivariantGroupoidLift.Hom.id N.toLift :=
  EquivariantGroupoidLift.Hom.isoMk
    (Pseudofunctor.StrongTrans.isoMk (fun _ ↦ Iso.refl _) (fun f ↦ by
      exact Cat.rightUnitor_trans_leftUnitor_symm_id_modification
        (Cat.Hom.isoMk ((𝟙 N : N ⟶ N).jointIso f.as)) (fun x ↦ by simp [jointIso])))
    (fun p a ↦ by
      rw [EquivariantGroupoidLift.Hom.id_fiberIso_hom_as_app,
        toLiftHom_fiberIso_hom_as_app]
      -- The modification component is the identity on the identity functor.
      change 𝟙 (𝟙 (fiber actions p)) ▷ 𝟙 (fiber actions p) ≫
        (λ_ (𝟙 (fiber actions p))).hom = (λ_ (𝟙 (fiber actions p))).hom
      simp)

/-- Reconstruction preserves composition up to the compatible modification with inverse
left unitor components. -/
noncomputable def toLiftHomCompIso (φ : N ⟶ N') (ψ : N' ⟶ N'') :
    (φ ≫ ψ).toLiftHom ≅ φ.toLiftHom.comp ψ.toLiftHom :=
  EquivariantGroupoidLift.Hom.isoMk
    (Pseudofunctor.StrongTrans.isoMk (fun _ ↦ (λ_ _).symm) (fun f ↦ by
      exact Cat.rightUnitor_trans_leftUnitor_symm_trans_modification
        (Cat.Hom.isoMk (φ.jointIso f.as)) (Cat.Hom.isoMk (ψ.jointIso f.as))
        (Cat.Hom.isoMk ((φ ≫ ψ).jointIso f.as)) (fun x ↦ by simp [jointIso])))
    (fun p a ↦ by
      simp only [EquivariantGroupoidLift.Hom.comp_fiberIso_hom_as_app,
        toLiftHom_fiberIso_hom_as_app]
      -- All fiber components are identities; keep one category fixed for coherence.
      change (λ_ (𝟙 (fiber actions p))).inv ▷ 𝟙 (fiber actions p) ≫
          (α_ (𝟙 (fiber actions p)) (𝟙 (fiber actions p)) (𝟙 (fiber actions p))).hom ≫
            𝟙 (fiber actions p) ◁ (λ_ (𝟙 (fiber actions p))).hom ≫
              (λ_ (𝟙 (fiber actions p))).hom = (λ_ (𝟙 (fiber actions p))).hom
      bicategory)

@[simp]
lemma toLiftHomIdIso_hom_joint_as_app (N : NormalizedTransport Γ actions)
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (toLiftHomIdIso N).hom.joint.as.app X = 𝟙 (𝟙 (fiber actions X.as.1)) := by
  simp only [toLiftHomIdIso, EquivariantGroupoidLift.Hom.isoMk_hom_joint]
  rfl

@[simp]
lemma toLiftHomIdIso_inv_joint_as_app (N : NormalizedTransport Γ actions)
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (toLiftHomIdIso N).inv.joint.as.app X = 𝟙 (𝟙 (fiber actions X.as.1)) := by
  simp only [toLiftHomIdIso, EquivariantGroupoidLift.Hom.isoMk_inv_joint]
  rfl

@[simp]
lemma toLiftHomCompIso_hom_joint_as_app (φ : N ⟶ N') (ψ : N' ⟶ N'')
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (toLiftHomCompIso φ ψ).hom.joint.as.app X = (λ_ (𝟙 (fiber actions X.as.1))).inv := by
  simp only [toLiftHomCompIso, EquivariantGroupoidLift.Hom.isoMk_hom_joint]
  rfl

@[simp]
lemma toLiftHomCompIso_inv_joint_as_app (φ : N ⟶ N') (ψ : N' ⟶ N'')
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (toLiftHomCompIso φ ψ).inv.joint.as.app X = (λ_ (𝟙 (fiber actions X.as.1))).hom := by
  simp only [toLiftHomCompIso, EquivariantGroupoidLift.Hom.isoMk_inv_joint]
  rfl

end TauCeti.EquivariantGroupoidLift.NormalizedTransport.Hom

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- Reconstruct equivariant lifts and their morphisms from normalized transport data.
The unit and compositor are the canonical compatible modifications, and their coherence
follows from uniqueness of compatible modifications. -/
-- Expose the object and arrow carriers for the characteristic equations below.
@[expose] noncomputable def reconstructionPseudofunctor :
    LocallyDiscrete (NormalizedTransport Γ actions) ⥤ᵖ EquivariantGroupoidLift Γ actions where
  obj N := N.as.toLift
  map φ := φ.as.toLiftHom
  map₂ η := eqToHom (congrArg (fun φ ↦ NormalizedTransport.Hom.toLiftHom φ.as)
    (LocallyDiscrete.eq_of_hom η))
  mapId N := NormalizedTransport.Hom.toLiftHomIdIso N.as
  mapComp φ ψ := NormalizedTransport.Hom.toLiftHomCompIso φ.as ψ.as
  map₂_id _ := Subsingleton.elim _ _
  map₂_comp _ _ := Subsingleton.elim _ _
  map₂_whisker_left := by intros; exact Subsingleton.elim _ _
  map₂_whisker_right := by intros; exact Subsingleton.elim _ _
  map₂_associator _ _ _ := Subsingleton.elim _ _
  map₂_left_unitor _ := Subsingleton.elim _ _
  map₂_right_unitor _ := Subsingleton.elim _ _

@[simp]
lemma reconstructionPseudofunctor_obj (N : LocallyDiscrete (NormalizedTransport Γ actions)) :
    (reconstructionPseudofunctor actions).obj N = N.as.toLift := (rfl)

lemma reconstructionPseudofunctor_map {N N' : LocallyDiscrete (NormalizedTransport Γ actions)}
    (φ : N ⟶ N') :
    (reconstructionPseudofunctor actions).map φ = φ.as.toLiftHom := (rfl)

lemma reconstructionPseudofunctor_map₂ {N N' : LocallyDiscrete (NormalizedTransport Γ actions)}
    {φ ψ : N ⟶ N'} (η : φ ⟶ ψ) :
    (reconstructionPseudofunctor actions).map₂ η =
      eqToHom (congrArg (fun φ ↦ NormalizedTransport.Hom.toLiftHom φ.as)
        (LocallyDiscrete.eq_of_hom η)) := (rfl)

/-- The unit cell of reconstruction is the compatible identity modification. -/
lemma reconstructionPseudofunctor_mapId (N : LocallyDiscrete (NormalizedTransport Γ actions)) :
    (reconstructionPseudofunctor actions).mapId N =
      NormalizedTransport.Hom.toLiftHomIdIso N.as := (rfl)

/-- The compositor of reconstruction is the compatible inverse-unitor modification. -/
lemma reconstructionPseudofunctor_mapComp
    {N N' N'' : LocallyDiscrete (NormalizedTransport Γ actions)} (φ : N ⟶ N') (ψ : N' ⟶ N'') :
    (reconstructionPseudofunctor actions).mapComp φ ψ =
      NormalizedTransport.Hom.toLiftHomCompIso φ.as ψ.as := (rfl)

end TauCeti.EquivariantGroupoidLift
