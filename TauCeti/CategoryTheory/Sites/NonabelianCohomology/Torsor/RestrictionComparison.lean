/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.ContractedProduct

/-!
# Extension of structure group and restriction of torsors

Restriction by a continuous functor need not preserve local nonemptiness of a torsor.
Given an actual torsor identified equivariantly with the restricted sheaf, however,
its extension of structure group canonically identifies with the restricted extension.
This comparison is characterized by its value on the universal map into the extension.
It allows extension of structure group to be used with different presentations of
restricted torsors, in particular on slice sites.

The construction uses the universal property `Torsor.mapLift` of the contracted product,
as in Giraud, *Cohomologie non abélienne*, III, §1.3.
-/

public section

open CategoryTheory Opposite

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (u : D ⥤ C) [u.IsContinuous K J]
  {G H : Sheaf J GrpCat.{w}} (P : Torsor G) (φ : G ⟶ H)
  [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  (P' : Torsor ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj G))
  (e : P'.sheaf ⟶ (u.sheafPushforwardContinuous (Type w) K J).obj P.sheaf)

/-- The restriction of an extended torsor. A morphism from an actual restricted torsor
supplies its local sections; no preservation of covering families by `u` is required.
The abbreviation retains the original section types and action for computations. -/
noncomputable abbrev mapRestrict :
    Torsor ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj H) where
  sheaf := (u.sheafPushforwardContinuous (Type w) K J).obj (P.map φ).sheaf
  mulAction U := (P.map φ).mulAction (u.op.obj U)
  map_smul _ _ f g p := (P.map φ).map_smul (u.op.map f) g p
  coversTop X := K.superset_covering (by
    rintro Y a ⟨⟨V, ⟨p⟩⟩, ⟨b⟩⟩
    exact ⟨⟨V, ⟨(P.toMap φ).hom.app _ (e.hom.app _ p)⟩⟩, ⟨b⟩⟩) (P'.coversTop X)
  bijective U := (P.map φ).bijective (u.op.obj U)

/-- The sheaf of `mapRestrict` is the restriction of the extended sheaf. -/
lemma mapRestrict_sheaf : (P.mapRestrict u φ P' e).sheaf =
    (u.sheafPushforwardContinuous (Type w) K J).obj (P.map φ).sheaf := (rfl)

/-- The action on the restricted extension is the original action evaluated along `u`. -/
@[simp]
lemma mapRestrict_smul (U : Dᵒᵖ)
    (h : ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj H).obj.obj U)
    (q : (P.mapRestrict u φ P' e).sheaf.obj.obj U) :
    ((P.mapRestrict u φ P' e).mulAction U).smul h q =
      ((P.map φ).mulAction (u.op.obj U)).smul h q := (rfl)

variable (he : ∀ (U : Dᵒᵖ)
  (g : ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj G).obj.obj U)
  (p : P'.sheaf.obj.obj U), e.hom.app U (g • p) = (P.mulAction (u.op.obj U)).smul g (e.hom.app U p))

include he in
/-- Restricting the universal map `P → P.map φ`, and precomposing with the supplied
identification, is equivariant for the restricted group homomorphism. -/
lemma toMap_restrict_smul (U : Dᵒᵖ)
    (g : ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj G).obj.obj U)
    (p : P'.sheaf.obj.obj U) :
    (e ≫ (u.sheafPushforwardContinuous (Type w) K J).map (P.toMap φ)).hom.app U
        (g • p) =
      ((P.map φ).mulAction (u.op.obj U)).smul (φ.hom.app (u.op.obj U) g)
        ((e ≫ (u.sheafPushforwardContinuous (Type w) K J).map
          (P.toMap φ)).hom.app U p : (P.map φ).sheaf.obj.obj (u.op.obj U)) := by
  dsimp
  exact (congrArg ((P.toMap φ).hom.app (u.op.obj U)) (he U g p)).trans
    (P.toMap_smul φ g (e.hom.app U p))

variable [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)]

/-- Extending an actual restricted torsor identifies canonically with the restricted
extension. Any equivariant morphism into the restricted sheaf suffices. -/
noncomputable def mapRestrictIso :
    P'.map ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ) ≅
      P.mapRestrict u φ P' e :=
  asIso (P'.mapLift
    (R := P.mapRestrict u φ P' e)
    (e ≫ (u.sheafPushforwardContinuous (Type w) K J).map (P.toMap φ))
    (P.toMap_restrict_smul u φ P' e he))

/-- The restriction comparison sends the generator to the restricted universal map. -/
@[reassoc (attr := simp)]
lemma toMap_mapRestrictIso_hom :
    P'.toMap ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ) ≫
        (P.mapRestrictIso u φ P' e he).hom.hom =
      e ≫ (u.sheafPushforwardContinuous (Type w) K J).map (P.toMap φ) :=
  P'.toMap_mapLift _ _

section SuppliedTarget

variable (Q' : Torsor ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj H))
  (d : Q'.sheaf ⟶ (u.sheafPushforwardContinuous (Type w) K J).obj (P.map φ).sheaf)
  (hd : ∀ (U : Dᵒᵖ)
    (h : ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj H).obj.obj U)
    (q : Q'.sheaf.obj.obj U),
    d.hom.app U (h • q) = ((P.map φ).mulAction (u.op.obj U)).smul h
      (d.hom.app U q))

/-- The extension comparison with any supplied equivariantly identified restriction
of the extended torsor. An equivariant morphism of sheaves suffices, since
equivariant morphisms of torsors are invertible. -/
noncomputable def mapRestrictComparison :
    P'.map ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ) ≅ Q' :=
  P.mapRestrictIso u φ P' e he ≪≫
    (asIso (⟨d, hd⟩ : Q' ⟶ P.mapRestrict u φ P' e)).symm

/-- Under the supplied target identification, the comparison is the canonical one. -/
@[reassoc (attr := simp)]
lemma mapRestrictComparison_hom_hom_comp :
    (P.mapRestrictComparison u φ P' e he Q' d hd).hom.hom ≫ d =
      (P.mapRestrictIso u φ P' e he).hom.hom := by
  let f : Q' ⟶ P.mapRestrict u φ P' e := ⟨d, hd⟩
  have hf : (inv f).hom ≫ f.hom = 𝟙 _ := by
    rw [← comp_hom, IsIso.inv_hom_id, id_hom]
  exact (Category.assoc _ _ _).trans
    ((congrArg ((P.mapRestrictIso u φ P' e he).hom.hom ≫ ·) hf).trans
      (Category.comp_id _))

/-- The generator equation uniquely determines the comparison with any supplied
restricted extension. -/
lemma mapRestrictComparison_hom_unique
    (f : P'.map ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ) ⟶ Q')
    (hf : P'.toMap ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ) ≫
      f.hom ≫ d =
        e ≫ (u.sheafPushforwardContinuous (Type w) K J).map (P.toMap φ)) :
    f = (P.mapRestrictComparison u φ P' e he Q' d hd).hom := by
  apply map_hom_ext
  have : IsIso d := isIso_hom (⟨d, hd⟩ : Q' ⟶ P.mapRestrict u φ P' e)
  apply (cancel_mono d).1
  simpa only [Category.assoc, mapRestrictComparison_hom_hom_comp,
    toMap_mapRestrictIso_hom] using hf

end SuppliedTarget

section Naturality

variable {Q : Torsor G}
  (Q' : Torsor ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj G))
  (f : Q'.sheaf ⟶ (u.sheafPushforwardContinuous (Type w) K J).obj Q.sheaf)
  (hf : ∀ (U : Dᵒᵖ)
    (g : ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj G).obj.obj U)
    (q : Q'.sheaf.obj.obj U),
    f.hom.app U (g • q) = (Q.mulAction (u.op.obj U)).smul g (f.hom.app U q))

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
/-- Restriction of a morphism between extended torsors, for the actual torsors
`mapRestrict` on the restricted sheaves. -/
noncomputable def mapRestrictMap (a : P.map φ ⟶ Q.map φ) :
    P.mapRestrict u φ P' e ⟶ Q.mapRestrict u φ Q' f where
  hom := (u.sheafPushforwardContinuous (Type w) K J).map a.hom
  map_smul U h q := a.map_smul (u.op.obj U) h q

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
/-- The restriction of a morphism of extended torsors is precomposition on sheaves. -/
@[simp]
lemma mapRestrictMap_hom (a : P.map φ ⟶ Q.map φ) :
    (P.mapRestrictMap u φ P' e Q' f a).hom =
      (u.sheafPushforwardContinuous (Type w) K J).map a.hom := (rfl)

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
/-- Restricting the identity of an extended torsor gives the identity. -/
@[simp]
lemma mapRestrictMap_id :
    P.mapRestrictMap u φ P' e P' e (𝟙 (P.map φ)) = 𝟙 (P.mapRestrict u φ P' e) := by
  ext1
  simp

omit [HasWeakSheafify K (Type w)] [K.WEqualsLocallyBijective (Type w)] in
/-- Restriction of morphisms between extended torsors preserves composition. -/
lemma mapRestrictMap_comp {R : Torsor G}
    (R' : Torsor ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj G))
    (r : R'.sheaf ⟶ (u.sheafPushforwardContinuous (Type w) K J).obj R.sheaf)
    (a : P.map φ ⟶ Q.map φ) (b : Q.map φ ⟶ R.map φ) :
    P.mapRestrictMap u φ P' e R' r (a ≫ b) =
      P.mapRestrictMap u φ P' e Q' f a ≫ Q.mapRestrictMap u φ Q' f R' r b := by
  ext1
  simp

/-- The extension comparison is natural for compatible maps of torsors and their
extensions. The extension map on the restricted source is induced by `mapLift`. -/
lemma mapRestrictIso_naturality (a : P ⟶ Q) (a' : P' ⟶ Q')
    (b : P.map φ ⟶ Q.map φ)
    (ha : a'.hom ≫ f = e ≫ (u.sheafPushforwardContinuous (Type w) K J).map a.hom)
    (hb : P.toMap φ ≫ b.hom = a.hom ≫ Q.toMap φ) :
    P'.mapLift (a'.hom ≫ Q'.toMap
        ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ))
        (fun U g p ↦ by simp [a'.map_smul, toMap_smul]) ≫
        (Q.mapRestrictIso u φ Q' f hf).hom =
      (P.mapRestrictIso u φ P' e he).hom ≫ P.mapRestrictMap u φ P' e Q' f b := by
  apply map_hom_ext
  simp only [comp_hom, Category.assoc, toMap_mapLift_assoc,
    toMap_mapRestrictIso_hom_assoc, toMap_mapRestrictIso_hom, mapRestrictMap_hom]
  rw [← Category.assoc a'.hom, ha]
  simpa only [Category.assoc, Functor.map_comp] using
    congrArg (fun k ↦ e ≫ (u.sheafPushforwardContinuous (Type w) K J).map k) hb.symm

end Naturality

/-- For identity restriction and the canonical identity identifications, the comparison
with the original extended torsor is the identity isomorphism. -/
@[simp]
lemma mapRestrictComparison_id :
    P.mapRestrictComparison (𝟭 C) φ P
      ((Functor.sheafPushforwardContinuousId (Type w) J).inv.app P.sheaf)
      (fun _ _ _ ↦ rfl) (P.map φ)
      ((Functor.sheafPushforwardContinuousId (Type w) J).inv.app (P.map φ).sheaf)
      (fun _ _ _ ↦ rfl) = Iso.refl (P.map φ) := by
  apply Iso.ext
  symm
  apply mapRestrictComparison_hom_unique
  ext U p
  rfl

/-- Restriction of the extension comparison along a second continuous functor equals
comparison along the composite, with the composite sheaf identification. -/
lemma mapRestrictIso_comp {E : Type u₃} [Category.{v₃} E]
    {L : GrothendieckTopology E} (v : E ⥤ D) [v.IsContinuous L K]
    [HasWeakSheafify L (Type w)] [L.WEqualsLocallyBijective (Type w)]
    (P'' : Torsor ((v.sheafPushforwardContinuous GrpCat.{w} L K).obj
      ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj G)))
    (e' : P''.sheaf ⟶ (v.sheafPushforwardContinuous (Type w) L K).obj P'.sheaf)
    (he' : ∀ (U : Eᵒᵖ)
      (g : ((v.sheafPushforwardContinuous GrpCat.{w} L K).obj
        ((u.sheafPushforwardContinuous GrpCat.{w} K J).obj G)).obj.obj U)
      (p : P''.sheaf.obj.obj U),
      e'.hom.app U (g • p) = (P'.mulAction (v.op.obj U)).smul g (e'.hom.app U p)) :
    letI := Functor.isContinuous_comp v u L K J
    let ec := e' ≫ (v.sheafPushforwardContinuous (Type w) L K).map e ≫
      (v.sheafPushforwardContinuousComp u (Type w) L K J).hom.app P.sheaf
    let hec : ∀ (U : Eᵒᵖ)
      (g : (((v ⋙ u).sheafPushforwardContinuous GrpCat.{w} L J).obj G).obj.obj U)
      (p : P''.sheaf.obj.obj U),
      ec.hom.app U ((P''.mulAction U).smul g p) = (P.mulAction ((v ⋙ u).op.obj U)).smul g
        (ec.hom.app U p) := by
          intro U g p
          dsimp [ec]
          exact (congrArg (e.hom.app (v.op.obj U)) (he' U g p)).trans
            (he (v.op.obj U) g (e'.hom.app U p))
    (P.mapRestrictIso (v ⋙ u) φ P'' ec hec).hom.hom =
      (P'.mapRestrictIso v ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ)
        P'' e' he').hom.hom ≫
      (v.sheafPushforwardContinuous (Type w) L K).map
        (P.mapRestrictIso u φ P' e he).hom.hom ≫
      (v.sheafPushforwardContinuousComp u (Type w) L K J).hom.app (P.map φ).sheaf := by
  let := Functor.isContinuous_comp v u L K J
  intro ec hec
  let b : P'.mapRestrict v ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ)
      P'' e' ⟶ P.mapRestrict (v ⋙ u) φ P'' ec :=
    { hom := (v.sheafPushforwardContinuous (Type w) L K).map
        (P.mapRestrictIso u φ P' e he).hom.hom ≫
        (v.sheafPushforwardContinuousComp u (Type w) L K J).hom.app (P.map φ).sheaf
      map_smul U h q := by
        dsimp
        exact (P.mapRestrictIso u φ P' e he).hom.map_smul (v.op.obj U) h q }
  have hb : (P'.mapRestrictIso v
      ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ) P'' e' he').hom ≫ b =
      (P.mapRestrictIso (v ⋙ u) φ P'' ec hec).hom := by
    apply map_hom_ext
    calc
      _ = e' ≫ (v.sheafPushforwardContinuous (Type w) L K).map
          (P'.toMap ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ)) ≫ b.hom := by
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ b.hom) (P'.toMap_mapRestrictIso_hom v
            ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ) P'' e' he')).trans
              (Category.assoc _ _ _))
      _ = e' ≫ (v.sheafPushforwardContinuous (Type w) L K).map
          (P'.toMap ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ) ≫
            (P.mapRestrictIso u φ P' e he).hom.hom) ≫
          (v.sheafPushforwardContinuousComp u (Type w) L K J).hom.app
            (P.map φ).sheaf := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ e' ≫ k ≫
            (v.sheafPushforwardContinuousComp u (Type w) L K J).hom.app (P.map φ).sheaf)
          ((v.sheafPushforwardContinuous (Type w) L K).map_comp
            (P'.toMap ((u.sheafPushforwardContinuous GrpCat.{w} K J).map φ))
            (P.mapRestrictIso u φ P' e he).hom.hom).symm
      _ = e' ≫ (v.sheafPushforwardContinuous (Type w) L K).map
          (e ≫ (u.sheafPushforwardContinuous (Type w) K J).map (P.toMap φ)) ≫
          (v.sheafPushforwardContinuousComp u (Type w) L K J).hom.app
            (P.map φ).sheaf := by rw [toMap_mapRestrictIso_hom]
      _ = ec ≫ ((v ⋙ u).sheafPushforwardContinuous (Type w) L J).map
          (P.toMap φ) := by
        simpa only [ec, Functor.map_comp, Functor.comp_map, Category.assoc] using
          congrArg (fun k ↦ e' ≫ (v.sheafPushforwardContinuous (Type w) L K).map e ≫ k)
            ((v.sheafPushforwardContinuousComp u (Type w) L K J).hom.naturality
              (P.toMap φ))
      _ = _ := (P.toMap_mapRestrictIso_hom (v ⋙ u) φ P'' ec hec).symm
  exact (congrArg Hom.hom hb).symm

end CategoryTheory.Sheaf.Torsor
