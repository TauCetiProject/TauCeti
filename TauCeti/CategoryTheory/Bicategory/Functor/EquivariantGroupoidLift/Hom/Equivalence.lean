/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Isomorphism
public import TauCeti.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Equivalences of equivariant lifts

A morphism of lifts is an equivalence: its component functors are equivalences because
its prescribed-fiber comparisons identify their composites with equivalences. The inverse
strong transformation inherits its fiber comparison from the original comparison and the
component counits. The component units and counits then give compatible modifications.
Thus every morphism is an adjoint equivalence in the native bicategory of lifts.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Chapter 4: strong
  transformations, modifications, and pointwise equivalences.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.Hom

open CategoryTheory Bicategory Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions}

private instance isEquivalence_joint_app (φ : L.Hom L')
    (x : LocallyDiscrete (Γ × SingleObj H)) : (φ.joint.app x).toFunctor.IsEquivalence := by
  obtain ⟨p, a⟩ := x
  cases a
  exact isEquivalence_jointFunctor φ p

private noncomputable abbrev jointEquivalence (φ : L.Hom L') :
    Bicategory.Equivalence L.joint L'.joint := φ.joint.equivalenceOfIsEquivalence

private noncomputable def restrictedCounit (φ : L.Hom L') (p : Γ) :
    let P := (CategoryTheory.Prod.sectR p (SingleObj H)).toPseudofunctor
    P.whiskerLeft (jointEquivalence φ).inv ≫ P.whiskerLeft φ.joint ≅ 𝟙 (P.comp L'.joint) := by
  let P := (CategoryTheory.Prod.sectR p (SingleObj H)).toPseudofunctor
  let e := jointEquivalence φ
  exact Pseudofunctor.StrongTrans.isoMk (fun a => isoApp e.counit (P.obj a))
    (fun f => by simpa only [isoApp_hom] using! e.counit.hom.as.naturality (P.map f))

private noncomputable def inverseComparison (φ : L.Hom L') (p : Γ) :
    (CategoryTheory.Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeft
        (jointEquivalence φ).inv ≫ L.comparison p ≅ L'.comparison p := by
  let ε := restrictedCounit φ p
  exact whiskerLeftIso _ (φ.fiberIso p).symm ≪≫ (α_ _ _ _).symm ≪≫
    whiskerRightIso ε _ ≪≫ λ_ _

/-- The inverse lift morphism, with the chosen quasi-inverses of the component functors. -/
private noncomputable def inverse (φ : L.Hom L') : L'.Hom L where
  joint := (jointEquivalence φ).inv
  fiberIso := inverseComparison φ

private lemma inverse_fiberIso_hom_as_app (φ : L.Hom L') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((inverse φ).fiberIso p).hom.as.app a =
      (jointEquivalence φ).inv.app ⟨(p, a.as)⟩ ◁ (φ.fiberIso p).inv.as.app a ≫
        (α_ _ _ _).inv ≫
        (jointEquivalence φ).counit.hom.as.app ⟨(p, a.as)⟩ ▷ (L'.comparison p).app a ≫
        (λ_ ((L'.comparison p).app a)).hom := by
  have key {K J A : LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
      (R : J ⟶ K) (S : K ⟶ J) (c : J ⟶ A) (d : K ⟶ A)
      (i : S ≫ c ≅ d) (ε : R ≫ S ≅ 𝟙 J)
      (a : LocallyDiscrete (SingleObj H)) :
      (whiskerLeftIso R i.symm ≪≫ (α_ R S c).symm ≪≫
          whiskerRightIso ε c ≪≫ λ_ c).hom.as.app a =
        R.app a ◁ i.inv.as.app a ≫ (α_ (R.app a) (S.app a) (c.app a)).inv ≫
          ε.hom.as.app a ▷ c.app a ≫ (λ_ (c.app a)).hom := by
    simp
  let P := (CategoryTheory.Prod.sectR p (SingleObj H)).toPseudofunctor
  let e := jointEquivalence φ
  let ε := restrictedCounit φ p
  have h := key (P.whiskerLeft e.inv) (P.whiskerLeft e.hom)
    (L'.comparison p) (L.comparison p) (φ.fiberIso p) ε a
  refine h.trans ?_
  dsimp only [ε, restrictedCounit, Pseudofunctor.StrongTrans.isoMk]
  simp only [isoApp_hom]
  rfl

private noncomputable def inverseCounit (φ : L.Hom L') : (inverse φ).comp φ ≅ id L' :=
  isoMk (jointEquivalence φ).counit fun p a => by
    have key {C D A : Cat.{v, w}} (F : C ⟶ D) (G : D ⟶ C)
        (E : D ⟶ A) (E₀ : C ⟶ A) (i : F ≫ E ≅ E₀) (ε : G ≫ F ⟶ 𝟙 D) :
        ε ▷ E ≫ (λ_ E).hom =
          (α_ G F E).hom ≫ G ◁ i.hom ≫
            (G ◁ i.inv ≫ (α_ G F E).inv ≫ ε ▷ E ≫ (λ_ E).hom) := by
      simp
    simp only [id_fiberIso_hom_as_app, comp_fiberIso_hom_as_app,
      inverse_fiberIso_hom_as_app]
    simpa only [isoApp_hom, isoApp_inv] using!
      key (φ.joint.app ⟨(p, a.as)⟩) ((jointEquivalence φ).inv.app ⟨(p, a.as)⟩)
        ((L'.comparison p).app a) ((L.comparison p).app a)
        (isoApp (φ.fiberIso p) a) ((jointEquivalence φ).counit.hom.as.app ⟨(p, a.as)⟩)

private noncomputable def inverseUnit (φ : L.Hom L') : id L ≅ φ.comp (inverse φ) :=
  isoMk (jointEquivalence φ).unit fun p a => by
    have key {C D A : Cat.{v, w}} (F : C ⟶ D)
        [F.toFunctor.IsEquivalence] (E : D ⟶ A) (E₀ : C ⟶ A) (i : F ≫ E ≅ E₀) :
        (Cat.Hom.isoMk F.toFunctor.asEquivalence.unitIso).hom ▷ E₀ ≫
          (α_ F F.toFunctor.inv.toCatHom E₀).hom ≫
          F ◁ (F.toFunctor.inv.toCatHom ◁ i.inv ≫
            (α_ F.toFunctor.inv.toCatHom F E).inv ≫
            (Cat.Hom.isoMk F.toFunctor.asEquivalence.counitIso).hom ▷ E ≫ (λ_ E).hom) ≫
          i.hom = (λ_ E₀).hom := by
      ext X
      suffices h : E₀.toFunctor.map (F.toFunctor.asEquivalence.unit.app X) ≫
          i.inv.toNatTrans.app (F.toFunctor.inv.obj (F.toFunctor.obj X)) ≫
          E.toFunctor.map (F.toFunctor.asEquivalence.counit.app (F.toFunctor.obj X)) ≫
          i.hom.toNatTrans.app X = 𝟙 _ by
        simpa using! h
      have hi : E₀.toFunctor.map (F.toFunctor.asEquivalence.unit.app X) ≫
          i.inv.toNatTrans.app (F.toFunctor.inv.obj (F.toFunctor.obj X)) =
          i.inv.toNatTrans.app X ≫
            E.toFunctor.map (F.toFunctor.map (F.toFunctor.asEquivalence.unit.app X)) :=
        (Cat.Hom.toNatIso i).inv.naturality (F.toFunctor.asEquivalence.unit.app X)
      rw [reassoc_of% hi]
      have ht : E.toFunctor.map (F.toFunctor.map (F.toFunctor.asEquivalence.unit.app X)) ≫
          E.toFunctor.map (F.toFunctor.asEquivalence.counit.app (F.toFunctor.obj X)) = 𝟙 _ :=
        (E.toFunctor.map_comp _ _).symm.trans
          ((congrArg E.toFunctor.map (F.toFunctor.asEquivalence.functor_unit_comp X)).trans
            (E.toFunctor.map_id _))
      rw [reassoc_of% ht]
      simp
    simp only [id_fiberIso_hom_as_app, comp_fiberIso_hom_as_app,
      inverse_fiberIso_hom_as_app]
    have h := key (φ.joint.app ⟨(p, a.as)⟩)
      ((L'.comparison p).app a) ((L.comparison p).app a) (isoApp (φ.fiberIso p) a)
    simpa only [jointEquivalence, equivalenceOfIsEquivalence_unit_hom_as_app,
      equivalenceOfIsEquivalence_counit_hom_as_app, isoApp_hom, isoApp_inv] using! h

/-- Every morphism of equivariant lifts is an adjoint equivalence. Its forward morphism is
the given morphism, and its inverse uses the chosen quasi-inverses of the component functors.
The unit and counit are the compatible modifications induced by the component units and counits. -/
noncomputable def equivalence (φ : L.Hom L') : Bicategory.Equivalence L L' where
  hom := φ
  inv := inverse φ
  unit := inverseUnit φ
  counit := inverseCounit φ
  left_triangle := Iso.ext (Subsingleton.elim _ _)

@[simp]
lemma equivalence_hom (φ : L.Hom L') : φ.equivalence.hom = φ := (rfl)

/-- The inverse of the equivalence uses the chosen quasi-inverse on each joint fiber. -/
@[simp]
lemma equivalence_inv_jointFunctor (φ : L.Hom L') (p : Γ) :
    φ.equivalence.inv.jointFunctor p = (φ.jointFunctor p).inv := (rfl)

end TauCeti.EquivariantGroupoidLift.Hom
