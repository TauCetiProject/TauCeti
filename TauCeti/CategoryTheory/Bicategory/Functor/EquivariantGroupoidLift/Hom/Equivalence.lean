/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Isomorphism
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

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

/-- Every component of the joint transformation of a lift morphism is an equivalence. -/
instance isEquivalence_joint_app (φ : L.Hom L')
    (x : LocallyDiscrete (Γ × SingleObj H)) : (φ.joint.app x).toFunctor.IsEquivalence := by
  obtain ⟨p, a⟩ := x
  cases a
  exact isEquivalence_jointFunctor φ p

private lemma inverseComparison_hom_as_app
    {K J A : LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
    (R : J ⟶ K) (S : K ⟶ J) (c : J ⟶ A) (d : K ⟶ A)
    (i : S ≫ c ≅ d) (ε : R ≫ S ≅ 𝟙 J) (a : LocallyDiscrete (SingleObj H)) :
    (whiskerLeftIso R i.symm ≪≫ (α_ R S c).symm ≪≫
        whiskerRightIso ε c ≪≫ λ_ c).hom.as.app a =
      R.app a ◁ i.inv.as.app a ≫ (α_ (R.app a) (S.app a) (c.app a)).inv ≫
        ε.hom.as.app a ▷ c.app a ≫ (λ_ (c.app a)).hom := by
  simp

private lemma inverseComparison_inv_as_app
    {K J A : LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
    (R : J ⟶ K) (S : K ⟶ J) (c : J ⟶ A) (d : K ⟶ A)
    (i : S ≫ c ≅ d) (ε : R ≫ S ≅ 𝟙 J) (a : LocallyDiscrete (SingleObj H)) :
    (whiskerLeftIso R i.symm ≪≫ (α_ R S c).symm ≪≫
        whiskerRightIso ε c ≪≫ λ_ c).inv.as.app a =
      (λ_ (c.app a)).inv ≫ ε.inv.as.app a ▷ c.app a ≫
        (α_ (R.app a) (S.app a) (c.app a)).hom ≫ R.app a ◁ i.hom.as.app a := by
  simp
  rfl

private lemma inverseCounit_compatibility {C D A : Cat.{v, w}}
    (F : C ⟶ D) (G : D ⟶ C) (E : D ⟶ A) (E₀ : C ⟶ A)
    (i : F ≫ E ≅ E₀) (ε : G ≫ F ⟶ 𝟙 D) :
    ε ▷ E ≫ (λ_ E).hom =
      (α_ G F E).hom ≫ G ◁ i.hom ≫
        (G ◁ i.inv ≫ (α_ G F E).inv ≫ ε ▷ E ≫ (λ_ E).hom) := by
  simp

private lemma inverseUnit_compatibility {C D A : Cat.{v, w}}
    (F : C ⟶ D) [F.toFunctor.IsEquivalence] (E : D ⟶ A) (E₀ : C ⟶ A)
    (i : F ≫ E ≅ E₀) :
    (Cat.Hom.isoMk F.toFunctor.asEquivalence.unitIso).hom ▷ E₀ ≫
        (α_ F F.toFunctor.inv.toCatHom E₀).hom ≫
        F ◁ (F.toFunctor.inv.toCatHom ◁ i.inv ≫
          (α_ F.toFunctor.inv.toCatHom F E).inv ≫
          (Cat.Hom.isoMk F.toFunctor.asEquivalence.counitIso).hom ▷ E ≫ (λ_ E).hom) ≫
        i.hom = (λ_ E₀).hom := by
  let adj := F.toFunctor.asEquivalence.toAdjunction.toCat
  apply (cancel_epi (λ_ E₀).inv).mp
  have h := congrArg (fun m => m ≫ i.hom) (adj.homEquiv₁.symm_apply_apply i.inv)
  simpa only [Bicategory.Adjunction.homEquiv₁_symm_apply,
    Bicategory.Adjunction.homEquiv₁_apply, Category.assoc, Iso.inv_hom_id,
    Iso.inv_hom_id_assoc] using! h

/-- Every morphism of equivariant lifts is an adjoint equivalence. Its forward morphism is
the given morphism, and its inverse uses the chosen quasi-inverses of the component functors.
The unit and counit are the compatible modifications induced by the component units and counits. -/
-- Keep the inverse and isomorphism records inline to expose their carriers while keeping
-- the compatibility proofs private.
@[expose] noncomputable def equivalence (φ : L.Hom L') : Bicategory.Equivalence L L' where
  hom := φ
  inv := {
    joint := φ.joint.equivalenceOfIsEquivalence.inv
    fiberIso p :=
      let P := (CategoryTheory.Prod.sectR p (SingleObj H)).toPseudofunctor
      let e := φ.joint.equivalenceOfIsEquivalence
      whiskerLeftIso _ (φ.fiberIso p).symm ≪≫ (α_ _ _ _).symm ≪≫
        whiskerRightIso
          (Pseudofunctor.StrongTrans.isoMk (fun a => isoApp e.counit (P.obj a))
            (fun f => by simpa only [isoApp_hom] using! e.counit.hom.as.naturality (P.map f)))
          _ ≪≫ λ_ _ }
  unit := isoMk φ.joint.equivalenceOfIsEquivalence.unit
    (fun p a => by
      simp only [EquivariantGroupoidLift.id_fiberIso, EquivariantGroupoidLift.comp_fiberIso,
        id_fiberIso_hom_as_app, comp_fiberIso_hom_as_app,
        inverseComparison_hom_as_app, Pseudofunctor.StrongTrans.isoMk]
      have h := inverseUnit_compatibility (φ.joint.app ⟨(p, a.as)⟩)
        ((L'.comparison p).app a) ((L.comparison p).app a) (isoApp (φ.fiberIso p) a)
      simpa only [equivalenceOfIsEquivalence_unit_hom_as_app,
        equivalenceOfIsEquivalence_counit_hom_as_app, isoApp_hom, isoApp_inv] using! h)
  counit := isoMk φ.joint.equivalenceOfIsEquivalence.counit
    (fun p a => by
      simp only [EquivariantGroupoidLift.id_fiberIso, EquivariantGroupoidLift.comp_fiberIso,
        id_fiberIso_hom_as_app, comp_fiberIso_hom_as_app,
        inverseComparison_hom_as_app, Pseudofunctor.StrongTrans.isoMk]
      simpa only [isoApp_hom, isoApp_inv] using!
        inverseCounit_compatibility (φ.joint.app ⟨(p, a.as)⟩)
          (φ.joint.equivalenceOfIsEquivalence.inv.app ⟨(p, a.as)⟩)
          ((L'.comparison p).app a) ((L.comparison p).app a)
          (isoApp (φ.fiberIso p) a)
          (φ.joint.equivalenceOfIsEquivalence.counit.hom.as.app ⟨(p, a.as)⟩))
  left_triangle := Iso.ext (Subsingleton.elim _ _)

@[simp]
lemma equivalence_hom (φ : L.Hom L') : φ.equivalence.hom = φ := (rfl)

/-- The joint transformation of the inverse is the chosen pointwise inverse. -/
@[simp]
lemma equivalence_inv_joint (φ : L.Hom L') :
    φ.equivalence.inv.joint = φ.joint.equivalenceOfIsEquivalence.inv := (rfl)

-- Keep the dependent unit/counit and fiber-comparison equations named: ordinary importing
-- simp does not preserve a common normal form for their carriers.
/-- The unit projects to the unit of the joint pointwise equivalence. -/
lemma equivalence_unit_hom_joint (φ : L.Hom L') :
    φ.equivalence.unit.hom.joint = φ.joint.equivalenceOfIsEquivalence.unit.hom :=
  TauCeti.EquivariantGroupoidLift.Hom.isoMk_hom_joint _ _

lemma equivalence_unit_inv_joint (φ : L.Hom L') :
    φ.equivalence.unit.inv.joint = φ.joint.equivalenceOfIsEquivalence.unit.inv :=
  TauCeti.EquivariantGroupoidLift.Hom.isoMk_inv_joint _ _

/-- The counit projects to the counit of the joint pointwise equivalence. -/
lemma equivalence_counit_hom_joint (φ : L.Hom L') :
    φ.equivalence.counit.hom.joint = φ.joint.equivalenceOfIsEquivalence.counit.hom :=
  TauCeti.EquivariantGroupoidLift.Hom.isoMk_hom_joint _ _

lemma equivalence_counit_inv_joint (φ : L.Hom L') :
    φ.equivalence.counit.inv.joint = φ.joint.equivalenceOfIsEquivalence.counit.inv :=
  TauCeti.EquivariantGroupoidLift.Hom.isoMk_inv_joint _ _

/-- The inverse fiber comparison is induced by the original comparison and component counit. -/
lemma equivalence_inv_fiberIso_hom_as_app (φ : L.Hom L') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (φ.equivalence.inv.fiberIso p).hom.as.app a =
      φ.joint.equivalenceOfIsEquivalence.inv.app ⟨(p, a.as)⟩ ◁ (φ.fiberIso p).inv.as.app a ≫
        (α_ _ _ _).inv ≫
        φ.joint.equivalenceOfIsEquivalence.counit.hom.as.app ⟨(p, a.as)⟩ ▷
          (L'.comparison p).app a ≫ (λ_ ((L'.comparison p).app a)).hom := by
  dsimp only [equivalence]
  rw [inverseComparison_hom_as_app]
  simp only [Pseudofunctor.StrongTrans.isoMk, isoApp_hom]
  rfl

/-- The inverse direction of the inverse fiber comparison. -/
lemma equivalence_inv_fiberIso_inv_as_app (φ : L.Hom L') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (φ.equivalence.inv.fiberIso p).inv.as.app a =
      (λ_ ((L'.comparison p).app a)).inv ≫
        φ.joint.equivalenceOfIsEquivalence.counit.inv.as.app ⟨(p, a.as)⟩ ▷
          (L'.comparison p).app a ≫ (α_ _ _ _).hom ≫
        φ.joint.equivalenceOfIsEquivalence.inv.app ⟨(p, a.as)⟩ ◁ (φ.fiberIso p).hom.as.app a := by
  dsimp only [equivalence]
  rw [inverseComparison_inv_as_app]
  simp only [Pseudofunctor.StrongTrans.isoMk, isoApp_inv]
  rfl

/-- The inverse of the equivalence uses the chosen quasi-inverse on each joint fiber. -/
@[simp]
lemma equivalence_inv_jointFunctor (φ : L.Hom L') (p : Γ) :
    φ.equivalence.inv.jointFunctor p = (φ.jointFunctor p).inv := (rfl)

end TauCeti.EquivariantGroupoidLift.Hom
