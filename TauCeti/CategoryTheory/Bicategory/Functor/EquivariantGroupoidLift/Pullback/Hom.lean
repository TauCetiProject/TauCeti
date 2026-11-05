/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Pullback.Basic
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Bicategory
public import TauCeti.CategoryTheory.Bicategory.FunctorBicategory.Precomp

/-!
# Pullback of morphisms of equivariant lifts

Reindexing a family of categories must also reindex its equivariant comparisons and their
modifications. We extend pullback of equivariant lifts to a pseudofunctor between their
bicategories, and hence to a functor on each category of morphisms. The joint strong
transformation is whiskered by the product of the indexing functor with the identity on the
symmetry category. The fiber comparison retains the original
invertible modification, evaluated at the image parameter.

This construction uses the whiskering of strong transformations and modifications in
`Pseudofunctor.precomp`, and the fiber comparison of `EquivariantGroupoidLift.pullback`.
The unit and composition modifications have identity joint components; all five
pseudofunctor coherence laws are inherited from native precomposition. Thus reindexing retains
compatibility with the prescribed symmetry actions, not just the joint functors.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Chapter 4.
* Edward Frenkel, *Langlands Correspondence for Loop Groups*: descent of families of local
  categories along equivalences of parameter groupoids.
-/

public section

universe w v u₃ v₃ u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {Λ : Type u₃} [Category.{v₃} Λ]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions}

namespace Hom

/-- A fiber naturality square remains commutative after replacing its index by an equal
one and inserting the corresponding `eqToIso` corrections. This isolates the equality
transport caused by the indexing functor's `map_id` from the composite pseudofunctors. -/
private lemma fiber_naturality_of_eq {I : Type v₁} {A B C : Cat.{v, w}}
    (x y : I) (hxy : x = y)
    (F : I → (A ⟶ A)) (G : I → (B ⟶ B)) (T : C ⟶ C)
    (s : A ⟶ B) (e : A ⟶ C) (e' : B ⟶ C)
    (m : s ≫ e' ⟶ e) (n : ∀ i, F i ≫ s ≅ s ≫ G i)
    (c : F y ≫ e ⟶ e ≫ T) (c' : G y ≫ e' ⟶ e' ≫ T)
    (hm : F y ◁ m ≫ c =
      ((α_ _ _ _).inv ≫ (n y).hom ▷ e' ≫ (α_ _ _ _).hom ≫
        s ◁ c' ≫ (α_ _ _ _).inv) ≫ m ▷ T)
    (eF : F x ≫ 𝟙 A = 𝟙 A ≫ F y) (eG : G x ≫ 𝟙 B = 𝟙 B ≫ G y) :
    F x ◁ m ≫ ((α_ (F x) (𝟙 A) e).inv ≫ (eqToIso eF).hom ▷ e ≫
      (α_ (𝟙 A) (F y) e).hom ≫ 𝟙 A ◁ c ≫ (α_ (𝟙 A) e T).inv) =
    ((α_ (F x) s (𝟙 B ≫ e')).inv ≫ (n x).hom ▷ (𝟙 B ≫ e') ≫
      (α_ s (G x) (𝟙 B ≫ e')).hom ≫ s ◁
        ((α_ (G x) (𝟙 B) e').inv ≫ (eqToIso eG).hom ▷ e' ≫
          (α_ (𝟙 B) (G y) e').hom ≫ 𝟙 B ◁ c' ≫ (α_ (𝟙 B) e' T).inv) ≫
      (α_ s (𝟙 B ≫ e') T).inv) ≫ m ▷ T := by
  subst hxy
  ext X
  simpa using congrArg (fun t ↦ t.toNatTrans.app X) hm

/-- Pull back a morphism of equivariant lifts, retaining its prescribed-fiber comparison. -/
-- Exposed so that the joint transformation and the endpoints of its fiber modification
-- reduce to the native whiskering when stating component formulas.
@[expose] noncomputable def pullback (φ : L.Hom L') (ψ : Λ ⥤ Γ) :
    (L.pullback ψ).Hom (L'.pullback ψ) where
  joint := (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.whiskerLeft φ.joint
  fiberIso l := Pseudofunctor.StrongTrans.isoMk
    (fun a ↦ isoApp (φ.fiberIso (ψ.obj l)) a)
    (fun {a b} f ↦ by
      obtain ⟨⟨⟩⟩ := a
      obtain ⟨⟨⟩⟩ := b
      obtain ⟨f⟩ := f
      simp only [isoApp_hom]
      exact fiber_naturality_of_eq
        (x := ψ.map (𝟙 l)) (y := 𝟙 (ψ.obj l)) (hxy := ψ.map_id l)
        (F := fun x ↦ L.joint.map (x ×ₘ f).toLoc)
        (G := fun x ↦ L'.joint.map (x ×ₘ f).toLoc)
        (T := (actions (ψ.obj l)).map f.toLoc)
        (s := φ.joint.app ⟨(ψ.obj l, SingleObj.star H)⟩)
        (e := (L.comparison (ψ.obj l)).app ⟨SingleObj.star H⟩)
        (e' := (L'.comparison (ψ.obj l)).app ⟨SingleObj.star H⟩)
        (m := (φ.fiberIso (ψ.obj l)).hom.as.app ⟨SingleObj.star H⟩)
        (n := fun x ↦ φ.joint.naturality (x ×ₘ f).toLoc)
        (c := ((L.comparison (ψ.obj l)).naturality f.toLoc).hom)
        (c' := ((L'.comparison (ψ.obj l)).naturality f.toLoc).hom)
        (hm := (φ.fiberIso (ψ.obj l)).hom.as.naturality f.toLoc) (eF := _) (eG := _))

@[simp]
lemma pullback_joint (φ : L.Hom L') (ψ : Λ ⥤ Γ) :
    (φ.pullback ψ).joint = (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.whiskerLeft φ.joint :=
  (rfl)

@[simp]
lemma pullback_fiberIso_hom_as_app (φ : L.Hom L') (ψ : Λ ⥤ Γ) (l : Λ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((φ.pullback ψ).fiberIso l).hom.as.app a = (φ.fiberIso (ψ.obj l)).hom.as.app a :=
  isoApp_hom _ _

@[simp]
lemma pullback_fiberIso_inv_as_app (φ : L.Hom L') (ψ : Λ ⥤ Γ) (l : Λ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((φ.pullback ψ).fiberIso l).inv.as.app a = (φ.fiberIso (ψ.obj l)).inv.as.app a :=
  isoApp_inv _ _

/-- Pull back a compatible modification by restricting its joint components. -/
noncomputable def Hom₂.pullback {φ θ : L.Hom L'} (Θ : φ ⟶ θ) (ψ : Λ ⥤ Γ) :
    φ.pullback ψ ⟶ θ.pullback ψ where
  joint := (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂ Θ.joint
  comm l a := by
    simp only [pullback_fiberIso_hom_as_app]
    exact Θ.comm (ψ.obj l) a

@[simp]
lemma Hom₂.pullback_joint {φ θ : L.Hom L'} (Θ : φ ⟶ θ) (ψ : Λ ⥤ Γ) :
    (Θ.pullback ψ).joint =
      (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂ Θ.joint :=
  (rfl)

@[simp]
lemma Hom₂.pullback_id (φ : L.Hom L') (ψ : Λ ⥤ Γ) :
    (Hom₂.pullback (𝟙 φ) ψ) = 𝟙 (φ.pullback ψ) := by
  apply hom₂_ext
  exact (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂_id _

@[simp]
lemma Hom₂.pullback_comp {φ θ ι : L.Hom L'} (Θ : φ ⟶ θ) (Ξ : θ ⟶ ι) (ψ : Λ ⥤ Γ) :
    (Hom₂.pullback (Θ ≫ Ξ) ψ) = Θ.pullback ψ ≫ Ξ.pullback ψ := by
  apply hom₂_ext
  exact (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂_comp _ _

/-- Pullback preserves the identity lift morphism up to the native whiskering comparison. -/
noncomputable def pullbackIdIso (L : EquivariantGroupoidLift Γ actions) (ψ : Λ ⥤ Γ) :
    (id L).pullback ψ ≅ id (L.pullback ψ) :=
  isoMk ((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.whiskerLeftId L.joint)
    (fun l a ↦ by
      simp only [Pseudofunctor.whiskerLeftId_hom_as_app, id_fiberIso_hom_as_app,
        pullback_fiberIso_hom_as_app]
      exact (congrArg (· ≫ _) (id_whiskerRight _ _)).trans (Category.id_comp _))

variable {L'' : EquivariantGroupoidLift Γ actions}

/-- Pullback preserves composition of lift morphisms up to the native whiskering comparison. -/
noncomputable def pullbackCompIso (φ : L.Hom L') (θ : L'.Hom L'') (ψ : Λ ⥤ Γ) :
    (φ.comp θ).pullback ψ ≅ (φ.pullback ψ).comp (θ.pullback ψ) :=
  isoMk ((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.whiskerLeftComp φ.joint θ.joint)
    (fun l a ↦ by
      simp only [Pseudofunctor.whiskerLeftComp_hom_as_app, comp_fiberIso_hom_as_app,
        pullback_fiberIso_hom_as_app]
      exact (congrArg (· ≫ _) (id_whiskerRight _ _)).trans (Category.id_comp _))

@[simp]
lemma pullbackIdIso_hom_joint (L : EquivariantGroupoidLift Γ actions) (ψ : Λ ⥤ Γ) :
    (pullbackIdIso L ψ).hom.joint =
      ((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.whiskerLeftId L.joint).hom := by
  rw [pullbackIdIso]
  exact isoMk_hom_joint _ _

@[simp]
lemma pullbackIdIso_inv_joint (L : EquivariantGroupoidLift Γ actions) (ψ : Λ ⥤ Γ) :
    (pullbackIdIso L ψ).inv.joint =
      ((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.whiskerLeftId L.joint).inv := by
  rw [pullbackIdIso]
  exact isoMk_inv_joint _ _

@[simp]
lemma pullbackCompIso_hom_joint (φ : L.Hom L') (θ : L'.Hom L'') (ψ : Λ ⥤ Γ) :
    (pullbackCompIso φ θ ψ).hom.joint =
      ((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.whiskerLeftComp φ.joint θ.joint).hom := by
  rw [pullbackCompIso]
  exact isoMk_hom_joint _ _

@[simp]
lemma pullbackCompIso_inv_joint (φ : L.Hom L') (θ : L'.Hom L'') (ψ : Λ ⥤ Γ) :
    (pullbackCompIso φ θ ψ).inv.joint =
      ((ψ.prod (𝟭 (SingleObj H))).toPseudofunctor.whiskerLeftComp φ.joint θ.joint).inv := by
  rw [pullbackCompIso]
  exact isoMk_inv_joint _ _

end Hom

/-- Reindexing as a pseudofunctor on the bicategories of equivariant lifts. Its structure
modifications are the native identity-component comparisons for whiskering. -/
-- Exposed so the transported fibers and the endpoints of the structure modifications reduce
-- to those of `pullback`, `Hom.pullback`, and `Hom.Hom₂.pullback` in component formulas.
@[expose, simps obj map map₂ mapId mapComp] noncomputable def pullbackPseudofunctor
    (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) (ψ : Λ ⥤ Γ) :
    EquivariantGroupoidLift Γ actions ⥤ᵖ
      EquivariantGroupoidLift Λ (fun l ↦ actions (ψ.obj l)) where
  obj L := L.pullback ψ
  map φ := φ.pullback ψ
  map₂ Θ := Θ.pullback ψ
  map₂_id φ := Hom.Hom₂.pullback_id φ ψ
  map₂_comp Θ Ξ := Hom.Hom₂.pullback_comp Θ Ξ ψ
  mapId L := Hom.pullbackIdIso L ψ
  mapComp φ θ := Hom.pullbackCompIso φ θ ψ
  map₂_whisker_left φ θ θ' Θ := by
    apply Hom.hom₂_ext
    simp only [Hom.Hom₂.pullback_joint, whiskerLeft_joint, hom₂_comp_joint,
      Hom.pullbackCompIso_hom_joint, Hom.pullbackCompIso_inv_joint]
    exact (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂_whisker_left
      φ.joint Θ.joint
  map₂_whisker_right Θ θ := by
    apply Hom.hom₂_ext
    simp only [Hom.Hom₂.pullback_joint, whiskerRight_joint, hom₂_comp_joint,
      Hom.pullbackCompIso_hom_joint, Hom.pullbackCompIso_inv_joint]
    exact (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂_whisker_right
      Θ.joint θ.joint
  map₂_associator φ θ ι := by
    apply Hom.hom₂_ext
    simp only [Hom.Hom₂.pullback_joint, associator_hom_joint, hom₂_comp_joint,
      Hom.pullbackCompIso_hom_joint, Hom.pullbackCompIso_inv_joint,
      whiskerLeft_joint, whiskerRight_joint]
    exact (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂_associator
      φ.joint θ.joint ι.joint
  map₂_left_unitor φ := by
    apply Hom.hom₂_ext
    simp only [Hom.Hom₂.pullback_joint, leftUnitor_hom_joint, hom₂_comp_joint,
      Hom.pullbackCompIso_hom_joint, Hom.pullbackIdIso_hom_joint, whiskerRight_joint]
    exact (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂_left_unitor
      φ.joint
  map₂_right_unitor φ := by
    apply Hom.hom₂_ext
    simp only [Hom.Hom₂.pullback_joint, rightUnitor_hom_joint, hom₂_comp_joint,
      Hom.pullbackCompIso_hom_joint, Hom.pullbackIdIso_hom_joint, whiskerLeft_joint]
    exact (Pseudofunctor.precomp Cat (ψ.prod (𝟭 (SingleObj H))).toPseudofunctor).map₂_right_unitor
      φ.joint

end TauCeti.EquivariantGroupoidLift
