/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Discrete.Basic

/-!
# The discrete pseudofunctor of a presheaf of types

A presheaf of types `P` on a category `C` defines a `Cat`-valued pseudofunctor on
`LocallyDiscrete Cᵒᵖ` whose fibre over `X` is the discrete category on `P.obj X`, lifted to a
larger universe of objects so that it can be compared with pseudofunctors such as the ones
on schemes, with pullback given by `P.map`. In the language of fibred categories this is the
category fibred in sets, or in setoids, associated with `P`. Its fibres are discrete, hence
groupoids.

The main results compare Mathlib's descent conditions for this pseudofunctor with the sheaf
conditions for `P`. Since all hom-sets in the fibres are subsingletons, descent data for a
presieve `R` are exactly compatible families of elements of `P` along `R`, and morphisms of
descent data are equalities of the restrictions. Hence the pseudofunctor is a prestack exactly
when `P` is separated, and a stack exactly when `P` is a sheaf (Stacks, Lemma 0432). This is how
sheaves of sets, in particular algebraic spaces and representable functors, are viewed as stacks
in setoids.

## Main declarations

* `CategoryTheory.Pseudofunctor.ofPresheaf`: the discrete pseudofunctor of a presheaf of types.
* `CategoryTheory.Pseudofunctor.ofPresheaf.objEquiv`: the objects of the fibre over `X` are the
  elements of `P.obj X`.
* `CategoryTheory.Pseudofunctor.ofPresheafMap`: the strong transformation induced by a morphism
  of presheaves, with `ofPresheafMapId` and `ofPresheafMapComp` comparing it with identities and
  composites.
* `CategoryTheory.Pseudofunctor.ofPresheaf.descentDataEquivCompatible`: descent data for the
  discrete pseudofunctor along a presieve `R` are equivalent to compatible families of `P` along
  `R`.
* `CategoryTheory.Pseudofunctor.isPrestackFor_ofPresheaf_iff`,
  `CategoryTheory.Pseudofunctor.isStackFor_ofPresheaf_iff`: descent along a presieve `R` holds for
  morphisms iff `P` is separated for `R`, and is effective iff `P` is a sheaf for `R`.
* `CategoryTheory.Pseudofunctor.isPrestack_ofPresheaf_iff`,
  `CategoryTheory.Pseudofunctor.isStack_ofPresheaf_iff`: the discrete pseudofunctor is a prestack
  for `J` iff `P` is separated for `J`, and a stack for `J` iff `P` is a sheaf for `J`.

## References

* [Stacks Project, Lemma 0432](https://stacks.math.columbia.edu/tag/0432)
-/

@[expose] public section

universe w' w t v u

namespace CategoryTheory

open Opposite

attribute [local instance] uliftCategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w)

/-- The functor `Cᵒᵖ ⥤ Cat` sending `X` to the discrete category on `P.obj X`, with objects
lifted to the universe `max w w'`. -/
@[simps]
def ofPresheafFunctor : Cᵒᵖ ⥤ Cat.{w, max w w'} where
  obj X := Cat.of (ULift.{w'} (Discrete (P.obj X)))
  map f := (ULift.downFunctor ⋙ Discrete.functor (fun x ↦ Discrete.mk (P.map f x)) ⋙
    ULift.upFunctor).toCatHom
  map_id X := by
    ext
    exact Functor.ext (fun x ↦ by obtain ⟨⟨x⟩⟩ := x; simp [ULift.upFunctor])
      (fun _ _ _ ↦ Subsingleton.elim (α := (_ : ULift.{w'} (Discrete _)) ⟶ _) _ _)
  map_comp f g := by
    ext
    exact Functor.ext (fun x ↦ by obtain ⟨⟨x⟩⟩ := x; simp)
      (fun _ _ _ ↦ Subsingleton.elim (α := (_ : ULift.{w'} (Discrete _)) ⟶ _) _ _)

/-- The discrete pseudofunctor of a presheaf of types `P`: its fibre over `X` is the discrete
category on `P.obj X`, with objects lifted to the universe `max w w'`, and pullback along `f`
is `P.map f`. -/
def ofPresheaf : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, max w w'} :=
  (ofPresheafFunctor.{w'} P).toPseudofunctor'

lemma ofPresheaf_obj (X : LocallyDiscrete Cᵒᵖ) :
    (ofPresheaf.{w'} P).obj X = Cat.of (ULift.{w'} (Discrete (P.obj X.as))) :=
  rfl

@[simp]
lemma ofPresheaf_map_obj {X Y : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (x : (ofPresheaf.{w'} P).obj X) :
    ((ofPresheaf.{w'} P).map f).toFunctor.obj x = ⟨⟨P.map f.as x.down.as⟩⟩ :=
  rfl

/-- The fibres of the discrete pseudofunctor of a presheaf of types are discrete categories,
hence groupoids. -/
instance isDiscrete_ofPresheaf_obj (X : LocallyDiscrete Cᵒᵖ) :
    IsDiscrete ((ofPresheaf.{w'} P).obj X) :=
  isDiscrete_ulift _

/-- Two objects of a fibre of the discrete pseudofunctor of `P` are related by a morphism if
and only if the underlying sections of `P` are equal. -/
lemma nonempty_hom_ofPresheaf_obj_iff {X : LocallyDiscrete Cᵒᵖ} (x y : (ofPresheaf.{w'} P).obj X) :
    Nonempty (x ⟶ y) ↔ x.down.as = y.down.as :=
  ⟨fun ⟨f⟩ ↦ Discrete.eq_of_hom f, fun h ↦ ⟨eqToHom (ULift.ext (Discrete.ext h))⟩⟩

namespace ofPresheaf

variable {P}

/-- The objects of the fibre of the discrete pseudofunctor of `P` over `X` are the elements of
`P.obj X`. -/
def objEquiv (X : Cᵒᵖ) : (ofPresheaf.{w'} P).obj (.mk X) ≃ P.obj X where
  toFun M := M.down.as
  invFun x := ⟨⟨x⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pulling back an object of the discrete pseudofunctor of `P` applies `P.map`. -/
lemma objEquiv_map_toFunctor_obj {X Y : Cᵒᵖ} (f : X ⟶ Y) (M : (ofPresheaf.{w'} P).obj (.mk X)) :
    objEquiv Y (((ofPresheaf.{w'} P).map f.toLoc).toFunctor.obj M) = P.map f (objEquiv X M) :=
  (rfl)

variable {X : Cᵒᵖ}

/-- The morphism between two objects of a fibre of the discrete pseudofunctor with the same
underlying element. -/
def homMk {M N : (ofPresheaf.{w'} P).obj (.mk X)} (h : objEquiv X M = objEquiv X N) : M ⟶ N :=
  eqToHom (ULift.ext (Discrete.ext h))

/-- The isomorphism between two objects of a fibre of the discrete pseudofunctor with the same
underlying element. -/
def isoMk {M N : (ofPresheaf.{w'} P).obj (.mk X)} (h : objEquiv X M = objEquiv X N) : M ≅ N :=
  eqToIso (ULift.ext (Discrete.ext h))

/-- Two objects of a fibre of the discrete pseudofunctor related by a morphism have the same
underlying element. -/
lemma eq_of_hom {M N : (ofPresheaf.{w'} P).obj (.mk X)} (φ : M ⟶ N) :
    objEquiv X M = objEquiv X N :=
  Discrete.eq_of_hom φ

end ofPresheaf

open ofPresheaf

variable {P}

/-- The strong transformation between discrete pseudofunctors induced by a morphism of presheaves
of types: on the fibre over `X` it applies `α.app X`. -/
def ofPresheafMap {Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    StrongTrans (ofPresheaf.{w'} P) (ofPresheaf.{w'} Q) where
  app a := Functor.toCatHom
    { obj M := ⟨⟨α.app a.as M.down.as⟩⟩
      map φ := homMk (X := a.as) (congrArg (α.app a.as) (eq_of_hom (X := a.as) φ))
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }
  -- The two composites send `M` to `α (P.map f M)` and `Q.map f (α M)`, which agree by the
  -- naturality of `α`; all coherence conditions hold because the fibres are discrete.
  naturality f := Cat.Hom.isoMk (NatIso.ofComponents
    (fun M ↦ isoMk (by exact α.naturality_apply f.as M.down.as))
    (fun _ ↦ Subsingleton.elim _ _))
  naturality_naturality _ := by ext; exact Subsingleton.elim _ _
  naturality_id _ := by ext; exact Subsingleton.elim _ _
  naturality_comp _ _ := by ext; exact Subsingleton.elim _ _

/-- The strong transformation induced by `α` applies `α` to the underlying elements. -/
@[simp]
lemma ofPresheaf.objEquiv_ofPresheafMap_app_toFunctor_obj {Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q)
    {X : Cᵒᵖ} (M : (ofPresheaf.{w'} P).obj (.mk X)) :
    objEquiv X (((ofPresheafMap α).app (.mk X)).toFunctor.obj M) = α.app X (objEquiv X M) :=
  (rfl)

open scoped StrongTrans in
/-- The strong transformation induced by the identity of `P` is isomorphic to the identity. -/
def ofPresheafMapId (P : Cᵒᵖ ⥤ Type w) :
    Iso (C := ofPresheaf.{w'} P ⟶ ofPresheaf.{w'} P)
      (ofPresheafMap (𝟙 P)) (StrongTrans.id _) :=
  StrongTrans.isoMk
    (fun _ ↦ Cat.Hom.isoMk (NatIso.ofComponents (fun _ ↦ isoMk rfl)
      (fun _ ↦ Subsingleton.elim _ _)))
    (fun _ ↦ by ext; exact Subsingleton.elim _ _)

open scoped StrongTrans in
/-- The strong transformation induced by a composite of morphisms of presheaves is isomorphic to
the composite of the induced strong transformations. -/
def ofPresheafMapComp {Q R : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) (β : Q ⟶ R) :
    Iso (C := ofPresheaf.{w'} P ⟶ ofPresheaf.{w'} R)
      (ofPresheafMap (α ≫ β)) ((ofPresheafMap α).vcomp (ofPresheafMap β)) :=
  StrongTrans.isoMk
    (fun _ ↦ Cat.Hom.isoMk (NatIso.ofComponents (fun _ ↦ isoMk rfl)
      (fun _ ↦ Subsingleton.elim _ _)))
    (fun _ ↦ by ext; exact Subsingleton.elim _ _)

variable {S : C}

instance {ι : Type t} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (D₁ D₂ : (ofPresheaf.{w'} P).DescentData f) : Subsingleton (D₁ ⟶ D₂) :=
  ⟨fun _ _ ↦ DescentData.hom_ext fun _ ↦ Subsingleton.elim _ _⟩

instance (R : Presieve S) :
    ((ofPresheaf.{w'} P).toDescentData (fun (g : R.category) ↦ g.obj.hom)).Faithful :=
  ⟨fun _ ↦ Subsingleton.elim _ _⟩

/-- Descent data for the discrete pseudofunctor of `P` along a presieve `R` are the same as
compatible families of elements of `P` along `R`: the descent datum is determined by its objects,
and the morphisms of the descent datum exist exactly when the family is compatible. -/
def ofPresheaf.descentDataEquivCompatible (R : Presieve S) :
    (ofPresheaf.{w'} P).DescentData (fun (g : R.category) ↦ g.obj.hom) ≃
      {x : Presieve.FamilyOfElements P R // x.Compatible} where
  toFun D := ⟨fun _ f hf ↦ objEquiv _ (D.obj (R.categoryMk f hf)),
    fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w ↦ eq_of_hom
      (D.hom (g₁ ≫ f₁) (i₁ := R.categoryMk f₁ h₁) (i₂ := R.categoryMk f₂ h₂) g₁ g₂ rfl w.symm)⟩
  invFun x :=
    { obj g := (objEquiv _).symm (x.val g.obj.hom g.property)
      hom _ _ _ _ f₁ f₂ hf₁ hf₂ := homMk (x.property f₁ f₂ _ _ (hf₁.trans hf₂.symm))
      pullHom_hom := by intros; exact Subsingleton.elim _ _
      hom_self := by intros; exact Subsingleton.elim _ _
      hom_comp := by intros; exact Subsingleton.elim _ _ }
  left_inv D := by
    obtain ⟨obj, hom, _, _, _⟩ := D
    dsimp only
    congr 1
    funext _ _ _ _ _ _ _ _
    exact Subsingleton.elim _ _
  right_inv _ := rfl

/-- The compatible family attached to a descent datum consists of its underlying elements. -/
@[simp]
lemma ofPresheaf.descentDataEquivCompatible_apply_coe {R : Presieve S}
    (D : (ofPresheaf.{w'} P).DescentData (fun (g : R.category) ↦ g.obj.hom))
    {Y : C} (f : Y ⟶ S) (hf : R f) :
    (descentDataEquivCompatible R D).val f hf = objEquiv _ (D.obj (R.categoryMk f hf)) :=
  (rfl)

/-- The descent datum attached to a compatible family has the elements of the family as its
objects. -/
@[simp]
lemma ofPresheaf.descentDataEquivCompatible_symm_apply_obj {R : Presieve S}
    (x : {x : Presieve.FamilyOfElements P R // x.Compatible}) (g : R.category) :
    ((descentDataEquivCompatible.{w'} R).symm x).obj g =
      (objEquiv _).symm (x.val g.obj.hom g.property) :=
  (rfl)

private lemma nonempty_hom_toDescentData_obj_iff {R : Presieve S}
    (M N : (ofPresheaf.{w'} P).obj (.mk (op S))) :
    Nonempty (((ofPresheaf P).toDescentData (fun (g : R.category) ↦ g.obj.hom)).obj M ⟶
      ((ofPresheaf P).toDescentData (fun (g : R.category) ↦ g.obj.hom)).obj N) ↔
      ∀ ⦃Y : C⦄ ⦃f : Y ⟶ S⦄, R f → P.map f.op (objEquiv _ M) = P.map f.op (objEquiv _ N) := by
  refine ⟨fun ⟨φ⟩ Y f hf ↦ eq_of_hom (φ.hom (R.categoryMk f hf)), fun h ↦ ⟨?_⟩⟩
  exact { hom g := homMk (h g.property), comm := fun _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _ }

private lemma toDescentData_full_iff (R : Presieve S) :
    ((ofPresheaf.{w'} P).toDescentData (fun (g : R.category) ↦ g.obj.hom)).Full ↔
      Presieve.IsSeparatedFor P R := by
  refine ⟨fun h x t₁ t₂ ht₁ ht₂ ↦ ?_, fun h ↦ ⟨fun {M N} φ ↦ ?_⟩⟩
  · obtain ⟨φ⟩ := (nonempty_hom_toDescentData_obj_iff (R := R)
      ((objEquiv _).symm t₁) ((objEquiv _).symm t₂)).2
      (fun _ f hf ↦ (ht₁ f hf).trans (ht₂ f hf).symm)
    exact eq_of_hom (((ofPresheaf.{w'} P).toDescentData _).preimage φ)
  · exact ⟨homMk (h.ext fun _ _ hf ↦ (nonempty_hom_toDescentData_obj_iff M N).1 ⟨φ⟩ hf),
      Subsingleton.elim _ _⟩

/-- The discrete pseudofunctor of `P` satisfies descent of morphisms along a presieve `R` iff `P`
is separated for `R`. -/
lemma isPrestackFor_ofPresheaf_iff (R : Presieve S) :
    (ofPresheaf.{w'} P).IsPrestackFor R ↔ Presieve.IsSeparatedFor P R := by
  rw [isPrestackFor_iff, ← toDescentData_full_iff]
  exact ⟨fun ⟨h⟩ ↦ h.full, fun _ ↦ ⟨.ofFullyFaithful _⟩⟩

/-- The discrete pseudofunctor of `P` satisfies effective descent along a presieve `R` iff `P`
satisfies the sheaf condition for it. -/
theorem isStackFor_ofPresheaf_iff (R : Presieve S) :
    (ofPresheaf.{w'} P).IsStackFor R ↔ Presieve.IsSheafFor P R := by
  rw [isStackFor_iff, ← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor,
    ← toDescentData_full_iff]
  refine ⟨fun h ↦ ⟨h.full, fun x hx ↦ ?_⟩, fun ⟨hfull, hx⟩ ↦ ⟨inferInstance, hfull, ⟨fun D ↦ ?_⟩⟩⟩
  · obtain ⟨M, ⟨e⟩⟩ :=
      h.essSurj.mem_essImage ((descentDataEquivCompatible.{w'} R).symm ⟨x, hx⟩)
    exact ⟨objEquiv _ M, fun _ f hf ↦ eq_of_hom (e.hom.hom (R.categoryMk f hf))⟩
  · obtain ⟨t, ht⟩ := hx _ (descentDataEquivCompatible R D).property
    exact ⟨(objEquiv _).symm t, ⟨DescentData.isoMk
      (fun g ↦ isoMk (ht g.obj.hom g.property)) (fun _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _)⟩⟩

variable (P)

/-- The discrete pseudofunctor of `P` is a prestack for `J` iff `P` is separated for `J`. -/
lemma isPrestack_ofPresheaf_iff (J : GrothendieckTopology C) :
    (ofPresheaf.{w'} P).IsPrestack J ↔ Presieve.IsSeparated J P :=
  ⟨fun _ _ R hR ↦ (isPrestackFor_ofPresheaf_iff _).1 ((ofPresheaf.{w'} P).isPrestackFor' R hR),
    fun h ↦ .of_isPrestackFor fun _ R hR ↦ (isPrestackFor_ofPresheaf_iff _).2 (h R hR)⟩

/-- The discrete pseudofunctor of a presheaf of types `P` is a stack for `J` if and only if `P`
is a sheaf for `J` (Stacks, Lemma 0432). -/
@[stacks 0432]
theorem isStack_ofPresheaf_iff (J : GrothendieckTopology C) :
    (ofPresheaf.{w'} P).IsStack J ↔ Presieve.IsSheaf J P :=
  ⟨fun _ _ R hR ↦ (isStackFor_ofPresheaf_iff R.arrows).1 ((ofPresheaf.{w'} P).isStackFor' R hR),
    fun hP ↦ IsStack.of_isStackFor fun _ R hR ↦ (isStackFor_ofPresheaf_iff R.arrows).2 (hP R hR)⟩

/-- The discrete pseudofunctor of a sheaf of types is a stack. -/
instance isStack_ofPresheaf (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    (ofPresheaf.{w'} F.obj).IsStack J :=
  (isStack_ofPresheaf_iff _ J).2 ((isSheaf_iff_isSheaf_of_type J F.obj).1 F.property)

end Pseudofunctor

end CategoryTheory
