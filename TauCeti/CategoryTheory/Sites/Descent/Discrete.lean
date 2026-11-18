/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# The discrete pseudofunctor of a presheaf of types

A presheaf of types `P : Cᵒᵖ ⥤ Type w` defines a pseudofunctor
`P.discretePseudofunctor : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` whose fibre over `X` is the discrete
category on `P(X)` (its objects are lifted to an arbitrary larger universe, so that the
pseudofunctor can land in `Cat.{w, w'}` for any `w'` above `w`), with pullback given by `P.map`.
In the language of fibred categories this is the category fibred in sets, or in setoids,
associated with `P`. Its fibres are groupoids with at most one morphism between two objects.

The main results compare Mathlib's descent conditions for this pseudofunctor with the sheaf
conditions for `P`. Since all hom-sets in the fibres are subsingletons, descent data for a
presieve `R` are exactly compatible families of elements of `P` along `R`, and morphisms of
descent data are equalities of the restrictions. Hence the pseudofunctor is a prestack exactly
when `P` is separated, and a stack exactly when `P` is a sheaf. This is how sheaves of sets, in
particular algebraic spaces and representable functors, are viewed as stacks in setoids.

## Main declarations

* `CategoryTheory.Functor.discretePseudofunctor`: the discrete pseudofunctor of `P`.
* `CategoryTheory.Functor.discretePseudofunctorMap`: the strong transformation induced by a
  morphism of presheaves, with `discretePseudofunctorMapId` and `discretePseudofunctorMapComp`
  comparing it with identities and composites.
* `CategoryTheory.Functor.descentDataEquivCompatible`: descent data for the discrete
  pseudofunctor along a presieve `R` are equivalent to compatible families of `P` along `R`.
* `CategoryTheory.Functor.isPrestackFor_discretePseudofunctor_iff`,
  `CategoryTheory.Functor.isStackFor_discretePseudofunctor_iff`: descent along a presieve `R`
  holds for morphisms iff `P` is separated for `R`, and is effective iff `P` is a sheaf for `R`.
* `CategoryTheory.Functor.isPrestack_discretePseudofunctor_iff`,
  `CategoryTheory.Functor.isStack_discretePseudofunctor_iff`: the discrete pseudofunctor is a
  prestack for `J` iff `P` is separated for `J`, and a stack for `J` iff `P` is a sheaf for `J`.

## References

* [Stacks Project, Section 8.6 (Stacks in setoids) and Lemma 8.6.3](https://stacks.math.columbia.edu/tag/0432)
-/

@[expose] public section

universe w' w t v u

namespace CategoryTheory

open Opposite Bicategory

namespace Functor

variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w)

/-- The discrete pseudofunctor of a presheaf of types `P`: its fibre over `X` is the discrete
category on `P(X)`, with objects lifted to the universe `max w w'`, and pullback along `f` is
`P.map f`. -/
def discretePseudofunctor : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, max w w'} :=
  Functor.toPseudofunctor' (P ⋙
    { obj X := Cat.of (InducedCategory (Discrete X) (fun x : ULift.{w'} X ↦ Discrete.mk x.down))
      map f := Functor.toCatHom
        { obj x := ⟨f x.down⟩
          map g := InducedCategory.homMk
            (Discrete.eqToHom (congrArg f (Discrete.eq_of_hom g.hom)))
          map_id _ := InducedCategory.hom_ext (Subsingleton.elim _ _)
          map_comp _ _ := InducedCategory.hom_ext (Subsingleton.elim _ _) }
      map_id X := by
        ext
        exact Functor.ext (fun _ ↦ rfl)
          (fun _ _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _))
      map_comp f g := by
        ext
        exact Functor.ext (fun _ ↦ rfl)
          (fun _ _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _)) })

/-- Pulling back an object of the discrete pseudofunctor of `P` applies `P.map`. -/
@[simp]
lemma discretePseudofunctor_map_toFunctor_obj_down {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (M : P.discretePseudofunctor.{w'}.obj a) :
    ((P.discretePseudofunctor.{w'}.map f).toFunctor.obj M).down = P.map f.as M.down :=
  rfl

namespace discretePseudofunctor

variable {P} {a : LocallyDiscrete Cᵒᵖ}

instance (M N : P.discretePseudofunctor.{w'}.obj a) : Subsingleton (M ⟶ N) :=
  ⟨fun _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _)⟩

/-- The morphism between two objects of a fibre of the discrete pseudofunctor with the same
underlying element. -/
def homMk {M N : P.discretePseudofunctor.{w'}.obj a} (h : M.down = N.down) : M ⟶ N :=
  InducedCategory.homMk (Discrete.eqToHom h)

/-- The isomorphism between two objects of a fibre of the discrete pseudofunctor with the same
underlying element. -/
def isoMk {M N : P.discretePseudofunctor.{w'}.obj a} (h : M.down = N.down) : M ≅ N where
  hom := homMk h
  inv := homMk h.symm
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

/-- Two objects of a fibre of the discrete pseudofunctor related by a morphism have the same
underlying element. -/
lemma eq_of_hom {M N : P.discretePseudofunctor.{w'}.obj a} (φ : M ⟶ N) : M.down = N.down :=
  Discrete.eq_of_hom φ.hom

/-- Two objects of a fibre of the discrete pseudofunctor are related by a morphism iff they have
the same underlying element. -/
lemma nonempty_hom_iff (M N : P.discretePseudofunctor.{w'}.obj a) :
    Nonempty (M ⟶ N) ↔ M.down = N.down :=
  ⟨fun ⟨φ⟩ ↦ eq_of_hom φ, fun h ↦ ⟨homMk h⟩⟩

instance : IsGroupoid (P.discretePseudofunctor.{w'}.obj a) where
  all_isIso φ := ⟨homMk (eq_of_hom φ).symm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end discretePseudofunctor

open discretePseudofunctor

variable {P}

/-- The strong transformation between discrete pseudofunctors induced by a morphism of presheaves
of types: on the fibre over `X` it applies `α.app X`. -/
def discretePseudofunctorMap {Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    Pseudofunctor.StrongTrans P.discretePseudofunctor.{w'} Q.discretePseudofunctor.{w'} where
  app a := Functor.toCatHom
    { obj M := ⟨α.app a.as M.down⟩
      map φ := homMk (congrArg (α.app a.as) (eq_of_hom φ))
      map_id _ := InducedCategory.hom_ext (Subsingleton.elim _ _)
      map_comp _ _ := InducedCategory.hom_ext (Subsingleton.elim _ _) }
  -- The two composites send `M` to `α (P.map f M)` and `Q.map f (α M)`, which agree by the
  -- naturality of `α`; all coherence conditions hold because the fibres are thin.
  naturality f := Cat.Hom.isoMk (NatIso.ofComponents
    (fun M ↦ isoMk (by exact α.naturality_apply f.as M.down))
    (fun _ ↦ Subsingleton.elim _ _))
  naturality_naturality _ := by ext; exact Subsingleton.elim _ _
  naturality_id _ := by ext; exact Subsingleton.elim _ _
  naturality_comp _ _ := by ext; exact Subsingleton.elim _ _

/-- The strong transformation induced by `α` applies `α` to the underlying elements. -/
@[simp]
lemma discretePseudofunctorMap_app_toFunctor_obj_down {Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q)
    {a : LocallyDiscrete Cᵒᵖ} (M : P.discretePseudofunctor.{w'}.obj a) :
    (((discretePseudofunctorMap α).app a).toFunctor.obj M).down = α.app a.as M.down :=
  rfl

open scoped Pseudofunctor.StrongTrans in
/-- The strong transformation induced by the identity of `P` is isomorphic to the identity. -/
def discretePseudofunctorMapId (P : Cᵒᵖ ⥤ Type w) :
    Iso (C := P.discretePseudofunctor.{w'} ⟶ P.discretePseudofunctor.{w'})
      (discretePseudofunctorMap (𝟙 P)) (Pseudofunctor.StrongTrans.id _) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun _ ↦ Cat.Hom.isoMk (NatIso.ofComponents (fun _ ↦ isoMk rfl)
      (fun _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _))))
    (fun _ ↦ by ext; exact Subsingleton.elim _ _)

open scoped Pseudofunctor.StrongTrans in
/-- The strong transformation induced by a composite of morphisms of presheaves is isomorphic to
the composite of the induced strong transformations. -/
def discretePseudofunctorMapComp {Q R : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) (β : Q ⟶ R) :
    Iso (C := P.discretePseudofunctor.{w'} ⟶ R.discretePseudofunctor.{w'})
      (discretePseudofunctorMap (α ≫ β))
      ((discretePseudofunctorMap α).vcomp (discretePseudofunctorMap β)) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun _ ↦ Cat.Hom.isoMk (NatIso.ofComponents (fun _ ↦ isoMk rfl)
      (fun _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _))))
    (fun _ ↦ by ext; exact Subsingleton.elim _ _)

variable {S : C}

instance {ι : Type t} {X : ι → C} (f : ∀ i, X i ⟶ S)
    (D₁ D₂ : P.discretePseudofunctor.{w'}.DescentData f) : Subsingleton (D₁ ⟶ D₂) :=
  ⟨fun _ _ ↦ Pseudofunctor.DescentData.hom_ext fun _ ↦ Subsingleton.elim _ _⟩

instance (R : Presieve S) :
    (P.discretePseudofunctor.{w'}.toDescentData (fun (g : R.category) ↦ g.obj.hom)).Faithful :=
  ⟨fun _ ↦ Subsingleton.elim _ _⟩

/-- Descent data for the discrete pseudofunctor of `P` along a presieve `R` are the same as
compatible families of elements of `P` along `R`: the descent datum is determined by its objects,
and the morphisms of the descent datum exist exactly when the family is compatible. -/
def descentDataEquivCompatible (R : Presieve S) :
    P.discretePseudofunctor.{w'}.DescentData (fun (g : R.category) ↦ g.obj.hom) ≃
      {x : Presieve.FamilyOfElements P R // x.Compatible} where
  toFun D := ⟨fun _ f hf ↦ (D.obj (R.categoryMk f hf)).down,
    fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w ↦ eq_of_hom
      (D.hom (g₁ ≫ f₁) (i₁ := R.categoryMk f₁ h₁) (i₂ := R.categoryMk f₂ h₂) g₁ g₂ rfl w.symm)⟩
  invFun x :=
    { obj g := ⟨x.1 g.obj.hom g.property⟩
      hom _ _ _ _ f₁ f₂ hf₁ hf₂ := homMk (x.2 f₁ f₂ _ _ (hf₁.trans hf₂.symm))
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
lemma descentDataEquivCompatible_apply_coe {R : Presieve S}
    (D : P.discretePseudofunctor.{w'}.DescentData (fun (g : R.category) ↦ g.obj.hom))
    {Y : C} (f : Y ⟶ S) (hf : R f) :
    (descentDataEquivCompatible R D).1 f hf = (D.obj (R.categoryMk f hf)).down :=
  rfl

/-- The descent datum attached to a compatible family has the elements of the family as its
objects. -/
@[simp]
lemma descentDataEquivCompatible_symm_apply_obj_down {R : Presieve S}
    (x : {x : Presieve.FamilyOfElements P R // x.Compatible}) (g : R.category) :
    (((descentDataEquivCompatible.{w'} R).symm x).obj g).down = x.1 g.obj.hom g.property :=
  rfl

private lemma nonempty_hom_toDescentData_obj_iff {R : Presieve S}
    (M N : P.discretePseudofunctor.{w'}.obj (.mk (op S))) :
    Nonempty ((P.discretePseudofunctor.toDescentData (fun (g : R.category) ↦ g.obj.hom)).obj M ⟶
      (P.discretePseudofunctor.toDescentData (fun (g : R.category) ↦ g.obj.hom)).obj N) ↔
      ∀ ⦃Y : C⦄ ⦃f : Y ⟶ S⦄, R f → P.map f.op M.down = P.map f.op N.down := by
  refine ⟨fun ⟨φ⟩ Y f hf ↦ eq_of_hom (φ.hom (R.categoryMk f hf)), fun h ↦ ⟨?_⟩⟩
  exact { hom g := homMk (h g.property), comm := fun _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _ }

private lemma toDescentData_full_iff (R : Presieve S) :
    (P.discretePseudofunctor.{w'}.toDescentData (fun (g : R.category) ↦ g.obj.hom)).Full ↔
      Presieve.IsSeparatedFor P R := by
  refine ⟨fun h x t₁ t₂ ht₁ ht₂ ↦ ?_, fun h ↦ ⟨fun {M N} φ ↦ ?_⟩⟩
  · obtain ⟨φ⟩ := (nonempty_hom_toDescentData_obj_iff (R := R) (ULift.up t₁)
      (ULift.up t₂)).2 (fun _ f hf ↦ (ht₁ f hf).trans (ht₂ f hf).symm)
    exact eq_of_hom ((P.discretePseudofunctor.{w'}.toDescentData _).preimage φ)
  · exact ⟨homMk (h.ext fun _ _ hf ↦ (nonempty_hom_toDescentData_obj_iff M N).1 ⟨φ⟩ hf),
      Subsingleton.elim _ _⟩

/-- The discrete pseudofunctor of `P` satisfies descent of morphisms along a presieve `R` iff `P`
is separated for `R`. -/
lemma isPrestackFor_discretePseudofunctor_iff (R : Presieve S) :
    P.discretePseudofunctor.{w'}.IsPrestackFor R ↔ Presieve.IsSeparatedFor P R := by
  rw [Pseudofunctor.isPrestackFor_iff, ← toDescentData_full_iff]
  exact ⟨fun ⟨h⟩ ↦ h.full, fun _ ↦ ⟨.ofFullyFaithful _⟩⟩

/-- The discrete pseudofunctor of `P` satisfies effective descent along a presieve `R` iff `P` is a
sheaf for `R`. -/
lemma isStackFor_discretePseudofunctor_iff (R : Presieve S) :
    P.discretePseudofunctor.{w'}.IsStackFor R ↔ Presieve.IsSheafFor P R := by
  rw [Pseudofunctor.isStackFor_iff,
    ← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor, ← toDescentData_full_iff]
  refine ⟨fun h ↦ ⟨h.full, fun x hx ↦ ?_⟩, fun ⟨hfull, hx⟩ ↦ ⟨inferInstance, hfull, ⟨fun D ↦ ?_⟩⟩⟩
  · obtain ⟨M, ⟨e⟩⟩ :=
      h.essSurj.mem_essImage ((descentDataEquivCompatible.{w'} R).symm ⟨x, hx⟩)
    exact ⟨M.down, fun _ f hf ↦ eq_of_hom (e.hom.hom (R.categoryMk f hf))⟩
  · obtain ⟨t, ht⟩ := hx _ (descentDataEquivCompatible R D).2
    exact ⟨ULift.up t, ⟨Pseudofunctor.DescentData.isoMk (fun g ↦ isoMk (ht g.obj.hom g.property))
      (fun _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _)⟩⟩

/-- The discrete pseudofunctor of `P` is a prestack for `J` iff `P` is separated for `J`. -/
lemma isPrestack_discretePseudofunctor_iff (J : GrothendieckTopology C) :
    P.discretePseudofunctor.{w'}.IsPrestack J ↔ Presieve.IsSeparated J P :=
  ⟨fun _ _ R hR ↦ (isPrestackFor_discretePseudofunctor_iff _).1
      (Pseudofunctor.isPrestackFor' _ R hR),
    fun h ↦ .of_isPrestackFor fun _ R hR ↦ (isPrestackFor_discretePseudofunctor_iff _).2 (h R hR)⟩

/-- The discrete pseudofunctor of `P` is a stack for `J` iff `P` is a sheaf for `J`: a presheaf of
sets defines a stack in setoids exactly when it is a sheaf. -/
@[stacks 0432]
lemma isStack_discretePseudofunctor_iff (J : GrothendieckTopology C) :
    P.discretePseudofunctor.{w'}.IsStack J ↔ Presieve.IsSheaf J P :=
  ⟨fun _ _ R hR ↦ (isStackFor_discretePseudofunctor_iff _).1 (Pseudofunctor.isStackFor' _ R hR),
    fun h ↦ .of_isStackFor fun _ R hR ↦ (isStackFor_discretePseudofunctor_iff _).2 (h R hR)⟩

end Functor

end CategoryTheory
