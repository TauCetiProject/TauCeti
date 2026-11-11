/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# The discrete pseudofunctor of a presheaf of types

A presheaf of types `P` on a category `C` defines a `Cat`-valued pseudofunctor on
`LocallyDiscrete Cᵒᵖ` whose fibre over `X` is the discrete category on `P.obj X`, lifted to a
larger universe of objects so that it can be compared with pseudofunctors such as the ones
on schemes. Its fibres are groupoids, and it is a stack for a Grothendieck topology `J` exactly
when `P` is a sheaf for `J` (Stacks, Lemma 0432).

## Main declarations

* `CategoryTheory.Pseudofunctor.ofPresheaf`: the discrete pseudofunctor of a presheaf of types.
* `CategoryTheory.Pseudofunctor.isStackFor_ofPresheaf`: it satisfies effective descent along
  every sieve for which `P` satisfies the sheaf condition.
* `CategoryTheory.Pseudofunctor.isStack_ofPresheaf_iff`: it is a stack for `J` if and only if
  `P` is a sheaf for `J`.

## References

* [Stacks Project, Lemma 0432](https://stacks.math.columbia.edu/tag/0432)
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Pseudofunctor

open Opposite

attribute [local instance] uliftCategory

private lemma ulift_discrete_hom_ext {α : Type w} {X Y : ULift.{w'} (Discrete α)} (f g : X ⟶ Y) :
    f = g :=
  Subsingleton.elim (α := X.down ⟶ Y.down) f g

private lemma ulift_discrete_eq_of_hom {α : Type w} {X Y : ULift.{w'} (Discrete α)} (f : X ⟶ Y) :
    X.down.as = Y.down.as :=
  Discrete.eq_of_hom f

private lemma ulift_discrete_ext_of_hom {α : Type w} {X Y : ULift.{w'} (Discrete α)} (f : X ⟶ Y) :
    X = Y := by
  obtain ⟨⟨a⟩⟩ := X
  obtain ⟨⟨b⟩⟩ := Y
  cases Discrete.eq_of_hom f
  rfl

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
    exact Functor.ext (fun x ↦ by obtain ⟨⟨x⟩⟩ := x; simp; rfl)
      (fun _ _ _ ↦ ulift_discrete_hom_ext _ _)
  map_comp f g := by
    ext
    exact Functor.ext (fun x ↦ by obtain ⟨⟨x⟩⟩ := x; simp)
      (fun _ _ _ ↦ ulift_discrete_hom_ext _ _)

/-- The discrete pseudofunctor of a presheaf of types `P`: its fibre over `X` is the discrete
category on `P.obj X`, with objects lifted to the universe `max w w'`, and pullback along `f`
is `P.map f`. -/
def ofPresheaf : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, max w w'} :=
  (ofPresheafFunctor.{w'} P).toPseudofunctor'

lemma ofPresheaf_obj (X : Cᵒᵖ) :
    (ofPresheaf.{w'} P).obj ⟨X⟩ = Cat.of (ULift.{w'} (Discrete (P.obj X))) :=
  rfl

lemma ofPresheaf_map_obj {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : P.obj X) :
    ((ofPresheaf.{w'} P).map f.toLoc).toFunctor.obj ⟨⟨x⟩⟩ = ⟨⟨P.map f x⟩⟩ :=
  rfl

/-- The fibres of the discrete pseudofunctor of a presheaf of types are groupoids. -/
instance isGroupoid_ofPresheaf_obj (X : LocallyDiscrete Cᵒᵖ) :
    IsGroupoid ((ofPresheaf.{w'} P).obj X) where
  all_isIso f := ⟨⟨eqToHom (ulift_discrete_ext_of_hom f).symm, ulift_discrete_hom_ext _ _,
    ulift_discrete_hom_ext _ _⟩⟩

variable {P} in
/-- The discrete pseudofunctor of `P` satisfies effective descent along every sieve for which
`P` satisfies the sheaf condition. -/
theorem isStackFor_ofPresheaf {S : C} {R : Sieve S} (hR : Presieve.IsSheafFor P R.arrows) :
    (ofPresheaf.{w'} P).IsStackFor R.arrows := by
  rw [isStackFor_iff]
  exact
    { faithful := ⟨fun _ ↦ ulift_discrete_hom_ext _ _⟩
      full := ⟨fun {M N} φ ↦ ⟨eqToHom (by
        obtain ⟨⟨m⟩⟩ := M
        obtain ⟨⟨n⟩⟩ := N
        have := hR.isSeparatedFor.ext (t₁ := m) (t₂ := n) fun Y f hf ↦
          ulift_discrete_eq_of_hom (φ.hom ⟨Over.mk f, hf⟩)
        rw [this]), DescentData.hom_ext fun _ ↦ ulift_discrete_hom_ext _ _⟩⟩
      essSurj := ⟨fun D ↦ by
        let x : Presieve.FamilyOfElements P R.arrows :=
          fun _ g hg ↦ (D.obj ⟨Over.mk g, hg⟩).down.as
        have hx : x.Compatible := fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w ↦
          ulift_discrete_eq_of_hom (D.hom (g₁ ≫ f₁) (i₁ := ⟨Over.mk f₁, h₁⟩)
            (i₂ := ⟨Over.mk f₂, h₂⟩) g₁ g₂ rfl w.symm)
        refine ⟨⟨⟨hR.amalgamate x hx⟩⟩, ⟨DescentData.isoMk (fun i ↦ eqToIso ?_)
          (fun _ _ _ _ _ _ _ _ ↦ ulift_discrete_hom_ext _ _)⟩⟩
        have := hR.valid_glue hx i.obj.hom i.property
        exact congrArg (fun a ↦ ULift.up (Discrete.mk a)) this⟩ }

/-- The discrete pseudofunctor of a presheaf of types `P` is a stack for `J` if and only if `P`
is a sheaf for `J` (Stacks, Lemma 0432). -/
@[stacks 0432]
theorem isStack_ofPresheaf_iff (J : GrothendieckTopology C) :
    (ofPresheaf.{w'} P).IsStack J ↔ Presieve.IsSheaf J P := by
  refine ⟨fun _ X R hR x hx ↦ ?_,
    fun hP ↦ IsStack.of_isStackFor fun _ R hR ↦ isStackFor_ofPresheaf (hP R hR)⟩
  have := ((ofPresheaf.{w'} P).isStackFor' R hR).isEquivalence
  let G := (ofPresheaf.{w'} P).toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)
  let D : (ofPresheaf.{w'} P).DescentData (fun (f : R.arrows.category) ↦ f.obj.hom) :=
    { obj i := ⟨⟨x i.obj.hom i.property⟩⟩
      hom _ _ i₁ i₂ f₁ f₂ hf₁ hf₂ := eqToHom (congrArg (fun a ↦ ULift.up (Discrete.mk a))
        (hx f₁ f₂ i₁.property i₂.property (hf₁.trans hf₂.symm)))
      pullHom_hom := by intros; exact ulift_discrete_hom_ext _ _
      hom_self := by intros; exact ulift_discrete_hom_ext _ _
      hom_comp := by intros; exact ulift_discrete_hom_ext _ _ }
  let e := G.objObjPreimageIso D
  refine ⟨(G.objPreimage D).down.as,
    fun _ f hf ↦ ulift_discrete_eq_of_hom (e.hom.hom ⟨Over.mk f, hf⟩), fun t ht ↦ ?_⟩
  let φ : G.obj ⟨⟨t⟩⟩ ⟶ G.obj (G.objPreimage D) :=
    { hom i := eqToHom (congrArg (fun a ↦ ULift.up (Discrete.mk a))
        ((ht i.obj.hom i.property).trans (ulift_discrete_eq_of_hom (e.hom.hom i)).symm))
      comm := by intros; exact ulift_discrete_hom_ext _ _ }
  exact ulift_discrete_eq_of_hom (G.preimage φ)

/-- The discrete pseudofunctor of a sheaf of types is a stack. -/
instance isStack_ofPresheaf (J : GrothendieckTopology C) (F : Sheaf J (Type w)) :
    (ofPresheaf.{w'} F.obj).IsStack J :=
  (isStack_ofPresheaf_iff _ J).2 ((isSheaf_iff_isSheaf_of_type J F.obj).1 F.property)

end CategoryTheory.Pseudofunctor
