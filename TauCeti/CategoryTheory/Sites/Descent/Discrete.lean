/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# The discrete pseudofunctor of a presheaf of types

A presheaf of types `P` on a category `C` defines a `Cat`-valued pseudofunctor on
`LocallyDiscrete Cᵒᵖ` whose fibre over `X` is the discrete category on `P.obj X`, lifted to a
larger universe of objects so that it can be compared with pseudofunctors such as the ones
on schemes. Its fibres are discrete, hence groupoids, and it is a stack for a Grothendieck
topology `J` exactly when `P` is a sheaf for `J` (Stacks, Lemma 0432).

## Main declarations

* `CategoryTheory.Pseudofunctor.ofPresheaf`: the discrete pseudofunctor of a presheaf of types.
* `CategoryTheory.Pseudofunctor.isStackFor_ofPresheaf_iff`: it satisfies effective descent along
  a presieve if and only if `P` satisfies the sheaf condition for that presieve.
* `CategoryTheory.Pseudofunctor.isStack_ofPresheaf_iff`: it is a stack for `J` if and only if
  `P` is a sheaf for `J`.

## References

* [Stacks Project, Lemma 0432](https://stacks.math.columbia.edu/tag/0432)
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

open Opposite

attribute [local instance] uliftCategory

/-- The discrete category on a type, with objects lifted to a larger universe, is discrete. -/
instance isDiscrete_ulift_discrete (α : Type w) : IsDiscrete (ULift.{w'} (Discrete α)) where
  subsingleton X Y := inferInstanceAs (Subsingleton (X.down ⟶ Y.down))
  eq_of_hom {X Y} f := by
    obtain ⟨⟨a⟩⟩ := X
    obtain ⟨⟨b⟩⟩ := Y
    cases Discrete.eq_of_hom f
    rfl

namespace Pseudofunctor

/-- The isomorphism between the objects of `ULift (Discrete α)` given by an equality in `α`. -/
private abbrev uliftDiscreteIsoOfEq {α : Type w} {a b : α} (h : a = b) :
    (⟨⟨a⟩⟩ : ULift.{w'} (Discrete α)) ≅ ⟨⟨b⟩⟩ :=
  eqToIso (congrArg (fun a ↦ ULift.up (Discrete.mk a)) h)

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

@[simp]
lemma ofPresheaf_obj (X : Cᵒᵖ) :
    (ofPresheaf.{w'} P).obj ⟨X⟩ = Cat.of (ULift.{w'} (Discrete (P.obj X))) :=
  rfl

@[simp]
lemma ofPresheaf_map_obj {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : P.obj X) :
    ((ofPresheaf.{w'} P).map f.toLoc).toFunctor.obj ⟨⟨x⟩⟩ = ⟨⟨P.map f x⟩⟩ :=
  rfl

/-- The fibres of the discrete pseudofunctor of a presheaf of types are discrete categories,
hence groupoids. -/
instance isDiscrete_ofPresheaf_obj (X : LocallyDiscrete Cᵒᵖ) :
    IsDiscrete ((ofPresheaf.{w'} P).obj X) :=
  isDiscrete_ulift_discrete _

/-- Two objects of a fibre of the discrete pseudofunctor of `P` are related by a morphism if
and only if the underlying sections of `P` are equal. -/
lemma nonempty_hom_ofPresheaf_obj_iff {X : Cᵒᵖ} (x y : P.obj X) :
    Nonempty ((⟨⟨x⟩⟩ : (ofPresheaf.{w'} P).obj ⟨X⟩) ⟶ ⟨⟨y⟩⟩) ↔ x = y :=
  ⟨fun ⟨f⟩ ↦ Discrete.eq_of_hom f, fun h ↦ ⟨(uliftDiscreteIsoOfEq.{w'} h).hom⟩⟩

variable {P} in
/-- The discrete pseudofunctor of `P` satisfies effective descent along a presieve if and only
if `P` satisfies the sheaf condition for it. -/
theorem isStackFor_ofPresheaf_iff {S : C} (R : Presieve S) :
    (ofPresheaf.{w'} P).IsStackFor R ↔ Presieve.IsSheafFor P R := by
  refine ⟨fun h x hx ↦ ?_, fun hR ↦ ?_⟩
  · have := h.isEquivalence
    let G := (ofPresheaf.{w'} P).toDescentData (fun (f : R.category) ↦ f.obj.hom)
    let D : (ofPresheaf.{w'} P).DescentData (fun (f : R.category) ↦ f.obj.hom) :=
      { obj i := ⟨⟨x i.obj.hom i.property⟩⟩
        hom _ _ i₁ i₂ f₁ f₂ hf₁ hf₂ := (uliftDiscreteIsoOfEq.{w'}
          (hx f₁ f₂ i₁.property i₂.property (hf₁.trans hf₂.symm))).hom
        pullHom_hom := by intros; exact Subsingleton.elim _ _
        hom_self := by intros; exact Subsingleton.elim _ _
        hom_comp := by intros; exact Subsingleton.elim _ _ }
    let e := G.objObjPreimageIso D
    refine ⟨(G.objPreimage D).down.as,
      fun _ f hf ↦ Discrete.eq_of_hom (e.hom.hom ⟨Over.mk f, hf⟩), fun t ht ↦ ?_⟩
    let φ : G.obj ⟨⟨t⟩⟩ ⟶ G.obj (G.objPreimage D) :=
      { hom i := (uliftDiscreteIsoOfEq.{w'}
          ((ht i.obj.hom i.property).trans (Discrete.eq_of_hom (e.hom.hom i)).symm)).hom
        comm := by intros; exact Subsingleton.elim _ _ }
    exact Discrete.eq_of_hom (G.preimage φ)
  · rw [isStackFor_iff]
    exact
      { faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩
        full := ⟨fun {M N} φ ↦ ⟨by
          obtain ⟨⟨m⟩⟩ := M
          obtain ⟨⟨n⟩⟩ := N
          exact (uliftDiscreteIsoOfEq.{w'} (hR.isSeparatedFor.ext fun Y f hf ↦
            Discrete.eq_of_hom (φ.hom ⟨Over.mk f, hf⟩))).hom,
          DescentData.hom_ext fun _ ↦ Subsingleton.elim _ _⟩⟩
        essSurj := ⟨fun D ↦ by
          let x : Presieve.FamilyOfElements P R :=
            fun _ g hg ↦ (D.obj ⟨Over.mk g, hg⟩).down.as
          have hx : x.Compatible := fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w ↦
            Discrete.eq_of_hom (D.hom (g₁ ≫ f₁) (i₁ := ⟨Over.mk f₁, h₁⟩)
              (i₂ := ⟨Over.mk f₂, h₂⟩) g₁ g₂ rfl w.symm)
          exact ⟨⟨⟨hR.amalgamate x hx⟩⟩, ⟨DescentData.isoMk
            (fun i ↦ uliftDiscreteIsoOfEq.{w'} (hR.valid_glue hx i.obj.hom i.property))
            (fun _ _ _ _ _ _ _ _ ↦ Subsingleton.elim _ _)⟩⟩⟩ }

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
