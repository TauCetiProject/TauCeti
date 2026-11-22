/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import TauCeti.CategoryTheory.Bicategory.Functor.TwoFiberProduct
public import TauCeti.CategoryTheory.Sites.Descent.Discrete

/-!
# The 2-fiber product of discrete pseudofunctors

For presheaves of types, the 2-fiber product of the induced discrete pseudofunctors is the
discrete pseudofunctor of their fiber product. Precisely, let `f : P ⟶ F`, `g : P ⟶ G`,
`α : F ⟶ H` and `β : G ⟶ H` be morphisms of presheaves of types on `C` and let
`e : ofPresheafMap f ≫ ofPresheafMap α ≅ ofPresheafMap g ≫ ofPresheafMap β` be an invertible
modification (one exists exactly when `f ≫ α = g ≫ β`, see
`CategoryTheory.Pseudofunctor.ofPresheafMapCompIso`). The square is a pullback of presheaves
exactly when the induced strong transformation
`twoFiberProduct.lift _ _ (ofPresheafMap f) (ofPresheafMap g) e` from `ofPresheaf P` to
`twoFiberProduct (ofPresheafMap α) (ofPresheafMap β)` is an equivalence on every fiber.

The fiber of the 2-fiber product over `X` has as objects the triples `(x, y, α x ≅ β y)` with
`x ∈ F(X)` and `y ∈ G(X)`; since the fibers of `ofPresheaf H` are discrete, the isomorphism is
the equality `α x = β y`, and a morphism of triples is a pair of equalities. So the fiber is the
discrete category on `F(X) ×_{H(X)} G(X)`, and the comparison is an equivalence exactly when
`P(X) → F(X) ×_{H(X)} G(X)` is bijective (Stacks, Section 4.31 (003O)). This is how sheaves of
sets, and in particular algebraic spaces and schemes, have their fiber products computed inside
the 2-category of stacks in setoids.

## Main declarations

* `TauCeti.Stack.twoFiberProduct.isEquivalence_lift_ofPresheafMap_app`: for a pullback square of
  presheaves of types, the comparison from the discrete pseudofunctor of `P` to the 2-fiber
  product is an equivalence on every fiber.
* `TauCeti.Stack.twoFiberProduct.isPullback_iff_isEquivalence_lift_ofPresheafMap_app`: the square
  is a pullback exactly when the comparison is an equivalence on every fiber.

## References

* [Stacks Project, Section 003O](https://stacks.math.columbia.edu/tag/003O)
-/

public section

universe w' w v u

namespace TauCeti.Stack.twoFiberProduct

open CategoryTheory Limits Pseudofunctor
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C] {P F G H : Cᵒᵖ ⥤ Type w}
  {f : P ⟶ F} {g : P ⟶ G} {α : F ⟶ H} {β : G ⟶ H}
  (e : Iso (C := ofPresheaf.{w'} P ⟶ ofPresheaf.{w'} H)
    ((ofPresheafMap f).vcomp (ofPresheafMap α)) ((ofPresheafMap g).vcomp (ofPresheafMap β)))

/-- For a pullback square of presheaves of types, the comparison from the discrete
pseudofunctor of `P` to the 2-fiber product of `ofPresheafMap α` and `ofPresheafMap β` is an
equivalence on every fiber. -/
theorem isEquivalence_lift_ofPresheafMap_app (h : IsPullback f g α β)
    (X : LocallyDiscrete Cᵒᵖ) :
    ((lift (ofPresheafMap α) (ofPresheafMap β) (ofPresheafMap f) (ofPresheafMap g) e).app
      X).toFunctor.IsEquivalence := by
  set Φ := ((lift (ofPresheafMap α) (ofPresheafMap β) (ofPresheafMap f) (ofPresheafMap g)
    e).app X).toFunctor
  have hX := h.app X.as
  have : Φ.Faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩
  have : Φ.Full := ⟨fun {x y} φ ↦ by
    -- The components of `φ` are equalities `f x = f y` and `g x = g y`, so `x = y`.
    have hxy : x.down.as = y.down.as := Types.ext_of_isPullback hX
      (ofPresheaf.eq_of_hom (X := X.as) φ.fst) (ofPresheaf.eq_of_hom (X := X.as) φ.snd)
    exact ⟨ofPresheaf.homMk (X := X.as) hxy,
      CategoricalPullback.hom_ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩⟩
  have : Φ.EssSurj := ⟨fun z ↦ by
    -- The structure isomorphism of `z` is an equality `α z.fst = β z.snd`.
    obtain ⟨x, hf, hg⟩ :=
      Types.exists_of_isPullback hX _ _ (ofPresheaf.eq_of_hom (X := X.as) z.iso.hom)
    exact ⟨⟨⟨x⟩⟩, ⟨CategoricalPullback.mkIso (ofPresheaf.isoMk (X := X.as) hf)
      (ofPresheaf.isoMk (X := X.as) hg) (Subsingleton.elim _ _)⟩⟩⟩
  exact { }

/-- A square of presheaves of types `f ≫ α = g ≫ β`, witnessed by an invertible modification
`e`, is a pullback exactly when the comparison from the discrete pseudofunctor of `P` to the
2-fiber product of `ofPresheafMap α` and `ofPresheafMap β` is an equivalence on every fiber. -/
theorem isPullback_iff_isEquivalence_lift_ofPresheafMap_app :
    IsPullback f g α β ↔ ∀ X : LocallyDiscrete Cᵒᵖ,
      ((lift (ofPresheafMap α) (ofPresheafMap β) (ofPresheafMap f) (ofPresheafMap g) e).app
        X).toFunctor.IsEquivalence := by
  refine ⟨fun h X ↦ isEquivalence_lift_ofPresheafMap_app e h X, fun H ↦ ?_⟩
  have hw : f ≫ α = g ≫ β := eq_of_ofPresheafMap_modification
    ((ofPresheafMapComp f α).hom ≫ e.hom ≫ (ofPresheafMapComp g β).inv).as
  refine IsPullback.of_forall_isPullback_app fun X ↦ (Types.isPullback_iff _ _ _ _).2
    ⟨by simp only [← NatTrans.comp_app, hw], fun x y ⟨hf, hg⟩ ↦ ?_, fun a b hab ↦ ?_⟩
  all_goals
    set Φ := ((lift (ofPresheafMap α) (ofPresheafMap β) (ofPresheafMap f) (ofPresheafMap g)
      e).app (.mk X)).toFunctor
    have := H (.mk X)
  · -- A pair of equalities `f x = f y`, `g x = g y` is a morphism between the images of `x`
    -- and `y`, which lifts to the discrete fiber of `P` by fullness.
    let φ : Φ.obj ⟨⟨x⟩⟩ ⟶ Φ.obj ⟨⟨y⟩⟩ :=
      ⟨ofPresheaf.homMk hf, ofPresheaf.homMk hg, Subsingleton.elim _ _⟩
    exact ofPresheaf.eq_of_hom (Φ.preimage φ)
  · -- An equality `α a = β b` is an object of the 2-fiber product, which is the image of some
    -- element of `P` up to isomorphism by essential surjectivity.
    let z : Fiber (ofPresheafMap.{w'} α) (ofPresheafMap.{w'} β) X :=
      ⟨⟨⟨a⟩⟩, ⟨⟨b⟩⟩, ofPresheaf.isoMk hab⟩
    exact ⟨(Φ.objPreimage z).down.as, ofPresheaf.eq_of_hom (Φ.objObjPreimageIso z).hom.fst,
      ofPresheaf.eq_of_hom (Φ.objObjPreimageIso z).hom.snd⟩

end TauCeti.Stack.twoFiberProduct
