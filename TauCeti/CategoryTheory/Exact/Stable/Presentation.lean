/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# Injective presentations in a projective stable category

Let `E` be an exact structure and let `P` and `Q` be relative injective presentations
`X ⟶ P.I ⟶ P.K` and `Y ⟶ Q.I ⟶ Q.K`. A morphism `f : X ⟶ Y` extends to the injective middle
terms and hence induces `InjectivePresentation.cokernelMap` on the cokernel terms. That induced
morphism depends on a choice, but once `Q.I` is relatively projective the choice disappears in
the projective stable quotient: any two extensions of `f` induce the same morphism
`P.K ⟶ Q.K` there.

This file records that independence and its consequences. The construction becomes functorial in
the stable quotient, so two presentations of the same object have canonically isomorphic cokernel
terms, and a choice of presentation with projective-injective middle term for every object
produces a functor from `C` to the stable category which is independent, up to a canonical
natural isomorphism, of that choice. For a Frobenius exact structure the middle terms are
automatically projective and this functor is the suspension.

## Main definitions

* `TauCeti.ExactStructure.InjectivePresentation.projectiveStableIso`: the canonical isomorphism
  between the cokernel terms of two relative injective presentations of the same object, in the
  projective stable category.
* `TauCeti.ExactStructure.suspensionToStableOfPresentations`: the functor to the projective
  stable category determined by a choice of relative injective presentations with relatively
  projective middle terms.
* `TauCeti.ExactStructure.suspensionToStableOfPresentationsIso`: the canonical natural
  isomorphism comparing two such choices.

## Main results

* `TauCeti.ExactStructure.projectiveStableFunctor_map_cokernelMap_eq`: any extension of `f` to the
  injective middle terms induces the morphism `InjectivePresentation.cokernelMap` on cokernel
  terms, in the projective stable category.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]

namespace ExactStructure

variable {E : ExactStructure C} {X Y Z : C}

/-- Any pair of morphisms `a` and `g` extending `f : X ⟶ Y` across relative injective
presentations `P` of `X` and `Q` of `Y` induces `InjectivePresentation.cokernelMap` on the
cokernel terms, once the middle term of `Q` is relatively projective. -/
theorem projectiveStableFunctor_map_cokernelMap_eq (P : E.InjectivePresentation X)
    (Q : E.InjectivePresentation Y) (hQ : E.isProjective Q.I) (f : X ⟶ Y) (a : P.I ⟶ Q.I)
    (g : P.K ⟶ Q.K) (ha : P.i ≫ a = f ≫ Q.i) (hg : P.p ≫ g = a ≫ Q.p) :
    E.projectiveStableFunctor.map (P.cokernelMap Q f) = E.projectiveStableFunctor.map g := by
  let φ : ShortComplex.mk P.i P.p P.zero ⟶ ShortComplex.mk Q.i Q.p Q.zero :=
    { τ₁ := f, τ₂ := P.middleMap Q f, τ₃ := P.cokernelMap Q f
      comm₁₂ := (P.i_comp_middleMap Q f).symm
      comm₂₃ := (P.p_comp_cokernelMap Q f).symm }
  let ψ : ShortComplex.mk P.i P.p P.zero ⟶ ShortComplex.mk Q.i Q.p Q.zero :=
    { τ₁ := f, τ₂ := a, τ₃ := g, comm₁₂ := ha.symm, comm₂₃ := hg.symm }
  exact E.projectiveStableFunctor_map_τ₃_eq_of_τ₁_eq P.conflation hQ (φ := φ) (ψ := ψ) rfl

/-- In the projective stable category, the identity induces the identity of the cokernel term of
a relative injective presentation. -/
@[simp]
theorem projectiveStableFunctor_map_cokernelMap_id (P : E.InjectivePresentation X)
    (hP : E.isProjective P.I) :
    E.projectiveStableFunctor.map (P.cokernelMap P (𝟙 X)) = 𝟙 _ :=
  (projectiveStableFunctor_map_cokernelMap_eq P P hP (𝟙 X) (𝟙 P.I) (𝟙 P.K)
    (by simp) (by simp)).trans (E.projectiveStableFunctor.map_id P.K)

/-- In the projective stable category, the morphisms induced on cokernel terms of relative
injective presentations compose. -/
/- This is deliberately not a `simp` lemma: the intermediate presentation `Q` occurs only on the
right-hand side, so `simp` can never infer it and the `simpNF` linter rejects the attribute. -/
theorem projectiveStableFunctor_map_cokernelMap_comp (P : E.InjectivePresentation X)
    (Q : E.InjectivePresentation Y) (R : E.InjectivePresentation Z) (hR : E.isProjective R.I)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.projectiveStableFunctor.map (P.cokernelMap R (f ≫ g)) =
      E.projectiveStableFunctor.map (P.cokernelMap Q f) ≫
        E.projectiveStableFunctor.map (Q.cokernelMap R g) := by
  rw [← E.projectiveStableFunctor.map_comp]
  exact projectiveStableFunctor_map_cokernelMap_eq P R hR (f ≫ g)
    (P.middleMap Q f ≫ Q.middleMap R g) (P.cokernelMap Q f ≫ Q.cokernelMap R g)
    (by simp) (by simp)

namespace InjectivePresentation

/-- The canonical isomorphism, in the projective stable category, between the cokernel terms of
two relative injective presentations of the same object with relatively projective middle
terms. -/
noncomputable def projectiveStableIso (P Q : E.InjectivePresentation X)
    (hP : E.isProjective P.I) (hQ : E.isProjective Q.I) :
    E.projectiveStableFunctor.obj P.K ≅ E.projectiveStableFunctor.obj Q.K where
  hom := E.projectiveStableFunctor.map (P.cokernelMap Q (𝟙 X))
  inv := E.projectiveStableFunctor.map (Q.cokernelMap P (𝟙 X))
  hom_inv_id := by
    rw [← projectiveStableFunctor_map_cokernelMap_comp P Q P hP, Category.comp_id,
      projectiveStableFunctor_map_cokernelMap_id P hP]
  inv_hom_id := by
    rw [← projectiveStableFunctor_map_cokernelMap_comp Q P Q hQ, Category.comp_id,
      projectiveStableFunctor_map_cokernelMap_id Q hQ]

/-- The comparison isomorphism is induced by the identity morphism of the presented object. -/
@[simp]
theorem projectiveStableIso_hom (P Q : E.InjectivePresentation X)
    (hP : E.isProjective P.I) (hQ : E.isProjective Q.I) :
    (P.projectiveStableIso Q hP hQ).hom =
      E.projectiveStableFunctor.map (P.cokernelMap Q (𝟙 X)) :=
  (rfl)

/-- The inverse comparison isomorphism is the one induced in the opposite direction. -/
@[simp]
theorem projectiveStableIso_inv (P Q : E.InjectivePresentation X)
    (hP : E.isProjective P.I) (hQ : E.isProjective Q.I) :
    (P.projectiveStableIso Q hP hQ).inv =
      E.projectiveStableFunctor.map (Q.cokernelMap P (𝟙 X)) :=
  (rfl)

end InjectivePresentation

/-- The comparison isomorphisms between two choices of relative injective presentation are
natural: they turn the morphism induced by `f` on one choice into the morphism induced by `f` on
the other. -/
theorem projectiveStableIso_hom_naturality (P P' : E.InjectivePresentation X)
    (Q Q' : E.InjectivePresentation Y)
    (hP : E.isProjective P.I) (hP' : E.isProjective P'.I) (hQ : E.isProjective Q.I)
    (hQ' : E.isProjective Q'.I) (f : X ⟶ Y) :
    E.projectiveStableFunctor.map (P.cokernelMap Q f) ≫ (Q.projectiveStableIso Q' hQ hQ').hom =
      (P.projectiveStableIso P' hP hP').hom ≫
        E.projectiveStableFunctor.map (P'.cokernelMap Q' f) := by
  rw [InjectivePresentation.projectiveStableIso_hom,
    InjectivePresentation.projectiveStableIso_hom,
    ← projectiveStableFunctor_map_cokernelMap_comp P Q Q' hQ',
    ← projectiveStableFunctor_map_cokernelMap_comp P P' Q' hQ', Category.comp_id, Category.id_comp]

/-- The functor to the projective stable category sending an object to the cokernel term of a
chosen relative injective presentation with relatively projective middle term, and a morphism to
the morphism it induces there. For a Frobenius exact structure this is Happel's suspension,
before it is descended to an endofunctor of the stable category. -/
noncomputable def suspensionToStableOfPresentations (E : ExactStructure C)
    (P : ∀ X : C, E.InjectivePresentation X) (hP : ∀ X : C, E.isProjective (P X).I) :
    C ⥤ E.ProjectiveStableCategory where
  obj X := E.projectiveStableFunctor.obj (P X).K
  map f := E.projectiveStableFunctor.map ((P _).cokernelMap (P _) f)
  map_id X := projectiveStableFunctor_map_cokernelMap_id (P X) (hP X)
  map_comp f g := projectiveStableFunctor_map_cokernelMap_comp _ (P _) _ (hP _) f g

/-- The object formula for the functor determined by a choice of relative injective
presentations. -/
@[simp]
theorem suspensionToStableOfPresentations_obj (P : ∀ X : C, E.InjectivePresentation X)
    (hP : ∀ X : C, E.isProjective (P X).I) (X : C) :
    (E.suspensionToStableOfPresentations P hP).obj X =
      E.projectiveStableFunctor.obj (P X).K :=
  (rfl)

/-- The morphism formula for the functor determined by a choice of relative injective
presentations. -/
@[simp]
theorem suspensionToStableOfPresentations_map (P : ∀ X : C, E.InjectivePresentation X)
    (hP : ∀ X : C, E.isProjective (P X).I) {X Y : C} (f : X ⟶ Y) :
    (E.suspensionToStableOfPresentations P hP).map f =
      eqToHom (E.suspensionToStableOfPresentations_obj P hP X) ≫
        E.projectiveStableFunctor.map ((P X).cokernelMap (P Y) f) ≫
          eqToHom (E.suspensionToStableOfPresentations_obj P hP Y).symm :=
  (conj_eqToHom_iff_heq _ _ (E.suspensionToStableOfPresentations_obj P hP X)
    (E.suspensionToStableOfPresentations_obj P hP Y)).2 HEq.rfl

noncomputable instance suspensionToStableOfPresentations_additive
    (P : ∀ X : C, E.InjectivePresentation X) (hP : ∀ X : C, E.isProjective (P X).I) :
    (E.suspensionToStableOfPresentations P hP).Additive where
  map_add {X Y f g} := by
    rw [E.suspensionToStableOfPresentations_map P hP (f + g),
      E.suspensionToStableOfPresentations_map P hP f,
      E.suspensionToStableOfPresentations_map P hP g,
      ← Preadditive.comp_add, ← Preadditive.add_comp,
      projectiveStableFunctor_map_cokernelMap_eq (P X) (P Y) (hP Y) (f + g)
        ((P X).middleMap (P Y) f + (P X).middleMap (P Y) g)
        ((P X).cokernelMap (P Y) f + (P X).cokernelMap (P Y) g) (by simp) (by simp),
      Functor.map_add]

/-- Two choices of relative injective presentations with relatively projective middle terms give
canonically naturally isomorphic functors to the projective stable category. -/
noncomputable def suspensionToStableOfPresentationsIso (E : ExactStructure C)
    (P Q : ∀ X : C, E.InjectivePresentation X) (hP : ∀ X : C, E.isProjective (P X).I)
    (hQ : ∀ X : C, E.isProjective (Q X).I) :
    E.suspensionToStableOfPresentations P hP ≅ E.suspensionToStableOfPresentations Q hQ :=
  -- The morphisms of both functors and the components of the comparison are, in this file,
  -- the morphisms `E.projectiveStableFunctor.map (_.cokernelMap _ _)` appearing in the lemma.
  NatIso.ofComponents (fun X ↦ (P X).projectiveStableIso (Q X) (hP X) (hQ X)) (fun {X Y} f ↦
    projectiveStableIso_hom_naturality
      (P X) (Q X) (P Y) (Q Y) (hP X) (hQ X) (hP Y) (hQ Y) f)

/-- The components of the comparison of two choices of relative injective presentations are the
comparison isomorphisms of the two presentations of each object. -/
@[simp]
theorem suspensionToStableOfPresentationsIso_hom_app (P Q : ∀ X : C, E.InjectivePresentation X)
    (hP : ∀ X : C, E.isProjective (P X).I) (hQ : ∀ X : C, E.isProjective (Q X).I) (X : C) :
    (E.suspensionToStableOfPresentationsIso P Q hP hQ).hom.app X =
      eqToHom (E.suspensionToStableOfPresentations_obj P hP X) ≫
        ((P X).projectiveStableIso (Q X) (hP X) (hQ X)).hom ≫
          eqToHom (E.suspensionToStableOfPresentations_obj Q hQ X).symm :=
  (conj_eqToHom_iff_heq _ _ (E.suspensionToStableOfPresentations_obj P hP X)
    (E.suspensionToStableOfPresentations_obj Q hQ X)).2 HEq.rfl

/-- The inverse of the comparison of two choices of relative injective presentations is the
comparison taken in the other order. -/
@[simp]
theorem suspensionToStableOfPresentationsIso_inv_app (P Q : ∀ X : C, E.InjectivePresentation X)
    (hP : ∀ X : C, E.isProjective (P X).I) (hQ : ∀ X : C, E.isProjective (Q X).I) (X : C) :
    (E.suspensionToStableOfPresentationsIso P Q hP hQ).inv.app X =
      eqToHom (E.suspensionToStableOfPresentations_obj Q hQ X) ≫
        ((P X).projectiveStableIso (Q X) (hP X) (hQ X)).inv ≫
          eqToHom (E.suspensionToStableOfPresentations_obj P hP X).symm :=
  (conj_eqToHom_iff_heq _ _ (E.suspensionToStableOfPresentations_obj Q hQ X)
    (E.suspensionToStableOfPresentations_obj P hP X)).2 HEq.rfl

end ExactStructure

end TauCeti
