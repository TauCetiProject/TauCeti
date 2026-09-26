/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Basic

/-!
# Projective presentations in a projective stable category

Let `E` be an exact structure and let `P` and `Q` be relative projective presentations
`P.K ⟶ P.P ⟶ X` and `Q.K ⟶ Q.P ⟶ Y`. A morphism `f : X ⟶ Y` lifts to the
projective middle terms and hence induces `ProjectivePresentation.kernelMap` on the kernel terms.
The lift is not unique, but the induced kernel map is unique in the projective stable quotient.

Consequently, the kernel terms of two projective presentations of the same object are canonically
isomorphic in the stable category. A choice of projective presentation for every object produces
an additive functor to the stable category, and any two choices produce canonically naturally
isomorphic functors. For an exact structure with enough projectives, this is the loop construction
before it is descended to an endofunctor of the stable category.

## Main definitions

* `TauCeti.ExactStructure.ProjectivePresentation.projectiveStableIso`: the canonical isomorphism
  between the kernel terms of two relative projective presentations of the same object, in the
  projective stable category.
* `TauCeti.ExactStructure.loopToStableOfPresentations`: the functor to the projective stable
  category determined by a choice of relative projective presentation for every object.
* `TauCeti.ExactStructure.loopToStableOfPresentationsIso`: the canonical natural isomorphism
  comparing two choices.

## Main results

* `TauCeti.ExactStructure.projectiveStableFunctor_map_kernelMap_eq`: any compatible maps between
  projective presentations inducing `f` give `ProjectivePresentation.kernelMap` in the projective
  stable category.

## References

* `TauCeti.CategoryTheory.Exact.Stable.Presentation`, whose injective-presentation comparison
  API is the dual template for this projective-presentation construction.
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

/-- Any compatible maps `a` and `g` between relative projective presentations `P` of `X` and
`Q` of `Y` inducing `f : X ⟶ Y` give `ProjectivePresentation.kernelMap` on the kernel terms in
the projective stable category. -/
theorem projectiveStableFunctor_map_kernelMap_eq (P : E.ProjectivePresentation X)
    (Q : E.ProjectivePresentation Y) (f : X ⟶ Y) (a : P.P ⟶ Q.P) (g : P.K ⟶ Q.K)
    (ha : a ≫ Q.p = P.p ≫ f) (hg : g ≫ Q.i = P.i ≫ a) :
    E.projectiveStableFunctor.map (P.kernelMap Q f) = E.projectiveStableFunctor.map g := by
  let φ : ShortComplex.mk P.i P.p P.zero ⟶ ShortComplex.mk Q.i Q.p Q.zero :=
    { τ₁ := P.kernelMap Q f, τ₂ := P.middleMap Q f, τ₃ := f
      comm₁₂ := P.kernelMap_comp_i Q f
      comm₂₃ := P.middleMap_comp_p Q f }
  let ψ : ShortComplex.mk P.i P.p P.zero ⟶ ShortComplex.mk Q.i Q.p Q.zero :=
    { τ₁ := g, τ₂ := a, τ₃ := f, comm₁₂ := hg, comm₂₃ := ha }
  exact E.projectiveStableFunctor_map_τ₁_eq_of_τ₃_eq Q.conflation P.isProjective
    (φ := φ) (ψ := ψ) rfl

/-- In the projective stable category, the identity induces the identity of the kernel term of a
relative projective presentation. -/
@[simp]
theorem projectiveStableFunctor_map_kernelMap_id (P : E.ProjectivePresentation X) :
    E.projectiveStableFunctor.map (P.kernelMap P (𝟙 X)) = 𝟙 _ :=
  (projectiveStableFunctor_map_kernelMap_eq P P (𝟙 X) (𝟙 P.P) (𝟙 P.K)
    (by simp) (by simp)).trans (E.projectiveStableFunctor.map_id P.K)

/-- In the projective stable category, the morphisms induced on kernel terms of relative
projective presentations compose. -/
/- This is deliberately not a `simp` lemma: the intermediate presentation `Q` occurs only on the
right-hand side, so `simp` cannot infer it. -/
theorem projectiveStableFunctor_map_kernelMap_comp (P : E.ProjectivePresentation X)
    (Q : E.ProjectivePresentation Y) (R : E.ProjectivePresentation Z) (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.projectiveStableFunctor.map (P.kernelMap R (f ≫ g)) =
      E.projectiveStableFunctor.map (P.kernelMap Q f) ≫
        E.projectiveStableFunctor.map (Q.kernelMap R g) := by
  rw [← E.projectiveStableFunctor.map_comp]
  exact projectiveStableFunctor_map_kernelMap_eq P R (f ≫ g)
    (P.middleMap Q f ≫ Q.middleMap R g) (P.kernelMap Q f ≫ Q.kernelMap R g)
    (by simp) (by simp)

namespace ProjectivePresentation

/-- The canonical isomorphism, in the projective stable category, between the kernel terms of
two relative projective presentations of the same object. -/
noncomputable def projectiveStableIso (P Q : E.ProjectivePresentation X) :
    E.projectiveStableFunctor.obj P.K ≅ E.projectiveStableFunctor.obj Q.K where
  hom := E.projectiveStableFunctor.map (P.kernelMap Q (𝟙 X))
  inv := E.projectiveStableFunctor.map (Q.kernelMap P (𝟙 X))
  hom_inv_id := by
    rw [← projectiveStableFunctor_map_kernelMap_comp P Q P, Category.comp_id,
      projectiveStableFunctor_map_kernelMap_id]
  inv_hom_id := by
    rw [← projectiveStableFunctor_map_kernelMap_comp Q P Q, Category.comp_id,
      projectiveStableFunctor_map_kernelMap_id]

/-- The comparison isomorphism is induced by the identity morphism of the presented object. -/
@[simp]
theorem projectiveStableIso_hom (P Q : E.ProjectivePresentation X) :
    (P.projectiveStableIso Q).hom =
      E.projectiveStableFunctor.map (P.kernelMap Q (𝟙 X)) :=
  (rfl)

/-- The inverse comparison isomorphism is the one induced in the opposite direction. -/
@[simp]
theorem projectiveStableIso_inv (P Q : E.ProjectivePresentation X) :
    (P.projectiveStableIso Q).inv =
      E.projectiveStableFunctor.map (Q.kernelMap P (𝟙 X)) :=
  (rfl)

/-- The comparison isomorphisms between two choices of relative projective presentation are
natural with respect to the induced maps on their kernel terms. -/
theorem projectiveStableIso_hom_naturality (P P' : E.ProjectivePresentation X)
    (Q Q' : E.ProjectivePresentation Y) (f : X ⟶ Y) :
    E.projectiveStableFunctor.map (P.kernelMap Q f) ≫ (Q.projectiveStableIso Q').hom =
      (P.projectiveStableIso P').hom ≫
        E.projectiveStableFunctor.map (P'.kernelMap Q' f) := by
  rw [projectiveStableIso_hom, projectiveStableIso_hom,
    ← projectiveStableFunctor_map_kernelMap_comp P Q Q',
    ← projectiveStableFunctor_map_kernelMap_comp P P' Q', Category.comp_id, Category.id_comp]

end ProjectivePresentation

/-- The functor to the projective stable category sending an object to the kernel term of a
chosen relative projective presentation and a morphism to the morphism it induces there. -/
noncomputable def loopToStableOfPresentations (E : ExactStructure C)
    (P : ∀ X : C, E.ProjectivePresentation X) : C ⥤ E.ProjectiveStableCategory where
  obj X := E.projectiveStableFunctor.obj (P X).K
  map f := E.projectiveStableFunctor.map ((P _).kernelMap (P _) f)
  map_id X := projectiveStableFunctor_map_kernelMap_id (P X)
  map_comp f g := projectiveStableFunctor_map_kernelMap_comp _ (P _) _ f g

/-- The object formula for the functor determined by a choice of relative projective
presentations. -/
@[simp]
theorem loopToStableOfPresentations_obj (P : ∀ X : C, E.ProjectivePresentation X) (X : C) :
    (E.loopToStableOfPresentations P).obj X = E.projectiveStableFunctor.obj (P X).K :=
  (rfl)

/-- The morphism formula for the functor determined by a choice of relative projective
presentations. -/
@[simp]
theorem loopToStableOfPresentations_map (P : ∀ X : C, E.ProjectivePresentation X)
    {X Y : C} (f : X ⟶ Y) :
    (E.loopToStableOfPresentations P).map f =
      eqToHom (E.loopToStableOfPresentations_obj P X) ≫
        E.projectiveStableFunctor.map ((P X).kernelMap (P Y) f) ≫
          eqToHom (E.loopToStableOfPresentations_obj P Y).symm :=
  (conj_eqToHom_iff_heq _ _ (E.loopToStableOfPresentations_obj P X)
    (E.loopToStableOfPresentations_obj P Y)).2 HEq.rfl

noncomputable instance loopToStableOfPresentations_additive
    (P : ∀ X : C, E.ProjectivePresentation X) : (E.loopToStableOfPresentations P).Additive where
  map_add {X Y f g} := by
    rw [E.loopToStableOfPresentations_map P (f + g), E.loopToStableOfPresentations_map P f,
      E.loopToStableOfPresentations_map P g, ← Preadditive.comp_add, ← Preadditive.add_comp,
      projectiveStableFunctor_map_kernelMap_eq (P X) (P Y) (f + g)
        ((P X).middleMap (P Y) f + (P X).middleMap (P Y) g)
        ((P X).kernelMap (P Y) f + (P X).kernelMap (P Y) g) (by simp) (by simp),
      Functor.map_add]

/-- Two choices of relative projective presentations give canonically naturally isomorphic
functors to the projective stable category. -/
noncomputable def loopToStableOfPresentationsIso (E : ExactStructure C)
    (P Q : ∀ X : C, E.ProjectivePresentation X) :
    E.loopToStableOfPresentations P ≅ E.loopToStableOfPresentations Q :=
  NatIso.ofComponents (fun X ↦ (P X).projectiveStableIso (Q X)) (fun {X Y} f ↦
    ProjectivePresentation.projectiveStableIso_hom_naturality
      (P X) (Q X) (P Y) (Q Y) f)

/-- The components of the comparison of two choices of relative projective presentations are the
comparison isomorphisms of the two presentations of each object. -/
@[simp]
theorem loopToStableOfPresentationsIso_hom_app (P Q : ∀ X : C, E.ProjectivePresentation X)
    (X : C) :
    (E.loopToStableOfPresentationsIso P Q).hom.app X =
      eqToHom (E.loopToStableOfPresentations_obj P X) ≫
        ((P X).projectiveStableIso (Q X)).hom ≫
          eqToHom (E.loopToStableOfPresentations_obj Q X).symm :=
  (conj_eqToHom_iff_heq _ _ (E.loopToStableOfPresentations_obj P X)
    (E.loopToStableOfPresentations_obj Q X)).2 HEq.rfl

/-- The inverse of the comparison of two choices of relative projective presentations is the
comparison taken in the other order. -/
@[simp]
theorem loopToStableOfPresentationsIso_inv_app (P Q : ∀ X : C, E.ProjectivePresentation X)
    (X : C) :
    (E.loopToStableOfPresentationsIso P Q).inv.app X =
      eqToHom (E.loopToStableOfPresentations_obj Q X) ≫
        ((P X).projectiveStableIso (Q X)).inv ≫
          eqToHom (E.loopToStableOfPresentations_obj P X).symm :=
  (conj_eqToHom_iff_heq _ _ (E.loopToStableOfPresentations_obj Q X)
    (E.loopToStableOfPresentations_obj P X)).2 HEq.rfl

end ExactStructure

end TauCeti
