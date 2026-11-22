/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic
public import TauCeti.AlgebraicGeometry.Stack.OfSheaf
public import TauCeti.CategoryTheory.Bicategory.Functor.TwoFiberProduct
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat

/-!
# Morphisms representable by algebraic spaces

A pseudofunctor `P` on schemes is *representable by an algebraic space* if it is equivalent to the
stack in setoids `StackInGroupoids.ofSheaf F` of an algebraic space `F`: there is a strong
transformation `ofSheaf F ⟶ P` whose components are equivalences of categories. A morphism
`f : X ⟶ Y` of pseudofunctors on schemes is *representable by algebraic spaces* if for every
scheme `T` and every morphism `y : h_T ⟶ Y` from the stack of `T`, the 2-fiber product
`T ×_Y X = twoFiberProduct y f` is representable by an algebraic space (Stacks, Definition 94.9.1
(02ZW)).

Stacks phrases the condition with objects `y` of the fiber `Y(T)`; by the 2-Yoneda lemma these are
the morphisms `h_T ⟶ Y` up to isomorphism, so the two formulations agree. This notion underlies
the definition of algebraic stacks (the diagonal is representable by algebraic spaces) and of the
properties of morphisms of stacks defined by base change to algebraic spaces.

The definitions make sense for arbitrary `Cat`-valued pseudofunctors on schemes; morphisms of
stacks in groupoids (`StackInGroupoids.Hom`) are a special case.

## Main declarations

* `TauCeti.AlgebraicGeometry.IsRepresentableBySpace`: a pseudofunctor on schemes equivalent to the
  stack in setoids of an algebraic space.
* `TauCeti.AlgebraicGeometry.isRepresentableBySpace_iff_of_isEquivalence`: being representable by
  an algebraic space is invariant under strong transformations whose components are equivalences.
* `TauCeti.AlgebraicGeometry.IsRepresentableBySpaces`: morphisms representable by algebraic
  spaces.
* `TauCeti.AlgebraicGeometry.IsRepresentableBySpaces.of_isEquivalence`: a morphism whose
  components are equivalences, in particular an identity, is representable by algebraic spaces.
* `TauCeti.AlgebraicGeometry.IsRepresentableBySpaces.twoFiberProduct_fst`: representability by
  algebraic spaces is stable under base change.

## References

* [Stacks Project, Definition 94.9.1](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Lemma 94.9.7](https://stacks.math.columbia.edu/tag/0300)
-/

public section

open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry TauCeti.Stack

universe u

/-- A pseudofunctor `P` on schemes is *representable by an algebraic space* if it is equivalent to
the stack in setoids of an algebraic space: there are an fppf sheaf `F` which is an algebraic
space and a strong transformation `StackInGroupoids.ofSheaf F ⟶ P` whose components are
equivalences of categories. -/
def IsRepresentableBySpace (P : SchPseudofunctor.{u}) : Prop :=
  ∃ (F : Sheaf Scheme.fppfTopology.{u} (Type u))
    (φ : (StackInGroupoids.ofSheaf F).toSchPseudofunctor ⟶ P),
    Spaces.IsAlgebraicSpace F.obj ∧ ∀ S, (φ.app S).toFunctor.IsEquivalence

/-- The stack in setoids of an algebraic space is representable by an algebraic space. -/
lemma isRepresentableBySpace_ofSheaf (F : Sheaf Scheme.fppfTopology.{u} (Type u))
    (hF : Spaces.IsAlgebraicSpace F.obj) :
    IsRepresentableBySpace (StackInGroupoids.ofSheaf F).toSchPseudofunctor :=
  ⟨F, 𝟙 _, hF, fun _ ↦ inferInstanceAs (Functor.id _).IsEquivalence⟩

/-- The stack of a scheme is representable by an algebraic space. -/
lemma isRepresentableBySpace_ofScheme (T : Scheme.{u}) :
    IsRepresentableBySpace (StackInGroupoids.ofScheme T).toSchPseudofunctor :=
  isRepresentableBySpace_ofSheaf _ (Spaces.IsAlgebraicSpace.yoneda_obj T)

/-- Being representable by an algebraic space is transported along a strong transformation whose
components are equivalences. -/
lemma IsRepresentableBySpace.of_isEquivalence {P Q : SchPseudofunctor.{u}} (ψ : P ⟶ Q)
    [∀ S, (ψ.app S).toFunctor.IsEquivalence] (hP : IsRepresentableBySpace P) :
    IsRepresentableBySpace Q := by
  obtain ⟨F, φ, hF, hφ⟩ := hP
  exact ⟨F, φ ≫ ψ, hF, fun S ↦
    have := hφ S
    inferInstanceAs ((φ.app S).toFunctor ⋙ (ψ.app S).toFunctor).IsEquivalence⟩

/-- Being representable by an algebraic space is invariant under strong transformations whose
components are equivalences. -/
lemma isRepresentableBySpace_iff_of_isEquivalence {P Q : SchPseudofunctor.{u}} (ψ : P ⟶ Q)
    [∀ S, (ψ.app S).toFunctor.IsEquivalence] :
    IsRepresentableBySpace P ↔ IsRepresentableBySpace Q := by
  refine ⟨IsRepresentableBySpace.of_isEquivalence ψ, fun hQ ↦ ?_⟩
  -- The inverse of `ψ` has the chosen quasi-inverses of the components of `ψ` as components.
  have (S : LocallyDiscrete Scheme.{u}ᵒᵖ) :
      (ψ.equivalenceOfIsEquivalence.inv.app S).toFunctor.IsEquivalence := by
    rw [Pseudofunctor.StrongTrans.equivalenceOfIsEquivalence_inv_app]
    exact inferInstanceAs (ψ.app S).toFunctor.inv.IsEquivalence
  exact hQ.of_isEquivalence ψ.equivalenceOfIsEquivalence.inv

/-- A morphism `f : X ⟶ Y` of pseudofunctors on schemes is *representable by algebraic spaces* if
for every scheme `T` and every morphism `y : h_T ⟶ Y` from the stack of `T`, the 2-fiber product
`T ×_Y X` of `y` and `f` is representable by an algebraic space (Stacks, Definition 94.9.1
(02ZW)). -/
@[stacks 02ZW]
def IsRepresentableBySpaces {X Y : SchPseudofunctor.{u}} (f : X ⟶ Y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (y : (StackInGroupoids.ofScheme T).toSchPseudofunctor ⟶ Y),
    IsRepresentableBySpace (twoFiberProduct.{u + 1, u} y f)

lemma isRepresentableBySpaces_iff {X Y : SchPseudofunctor.{u}} (f : X ⟶ Y) :
    IsRepresentableBySpaces f ↔
      ∀ ⦃T : Scheme.{u}⦄ (y : (StackInGroupoids.ofScheme T).toSchPseudofunctor ⟶ Y),
        IsRepresentableBySpace (twoFiberProduct.{u + 1, u} y f) :=
  Iff.rfl

namespace IsRepresentableBySpaces

/-- A morphism whose components are equivalences of categories is representable by algebraic
spaces: its 2-fiber product with `h_T ⟶ Y` is equivalent to `h_T` through the first
projection. -/
lemma of_isEquivalence {X Y : SchPseudofunctor.{u}} (f : X ⟶ Y)
    [∀ S, (f.app S).toFunctor.IsEquivalence] : IsRepresentableBySpaces f := fun T y ↦
  (isRepresentableBySpace_iff_of_isEquivalence (twoFiberProduct.fst.{u + 1, u} y f)).2
    (isRepresentableBySpace_ofScheme T)

/-- The identity of a pseudofunctor on schemes is representable by algebraic spaces. -/
lemma id (X : SchPseudofunctor.{u}) :
    IsRepresentableBySpaces (Pseudofunctor.StrongTrans.id X) :=
  have (S : LocallyDiscrete Scheme.{u}ᵒᵖ) :
      ((Pseudofunctor.StrongTrans.id X).app S).toFunctor.IsEquivalence :=
    inferInstanceAs (Functor.id _).IsEquivalence
  of_isEquivalence _

/-- Representability by algebraic spaces is stable under base change: if `f : X ⟶ Y` is
representable by algebraic spaces, so is the projection `Y' ×_Y X ⟶ Y'` of its 2-fiber product
with any `g : Y' ⟶ Y` (Stacks, Lemma 94.9.7 (0300)). The 2-fiber product of `y : h_T ⟶ Y'` with
the projection is that of `y ≫ g` with `f`, by the pasting law. -/
@[stacks 0300]
lemma twoFiberProduct_fst {X Y Y' : SchPseudofunctor.{u}} {f : X ⟶ Y}
    (hf : IsRepresentableBySpaces f) (g : Y' ⟶ Y) :
    IsRepresentableBySpaces (twoFiberProduct.fst.{u + 1, u} g f) := fun _ y ↦
  (isRepresentableBySpace_iff_of_isEquivalence
    (twoFiberProduct.pullbackRightPullbackFst.{u + 1, u} g f y)).2 (hf (y ≫ g))

end IsRepresentableBySpaces

end TauCeti.AlgebraicGeometry
