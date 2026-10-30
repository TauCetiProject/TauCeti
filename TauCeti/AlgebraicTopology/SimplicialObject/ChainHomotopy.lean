/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# Chain homotopies of simplicial objects in a commutative square

A simplicial homotopy between morphisms of simplicial objects induces a chain homotopy between
the induced morphisms of alternating face map complexes.  This file records that the construction
is compatible with a commutative square: two simplicial homotopies whose defining families of
morphisms commute with a pair of morphisms of simplicial objects give chain homotopies whose
components commute with the induced chain maps.

This is the form in which the construction is applied to a pair of simplicial sets, where the
square is the inclusion of the subcomplex.
-/

@[expose] public section

open CategoryTheory Limits Opposite AlgebraicTopology

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X Y X' Y' : SimplicialObject C} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- Simplicial homotopies which are compatible with a commutative square of simplicial objects
induce compatible chain homotopies on the alternating face map complexes. -/
lemma toChainHomotopy_hom_comm (H : Homotopy f g) (H' : Homotopy f' g') (u : X ⟶ X') (v : Y ⟶ Y')
    (hu : ∀ (n : ℕ) (i : Fin (n + 1)), u.app (op ⦋n⦌) ≫ H'.h i = H.h i ≫ v.app (op ⦋n + 1⦌))
    (p q : ℕ) :
    ((alternatingFaceMapComplex C).map u).f p ≫ H'.toChainHomotopy.hom p q =
      H.toChainHomotopy.hom p q ≫ ((alternatingFaceMapComplex C).map v).f q := by
  rcases eq_or_ne (p + 1) q with rfl | h
  · dsimp only [toChainHomotopy]
    rw [ToChainHomotopy.hom_eq, ToChainHomotopy.hom_eq, alternatingFaceMapComplex_map_f,
      alternatingFaceMapComplex_map_f]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
      Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    exact congrArg _ (Finset.sum_congr rfl fun i _ ↦ by rw [hu])
  · dsimp only [toChainHomotopy]
    rw [ToChainHomotopy.hom_eq_zero _ _ _ h, ToChainHomotopy.hom_eq_zero _ _ _ h]
    simp

/-- If every simplicial prism term vanishes between two morphisms, so does the induced chain
homotopy component. The morphisms need only exist in these degrees, so the target may be a
relative quotient without a simplicial structure. -/
lemma comp_toChainHomotopy_hom_comp_eq_zero (H : Homotopy f g) (n : ℕ) {A B : C}
    (a : A ⟶ X.obj (op ⦋n⦌)) (b : Y.obj (op ⦋n + 1⦌) ⟶ B)
    (h : ∀ i : Fin (n + 1), a ≫ H.h i ≫ b = 0) :
    a ≫ H.toChainHomotopy.hom n (n + 1) ≫ b = 0 := by
  dsimp only [toChainHomotopy]
  rw [ToChainHomotopy.hom_eq]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Preadditive.comp_sum,
    Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, h, smul_zero,
    Finset.sum_const_zero, neg_zero]

end CategoryTheory.SimplicialObject.Homotopy
