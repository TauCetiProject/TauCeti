/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair

/-!
# Homotopies of morphisms of pairs of simplicial sets

A homotopy between morphisms of a pair of simplicial sets consists of a homotopy on the
subcomplexes and a homotopy on the total complexes which agree on the subcomplexes, that is,
`SSetPair.Homotopy`.  This is the simplicial analogue of `TopPair.Homotopy` in
`Mathlib/Topology/Category/TopPair.lean` (J. Scharmberg), with the same two homotopies and the
same whiskered commuting square.

The file also records what such a commuting square gives on the combinatorial homotopies that
`SSet.Homotopy.toSimplicialObjectHomotopy` extracts: the two families of morphisms
`Xₙ ⟶ Y'ₙ₊₁` commute with the morphisms of the square.  That compatibility is what makes the
chain homotopies of the absolute case descend to relative chains.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

open scoped Simplicial

universe w

namespace SSet.Homotopy

variable {X Y X' Y' : SSet.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} {u : X ⟶ X'} {v : Y ⟶ Y'}

/-- The combinatorial homotopy extracted from a simplicial homotopy sends an `n`-simplex `x` to
the value of the homotopy at the `i`-th nondegenerate `(n + 1)`-simplex of `Δ[n] ⊗ Δ[1]`. -/
private lemma toSimplicialObjectHomotopy_h_apply (H : SSet.Homotopy f g) {n : ℕ} (i : Fin (n + 1))
    (x : X _⦋n⦌) :
    H.toSimplicialObjectHomotopy.h i x =
      (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h).app (op ⦋n + 1⦌)
        (prodStdSimplex.nonDegenerateEquiv₁ i).1 := rfl

/-- Simplicial homotopies which fit into a commutative square induce compatible families of
morphisms `Xₙ ⟶ Y'ₙ₊₁`. -/
lemma toSimplicialObjectHomotopy_h_comm (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (hu : u ▷ Δ[1] ≫ H'.h = H.h ≫ v) (n : ℕ) (i : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ H'.toSimplicialObjectHomotopy.h i =
      H.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n + 1⦌) := by
  have key : ∀ x : X _⦋n⦌, yonedaEquiv.symm (u.app (op ⦋n⦌) x) ▷ Δ[1] ≫ H'.h =
      (yonedaEquiv.symm x ▷ Δ[1] ≫ H.h) ≫ v := fun x ↦ by
    rw [← yonedaEquiv_symm_comp, comp_whiskerRight, Category.assoc, hu, Category.assoc]
  ext x
  simp only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
    toSimplicialObjectHomotopy_h_apply]
  rw [key x, NatTrans.comp_app, CategoryTheory.comp_apply]

end SSet.Homotopy

namespace SSetPair

/-- A homotopy between morphisms of pairs of simplicial sets consists of a homotopy on the
subcomplexes and a homotopy on the total complexes which agree on the subcomplexes. -/
@[ext]
structure Homotopy {P P' : SSetPair.{w}} (f g : P ⟶ P') where
  /-- The homotopy on the subcomplexes. -/
  left : SSet.Homotopy f.left g.left
  /-- The homotopy on the total complexes. -/
  right : SSet.Homotopy f.right g.right
  /-- The two homotopies agree on the subcomplexes. -/
  w : P.hom ▷ Δ[1] ≫ right.h = left.h ≫ P'.hom

end SSetPair
