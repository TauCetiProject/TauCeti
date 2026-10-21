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

Finally, it records where the combinatorial homotopy `h` from `f` to `g` starts: the initial vertex
of `h i x` is the image under `f` of the initial vertex of `x`, the first edge of `h (i + 1) x` is
the image under `f` of the first edge of `x`, and the first edge of `h 0 x` is the track `h 0 x₀`
of the initial vertex `x₀` of `x`.  These are what a construction transporting data along the
initial vertices of simplices, such as twisted chains, needs to lift the combinatorial homotopy.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

open scoped Simplicial

universe w

namespace SSet.Homotopy

variable {X Y X' Y' : SSet.{w}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'} {u : X ⟶ X'} {v : Y ⟶ Y'}

/-- The combinatorial homotopy extracted from a simplicial homotopy sends an `n`-simplex `x` to
the value of the homotopy at the pair formed by the `i`-th degeneracy of `x` and the `n + 1`-simplex
of `Δ[1]` taking the value `0` exactly `i + 1` times. -/
lemma toSimplicialObjectHomotopy_h_apply (H : SSet.Homotopy f g) {n : ℕ} (i : Fin (n + 1))
    (x : X _⦋n⦌) :
    H.toSimplicialObjectHomotopy.h i x =
      H.h.app (op ⦋n + 1⦌) ⟨X.map (SimplexCategory.σ i).op x,
        stdSimplex.objMk₁ i.succ.castSucc⟩ := rfl

/-- Simplicial homotopies which fit into a commutative square induce compatible families of
morphisms `Xₙ ⟶ Y'ₙ₊₁`. -/
lemma toSimplicialObjectHomotopy_h_comm (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (hu : u ▷ Δ[1] ≫ H'.h = H.h ≫ v) (n : ℕ) (i : Fin (n + 1)) :
    u.app (op ⦋n⦌) ≫ H'.toSimplicialObjectHomotopy.h i =
      H.toSimplicialObjectHomotopy.h i ≫ v.app (op ⦋n + 1⦌) := by
  ext x
  simp only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply,
    toSimplicialObjectHomotopy_h_apply, ← NatTrans.naturality_apply u]
  exact congr(($hu).app _ ⟨X.map (SimplexCategory.σ i).op x, stdSimplex.objMk₁ i.succ.castSucc⟩)

/-- The value of the homotopy at a pair whose second component is constant at `0` after
reindexing is the value of `f`. -/
private lemma map_h_app_eq_app (H : SSet.Homotopy f g) {m : SimplexCategoryᵒᵖ} {n : ℕ}
    (φ : m ⟶ op ⦋n⦌) (x : X.obj m) (b : (Δ[1] : SSet.{w}).obj m) (y : X _⦋n⦌)
    (hx : X.map φ x = y) (hb : (Δ[1] : SSet.{w}).map φ b = (ι₀.app _ y).2) :
    Y.map φ (H.h.app m ⟨x, b⟩) = f.app _ y := by
  have e : ((X ⊗ Δ[1]).map φ ⟨x, b⟩ : X _⦋n⦌ × (Δ[1] : SSet.{w}) _⦋n⦌) = ι₀.app _ y :=
    Prod.ext hx hb
  exact (NatTrans.naturality_apply H.h φ _).symm.trans
    ((congrArg (H.h.app _) e).trans congr($(H.h₀).app _ y))

/-- The combinatorial homotopy starts at `f`: the initial vertex of `h i x` is the image under `f`
of the initial vertex of `x`. -/
lemma map_const_toSimplicialObjectHomotopy_h (H : SSet.Homotopy f g) {n : ℕ} (i : Fin (n + 1))
    (x : X _⦋n⦌) :
    Y.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op (H.toSimplicialObjectHomotopy.h i x) =
      f.app _ (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply]
  refine map_h_app_eq_app H _ _ _ _ ?_ ?_
  · rw [← Functor.map_comp_apply, ← op_comp, SimplexCategory.const_comp]
    rfl
  · ext k : 1
    exact stdSimplex.objMk₁_of_castSucc_lt.{w} i.succ.castSucc (0 : Fin (n + 2)) (by simp)

/-- For `i ≥ 1`, the first edge of `h i x` is the image under `f` of the first edge of `x`. -/
lemma map_mkOfLe_toSimplicialObjectHomotopy_h_succ (H : SSet.Homotopy f g) {n : ℕ}
    (j : Fin (n + 1)) (x : X _⦋n + 1⦌) :
    Y.map (SimplexCategory.mkOfLe 0 1 (by simp)).op (H.toSimplicialObjectHomotopy.h j.succ x) =
      f.app _ (X.map (SimplexCategory.mkOfLe 0 1 (by simp)).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply]
  refine map_h_app_eq_app H _ _ _ _ ?_ ?_
  · rw [← Functor.map_comp_apply, ← op_comp]
    refine congrArg (fun φ : ⦋1⦌ ⟶ _ ↦ X.map φ.op x)
      (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k ↦ ?_)))
    fin_cases k <;> rfl
  · ext k : 1
    fin_cases k
    · exact stdSimplex.objMk₁_of_castSucc_lt.{w} j.succ.succ.castSucc 0 (by simp)
    · exact stdSimplex.objMk₁_of_castSucc_lt.{w} j.succ.succ.castSucc 1 (by
        rw [Fin.lt_def]; simp)

/-- The first edge of `h 0 x` is the track of the homotopy at the initial vertex of `x`. -/
lemma map_mkOfLe_toSimplicialObjectHomotopy_h_zero (H : SSet.Homotopy f g) {n : ℕ}
    (x : X _⦋n⦌) :
    Y.map (SimplexCategory.mkOfLe 0 1 (by simp)).op (H.toSimplicialObjectHomotopy.h 0 x) =
      H.toSimplicialObjectHomotopy.h 0 (X.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0).op x) := by
  rw [toSimplicialObjectHomotopy_h_apply, toSimplicialObjectHomotopy_h_apply]
  refine (NatTrans.naturality_apply H.h _ _).symm.trans (congrArg (H.h.app _) ?_)
  refine Prod.ext (α := X _⦋1⦌) (β := (Δ[1] : SSet.{w}) _⦋1⦌) ?_ ?_
  · -- The first components of the two pairs, both iterated reindexings of `x`.
    refine (prod_map_fst X Δ[1] _ _).trans ?_
    rw [← Functor.map_comp_apply, ← op_comp, ← Functor.map_comp_apply, ← op_comp]
    refine congrArg (fun φ : ⦋1⦌ ⟶ _ ↦ X.map φ.op x)
      (SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k ↦ ?_)))
    fin_cases k <;> rfl
  · ext k : 1
    fin_cases k <;> rfl

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
