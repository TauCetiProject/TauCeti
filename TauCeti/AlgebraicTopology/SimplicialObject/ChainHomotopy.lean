/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import TauCeti.AlgebraicTopology.SimplicialObject.Homotopy

/-!
# Naturality, vanishing, and homotopy equivalences for chain homotopies of simplicial objects

A simplicial homotopy `H` between morphisms of simplicial objects in a preadditive category
induces a chain homotopy `H.toChainHomotopy` between the induced morphisms of alternating face
map complexes. Its degree `n` component is, up to sign, the alternating sum of the maps `H.h i`.
This file records two consequences of that formula, checked one degree at a time, and upgrades
combinatorial simplicial homotopy equivalences to chain homotopy equivalences:

* `toChainHomotopy_hom_comm`: if the families of two simplicial homotopies commute with a pair
  of morphisms of simplicial objects, then the induced chain homotopy components commute with
  the induced chain maps;
* `comp_toChainHomotopy_hom_comp_eq_zero`: if every map `H.h i` vanishes after pre- and
  post-composition with fixed morphisms, then so does the induced chain homotopy component.
  The morphisms are arbitrary, so the target may be, for instance, a relative quotient complex
  that carries no simplicial structure;
* `CategoryTheory.SimplicialObject.HomotopyEquiv.toChainHomotopyEquiv`: a combinatorial simplicial
  homotopy equivalence induces a chain homotopy equivalence (and, when homology exists, a
  quasi-isomorphism) on alternating face map complexes.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject.Homotopy

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {X Y X' Y' : SimplicialObject C} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}

/-- If the families of two simplicial homotopies commute in degree `p` with a pair of morphisms
of simplicial objects, the induced chain homotopy components from degree `p` commute with the
induced chain maps. -/
lemma toChainHomotopy_hom_comm (H : Homotopy f g) (H' : Homotopy f' g') (u : X ⟶ X') (v : Y ⟶ Y')
    (p q : ℕ)
    (hu : ∀ i : Fin (p + 1), u.app (op ⦋p⦌) ≫ H'.h i = H.h i ≫ v.app (op ⦋p + 1⦌)) :
    ((alternatingFaceMapComplex C).map u).f p ≫ H'.toChainHomotopy.hom p q =
      H.toChainHomotopy.hom p q ≫ ((alternatingFaceMapComplex C).map v).f q := by
  rcases eq_or_ne (p + 1) q with rfl | h
  · simp [toChainHomotopy, Preadditive.comp_sum, Preadditive.sum_comp, hu]
  · simp [toChainHomotopy, h]

/-- If every simplicial homotopy term vanishes between two morphisms, so does the induced chain
homotopy component. The morphisms need only exist in these degrees, so the target may be a
relative quotient without a simplicial structure. -/
lemma comp_toChainHomotopy_hom_comp_eq_zero (H : Homotopy f g) (n : ℕ) {A B : C}
    (a : A ⟶ X.obj (op ⦋n⦌)) (b : Y.obj (op ⦋n + 1⦌) ⟶ B)
    (h : ∀ i : Fin (n + 1), a ≫ H.h i ≫ b = 0) :
    a ≫ H.toChainHomotopy.hom n (n + 1) ≫ b = 0 := by
  simp [toChainHomotopy, Preadditive.comp_sum, Preadditive.sum_comp, h]

end CategoryTheory.SimplicialObject.Homotopy

end

public noncomputable section

open CategoryTheory AlgebraicTopology

universe v u

namespace CategoryTheory.SimplicialObject.HomotopyEquiv

variable {C : Type u} [Category.{v} C] [Preadditive C] {X Y : SimplicialObject C}

/-- A combinatorial simplicial homotopy equivalence induces a chain homotopy equivalence between
the alternating face map complexes. -/
def toChainHomotopyEquiv (e : HomotopyEquiv X Y) :
    _root_.HomotopyEquiv
      ((alternatingFaceMapComplex C).obj X) ((alternatingFaceMapComplex C).obj Y) where
  hom := (alternatingFaceMapComplex C).map e.hom
  inv := (alternatingFaceMapComplex C).map e.inv
  homotopyHomInvId :=
    (_root_.Homotopy.ofEq (((alternatingFaceMapComplex C).map_comp e.hom e.inv).symm)).trans <|
      e.homotopyHomInvId.toChainHomotopy.trans <|
        _root_.Homotopy.ofEq ((alternatingFaceMapComplex C).map_id X)
  homotopyInvHomId :=
    (_root_.Homotopy.ofEq (((alternatingFaceMapComplex C).map_comp e.inv e.hom).symm)).trans <|
      e.homotopyInvHomId.toChainHomotopy.trans <|
        _root_.Homotopy.ofEq ((alternatingFaceMapComplex C).map_id Y)

@[simp]
lemma toChainHomotopyEquiv_hom (e : HomotopyEquiv X Y) :
    e.toChainHomotopyEquiv.hom = (alternatingFaceMapComplex C).map e.hom :=
  (rfl)

@[simp]
lemma toChainHomotopyEquiv_inv (e : HomotopyEquiv X Y) :
    e.toChainHomotopyEquiv.inv = (alternatingFaceMapComplex C).map e.inv :=
  (rfl)

/-- The forward map of a combinatorial simplicial homotopy equivalence induces a chain homotopy
equivalence on alternating face map complexes. -/
lemma homotopyEquivalences_alternatingFaceMapComplex_map (e : HomotopyEquiv X Y) :
    HomologicalComplex.homotopyEquivalences C (.down ℕ)
      ((alternatingFaceMapComplex C).map e.hom) :=
  ⟨e.toChainHomotopyEquiv, rfl⟩

/-- When `C` has homology, the forward map of a combinatorial simplicial homotopy equivalence
induces a quasi-isomorphism on alternating face map complexes. -/
lemma quasiIso_alternatingFaceMapComplex_map [CategoryWithHomology C] (e : HomotopyEquiv X Y) :
    QuasiIso ((alternatingFaceMapComplex C).map e.hom) := by
  rw [← e.toChainHomotopyEquiv_hom]
  infer_instance

/-- When `C` has homology, the backward map of a combinatorial simplicial homotopy equivalence
induces a quasi-isomorphism on alternating face map complexes. -/
lemma quasiIso_alternatingFaceMapComplex_map_inv [CategoryWithHomology C]
    (e : HomotopyEquiv X Y) :
    QuasiIso ((alternatingFaceMapComplex C).map e.inv) := by
  rw [← e.symm_hom]
  exact e.symm.quasiIso_alternatingFaceMapComplex_map

end CategoryTheory.SimplicialObject.HomotopyEquiv

end
