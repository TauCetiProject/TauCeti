/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# Naturality in relative simplicial homology

For a pair of simplicial sets `P`, given by a monomorphism `X ⟶ Y`, Mathlib constructs the short
exact sequence of chain complexes `0 ⟶ C(X) ⟶ C(Y) ⟶ C(Y, X) ⟶ 0` and the connecting morphism
`Hₙ(Y, X) ⟶ Hₘ(X)` for `m + 1 = n`.  This file shows that a morphism of pairs induces a morphism
of these short exact sequences, and deduces that the connecting morphism is natural, so that it
forms a natural transformation `SSetPair.homologyδNatTrans`.

It also records that the quotient maps from ambient to relative chains and homology are natural in
the pair: they commute with morphisms of simplicial-set pairs. The chain-level statement restates
the naturality that Mathlib's `SSetPair.chainComplexFunctorπ` expresses functorially.

The source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w

namespace SSetPair

variable {C : Type*} [Category* C] [HasCoproducts.{w} C] [Preadditive C]

/-- The quotient map onto the relative chain complex is natural in the pair. -/
@[reassoc]
lemma chainComplexπ_naturality {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C) :
    P.chainComplexπ R ≫ SSetPair.chainComplexMap f R =
      SSet.chainComplexMap f.right R ≫ P'.chainComplexπ R :=
  (((chainComplexFunctorπ C).app R).naturality f).symm

/-- The morphism of chain complex sequences `C(X) ⟶ C(Y) ⟶ C(Y, X)` induced by a morphism of
pairs of simplicial sets. -/
noncomputable def chainComplexShortComplexMap {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C) :
    P.chainComplexShortComplex R ⟶ P'.chainComplexShortComplex R where
  τ₁ := SSet.chainComplexMap f.left R
  τ₂ := SSet.chainComplexMap f.right R
  τ₃ := chainComplexMap f R
  comm₁₂ := ((chainComplexFunctorLeftToRight C).app R).naturality f
  comm₂₃ := (chainComplexπ_naturality f R).symm

@[simp]
lemma chainComplexShortComplexMap_τ₁ {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C) :
    (chainComplexShortComplexMap f R).τ₁ = SSet.chainComplexMap f.left R := by
  rw [chainComplexShortComplexMap.eq_def]

@[simp]
lemma chainComplexShortComplexMap_τ₂ {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C) :
    (chainComplexShortComplexMap f R).τ₂ = SSet.chainComplexMap f.right R := by
  rw [chainComplexShortComplexMap.eq_def]

@[simp]
lemma chainComplexShortComplexMap_τ₃ {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C) :
    (chainComplexShortComplexMap f R).τ₃ = chainComplexMap f R := by
  rw [chainComplexShortComplexMap.eq_def]

variable {A : Type*} [Category* A] [HasCoproducts.{w} A] [Abelian A]

/-- The connecting morphism of the long exact sequence of a pair of simplicial sets is natural:
for a morphism of pairs `f : P ⟶ P'`, the square formed by the connecting morphisms
`Hₙ(P) ⟶ Hₘ(P.left)` and `Hₙ(P') ⟶ Hₘ(P'.left)` and the maps induced by `f` commutes. -/
@[reassoc]
lemma homologyδ_naturality {P P' : SSetPair.{w}} (f : P ⟶ P') (R : A) (n m : ℕ)
    (h : m + 1 = n := by lia) :
    P.homologyδ R n m h ≫ SSet.homologyMap f.left R m =
      SSetPair.homologyMap f R n ≫ P'.homologyδ R n m h :=
  HomologicalComplex.HomologySequence.δ_naturality (chainComplexShortComplexMap f R)
    (P.shortExact_chainComplexShortComplex R) (P'.shortExact_chainComplexShortComplex R) n m
    (by simpa)

/-- The connecting morphism `Hₙ(Y, X) ⟶ Hₘ(X)` of the long exact sequence of a pair of simplicial
sets `X ⟶ Y`, for `m + 1 = n`, as a natural transformation from relative homology to the homology
of the subobject. -/
noncomputable def homologyδNatTrans (R : A) (n m : ℕ) (h : m + 1 = n := by lia) :
    SSetPair.homologyFunctor.{w} R n ⟶
      (SSetPair.forget ⋙ Arrow.leftFunc) ⋙ SSet.homologyFunctor R m where
  app P := P.homologyδ R n m h
  naturality _ _ f := (homologyδ_naturality f R n m h).symm

@[simp]
lemma homologyδNatTrans_app (R : A) (n m : ℕ) (h : m + 1 = n) (P : SSetPair.{w}) :
    (homologyδNatTrans R n m h).app P = P.homologyδ R n m h := by
  rw [homologyδNatTrans.eq_def]

variable {D : Type*} [Category* D] [HasCoproducts.{w} D] [Preadditive D]
  [CategoryWithHomology D]

/-- The quotient maps from ambient to relative simplicial homology are natural in the pair. -/
@[reassoc (attr := simp)]
lemma homologyπ_naturality {P P' : SSetPair.{w}} (f : P ⟶ P') (R : D) (n : ℕ) :
    SSet.homologyMap f.right R n ≫ P'.homologyπ R n =
      P.homologyπ R n ≫ SSetPair.homologyMap f R n := by
  have h : SSet.chainComplexMap f.right R ≫ P'.chainComplexπ R =
      P.chainComplexπ R ≫ SSetPair.chainComplexMap f R :=
    (chainComplexπ_naturality f R).symm
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, h]

end SSetPair
