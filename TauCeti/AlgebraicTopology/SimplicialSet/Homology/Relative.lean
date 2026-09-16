/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# Naturality of the long exact sequence of a pair of simplicial sets

For a pair of simplicial sets `P`, given by a monomorphism `X ⟶ Y`, Mathlib constructs the short
exact sequence of chain complexes `0 ⟶ C(X) ⟶ C(Y) ⟶ C(Y, X) ⟶ 0` and the connecting morphism
`Hₙ(Y, X) ⟶ Hₘ(X)` for `m + 1 = n`.  This file shows that a morphism of pairs induces a morphism
of these short exact sequences, and deduces that the connecting morphism is natural, so that it
forms a natural transformation `SSetPair.homologyδNatTrans`.

The source is Eilenberg--Steenrod, *Foundations of Algebraic Topology*, Chapters I--III.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe w

namespace SSetPair

variable {C : Type*} [Category* C] [HasCoproducts.{w} C] [Preadditive C]

/-- The morphism of chain complex sequences `C(X) ⟶ C(Y) ⟶ C(Y, X)` induced by a morphism of
pairs of simplicial sets. -/
@[simps]
noncomputable def chainComplexShortComplexMap {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C) :
    P.chainComplexShortComplex R ⟶ P'.chainComplexShortComplex R where
  τ₁ := SSet.chainComplexMap f.left R
  τ₂ := SSet.chainComplexMap f.right R
  τ₃ := chainComplexMap f R
  comm₁₂ := ((chainComplexFunctorLeftToRight C).app R).naturality f
  comm₂₃ := ((chainComplexFunctorπ C).app R).naturality f

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
@[simps]
noncomputable def homologyδNatTrans (R : A) (n m : ℕ) (h : m + 1 = n := by lia) :
    SSetPair.homologyFunctor.{w} R n ⟶
      (SSetPair.forget ⋙ Arrow.leftFunc) ⋙ SSet.homologyFunctor R m where
  app P := P.homologyδ R n m h
  naturality _ _ f := (homologyδ_naturality f R n m h).symm

end SSetPair
