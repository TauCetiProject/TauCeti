/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Module.Projective
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Simplicial chains with varying coefficients

This file records how the coproduct inclusion associated to a simplex behaves under a morphism
of coefficient objects, and how the degreewise components of the chain maps induced by maps of
simplicial sets compose with each other and with changes of coefficients.  It also records that
simplicial chain modules with semisimple coefficients are semisimple, and those with projective
coefficients are projective.
-/

public section

noncomputable section

open CategoryTheory Limits

open scoped Simplicial

universe w v u

namespace TauCeti.SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  {X : _root_.SSet.{w}} {R R' : C}

/-- Mapping the coefficient object of simplicial chains applies the coefficient morphism before
the coproduct inclusion associated to each simplex. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_chainComplexFunctor_map_app_f (f : R ⟶ R') {n : ℕ} (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (((_root_.SSet.chainComplexFunctor C).map f).app X).f n =
      f ≫ X.ιChainComplex x := by
  dsimp [_root_.SSet.chainComplexFunctor, _root_.SSet.ιChainComplex,
    _root_.SSet.chainComplex]
  simp

/-- The degreewise components of the chain maps induced by maps of simplicial sets compose like
the maps themselves. -/
@[reassoc]
lemma chainComplexMap_f_comp {X Y Z : _root_.SSet.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (R : C) (n : ℕ) :
    (_root_.SSet.chainComplexMap f R).f n ≫ (_root_.SSet.chainComplexMap g R).f n =
      (_root_.SSet.chainComplexMap (f ≫ g) R).f n := by
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp]

/-- The chain maps induced by maps of simplicial sets commute, degreewise, with changes of
coefficients. -/
@[reassoc]
lemma chainComplexMap_f_chainComplexFunctor_map_app_f {X Y : _root_.SSet.{w}} (f : X ⟶ Y)
    (u : R ⟶ R') (n : ℕ) :
    (_root_.SSet.chainComplexMap f R).f n ≫
        (((_root_.SSet.chainComplexFunctor C).map u).app Y).f n =
      (((_root_.SSet.chainComplexFunctor C).map u).app X).f n ≫
        (_root_.SSet.chainComplexMap f R').f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, NatTrans.naturality]

end TauCeti.SSet

namespace SSet

/-- The simplicial chain modules `Cₙ(X; M) = ⨁ M` with semisimple coefficients `M` are
semisimple. -/
instance isSemisimpleModule_chainComplex_X {k : Type w} [Ring k] (X : SSet.{w})
    (M : ModuleCat.{w} k) [IsSemisimpleModule k M] (n : ℕ) :
    IsSemisimpleModule k ((X.chainComplex M).X n) := by
  classical
  -- `Cₙ(X; M)` is by definition the coproduct of copies of `M` indexed by the `n`-simplices.
  exact .congr ((ModuleCat.coprodIsoDirectSum fun _ : X _⦋n⦌ ↦ M).toLinearEquiv.trans
    (finsuppLequivDFinsupp k).symm)

/-- The simplicial chain modules `Cₙ(X; M) = ⨁ M` with projective coefficients `M` are
projective. -/
instance projective_chainComplex_X {k : Type w} [Ring k] (X : SSet.{w})
    (M : ModuleCat.{w} k) [Module.Projective k M] (n : ℕ) :
    Module.Projective k ((X.chainComplex M).X n) := by
  classical
  -- `Cₙ(X; M)` is by definition the coproduct of copies of `M` indexed by the `n`-simplices.
  exact .of_equiv' (ModuleCat.coprodIsoDirectSum fun _ : X _⦋n⦌ ↦ M).toLinearEquiv.symm

end SSet
