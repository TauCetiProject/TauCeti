/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Simplicial chains with varying coefficients

This file records how the coproduct inclusion associated to a simplex behaves under a morphism
of coefficient objects.
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

end TauCeti.SSet
