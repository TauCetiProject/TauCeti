/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Classes of `1`-simplices with equal faces

A `1`-simplex of a simplicial set whose two faces agree is a `1`-cycle of its chain complex, and
so has a class `TauCeti.SSet.ιHomology₁` in first simplicial homology with coefficients in `R`.
This is the analogue in degree one of the vertex classes
`TauCeti.SSet.ιHomology₀` in degree zero.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial

universe w v u

namespace TauCeti.SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

/-- The homology class of a `1`-simplex whose two faces agree, a `1`-cycle. -/
def ιHomology₁ (X : _root_.SSet.{w}) (s : X _⦋1⦌) (h : X.δ 0 s = X.δ 1 s) :
    R ⟶ X.homology R 1 :=
  (X.chainComplex R).liftCycles (X.ιChainComplex s) 0 (by simp) (by
    rw [_root_.SSet.ιChainComplex_d, Fin.sum_univ_two, h]
    simp) ≫ (X.chainComplex R).homologyπ 1

/-- The class of a `1`-simplex with equal faces is the homology class of the cycle it defines. -/
lemma ιHomology₁_eq (X : _root_.SSet.{w}) (s : X _⦋1⦌) (h : X.δ 0 s = X.δ 1 s) :
    ιHomology₁ R X s h = (X.chainComplex R).liftCycles (X.ιChainComplex s) 0 (by simp) (by
      rw [_root_.SSet.ιChainComplex_d, Fin.sum_univ_two, h]
      simp) ≫ (X.chainComplex R).homologyπ 1 := by
  rw [ιHomology₁]

end TauCeti.SSet
