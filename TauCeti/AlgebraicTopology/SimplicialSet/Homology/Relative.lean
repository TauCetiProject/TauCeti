/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative

/-!
# Naturality of the quotient map onto relative chains

The relative chain complex of a pair of simplicial sets is the degreewise cokernel of the chains
of the subcomplex, and the quotient map onto it is a morphism of functors.  This file records the
resulting naturality square in the form that is convenient for a fixed morphism of pairs.
-/

@[expose] public section

open CategoryTheory Limits

universe w v u

namespace SSetPair

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The quotient map onto the relative chain complex is natural in the pair. -/
@[reassoc]
lemma chainComplexπ_naturality {P P' : SSetPair.{w}} (f : P ⟶ P') (R : C) :
    P.chainComplexπ R ≫ SSetPair.chainComplexMap f R =
      SSet.chainComplexMap f.right R ≫ P'.chainComplexπ R :=
  (((chainComplexFunctorπ C).app R).naturality f).symm

end SSetPair
