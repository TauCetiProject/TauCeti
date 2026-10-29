/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Exactness of simplicial chains in the coefficients

Simplicial chains send a short exact sequence of coefficients to a short exact sequence of chain
complexes whenever coproducts in the coefficient category are exact. The construction is Mathlib's
`SSet.chainComplexFunctor`, whose degree-n object is a coproduct of coefficient objects over
the n-simplices. Applying the homology long
exact sequence gives the coefficient connecting homomorphisms, including Bockstein maps.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.A, change of coefficients.
-/

public noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe w v u

namespace CategoryTheory.ShortComplex.ShortExact

/-- Simplicial chains preserve short exact coefficient sequences when coproducts are exact. -/
lemma map_simplicialChains {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] [AB4OfSize.{w} C] {S : ShortComplex C}
    (hS : S.ShortExact) (X : SSet.{w}) :
    (S.map ((SSet.chainComplexFunctor C).flip.obj X)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let F : C ⥤ C := Functor.const (Discrete (X _⦋n⦌)) ⋙ colim
  -- In degree n the chain functor is the coproduct of the constant coefficient diagram.
  convert hS.map_of_exact F using 1
  rfl

end CategoryTheory.ShortComplex.ShortExact
