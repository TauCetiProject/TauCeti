/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic
public import TauCeti.AlgebraicTopology.Singular.Additivity

/-!
# Additivity of singular chains with local coefficients

For a local coefficient system on a disjoint union, twisted singular chains are the coproduct
of the chains of the summands with the restricted systems. The coproduct inclusions are the
chain maps induced by the inclusions of spaces. The degreewise decomposition is compatible
with the differentials, including the coefficient transport on the first face.

A singular simplex of a disjoint union lies in exactly one summand. Reindexing the coproduct
of its coefficient fibres therefore identifies it with an iterated coproduct over summands
and their singular simplices. This chain decomposition also gives the product decomposition
of cochains with local coefficients after applying `Hom(-, M)`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.1 and 3.H.

The simplex decomposition is `TauCeti.toSSet_map_sigmaι_app_bijective`. The construction uses
Mathlib's `sigmaSigmaIso` and `Sigma.whiskerEquiv` to reindex coproducts, and follows the
ordinary additivity construction in `TauCeti.AlgebraicTopology.Singular.Additivity`.
-/

public section

noncomputable section

open CategoryTheory Limits TopCat
open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {ι : Type v} (X : ι → TopCat.{v})
  (L : LocalCoefficientSystem.{u, v, max v w} R (TopCat.of (Σ i, X i)))

/-- Twisted singular chains of a disjoint union are the coproduct of the twisted chains of
its summands, with coefficient systems pulled back along the summand inclusions. -/
def isColimitCofanTwistedChainComplex :
    IsColimit (Cofan.mk L.twistedChainComplex
      (fun i ↦ twistedChainComplexMap (sigmaι X i) L) :
      Cofan fun i ↦ ((pullback (sigmaι X i).hom).obj L).twistedChainComplex) := by
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact (isColimitMapCoconeCofanMkEquiv
    (HomologicalComplex.eval (ModuleCat.{max v w} R) (ComplexShape.down ℕ) n) _ _).symm
      (isColimitCofanTwistedChainComplexXOfBijective X (sigmaι X) L n
        (toSSet_map_sigmaι_app_bijective X (Opposite.op ⦋n⦌)))

end TauCeti.LocalCoefficientSystem
