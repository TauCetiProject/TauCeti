/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# The simplicial chain complex preserves colimits

In degree `n` the chain complex of a simplicial set `X` with coefficients in an object `R` is the
coproduct of copies of `R` indexed by the `n`-simplices of `X`.  Evaluating a simplicial set in a
fixed degree preserves colimits, because colimits of presheaves are computed pointwise, and
forming a coproduct of copies of `R` preserves colimits; hence so does `X ↦ X.chainComplex R`.

The case of a coproduct is chain-level additivity: the chain complex of a disjoint union of
simplicial sets is the coproduct of the chain complexes of the summands.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

open scoped Simplicial

universe w v u v' u'

namespace TauCeti

variable (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C] (R : C)

/-- In degree `n`, the simplicial chain complex with coefficients in `R` is the coproduct of
copies of `R` indexed by the `n`-simplices, naturally in the simplicial set.  This is the
functorial form of `SSet.isColimitChainComplexXCofan`; the two functors agree by construction,
so the isomorphism is the identity. -/
def sSetChainComplexFunctorCompEvalIso (n : ℕ) :
    (SSet.chainComplexFunctor.{w} C).obj R ⋙ HomologicalComplex.eval C _ n ≅
      (evaluation _ _).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R :=
  Iso.refl _

variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J (Type w)]

instance : PreservesColimitsOfShape J ((SSet.chainComplexFunctor.{w} C).obj R) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦ by
    have : PreservesColimitsOfShape J
        ((evaluation SimplexCategoryᵒᵖ (Type w)).obj (Opposite.op ⦋n⦌) ⋙ sigmaConst.obj R) :=
      comp_preservesColimitsOfShape _ _
    exact preservesColimitsOfShape_of_natIso
      (sSetChainComplexFunctorCompEvalIso C R n).symm

end TauCeti
