/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.Algebra.Homology.ShortComplex.Limit
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Cohomology.Relative
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Additivity of relative singular cohomology

For a family of pairs `(Xᵢ, Aᵢ)`, the relative singular cochains of their disjoint union form
the product of their relative cochain complexes. In every degree this induces the product
decomposition of relative singular cohomology. Both universal properties use restriction
along the inclusions of the pairs as their projections, and apply to arbitrary small families,
including the empty family.

Relative chains already take disjoint unions to coproducts. Applying `Hom(-, M)` changes that
coproduct to a product, and exactness of products of modules allows passage to cohomology.
No exactness hypothesis on coproducts in the chain coefficient category is needed.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter I, Section 3.

The formal inputs are `TopPair.isColimitCofanSingularChainComplex`, the contravariant
`TauCeti.ChainComplex.linearYonedaFunctor`, and the limit-preservation theorem for homology in
`TauCeti.Algebra.Homology.ShortComplex.Limit`.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace TauCeti

namespace TopPair

variable {ι : Type w} (P : ι → TopPair.{w})
  (C : Type u) [Category.{v} C] [Small.{v} ι] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- **Additivity of relative singular cochains.** The relative cochains of a disjoint union
of pairs are the product of the relative cochains of the pairs, with restriction along the
inclusions as projections. -/
def isLimitFanSingularCochainComplex :
    IsLimit (Fan.mk ((TopPair.sigma P).singularCochainComplex R k M)
      (fun i ↦ TopPair.singularCochainComplexMap (TopPair.sigmaι P i)) :
      Fan fun i ↦ (P i).singularCochainComplex R k M) :=
  isLimitFanMkObjOfIsLimit (ChainComplex.linearYonedaFunctor (α := ℕ) k M) _ _
    (Cofan.IsColimit.op (TopPair.isColimitCofanSingularChainComplex P C R))

/-- **Additivity of relative singular cohomology.** In every degree the relative cohomology
of a disjoint union of pairs is the product of the relative cohomologies of the pairs. The
projections are induced by the inclusions of the pairs. -/
def isLimitFanSingularCohomology (n : ℕ) :
    IsLimit (Fan.mk ((TopPair.sigma P).singularCohomology R k M n)
      (fun i ↦ TopPair.singularCohomologyMap (TopPair.sigmaι P i) n) :
      Fan fun i ↦ (P i).singularCohomology R k M n) := by
  have : HasLimitsOfShape (Discrete ι) (ModuleCat.{v} k) := ModuleCat.hasLimitsOfShape
  exact isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor
    (ModuleCat.{v} k) (ComplexShape.up ℕ) n) _ _
      (isLimitFanSingularCochainComplex P C R k M)

end TopPair

end TauCeti
