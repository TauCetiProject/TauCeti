/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Limit
public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.Additivity
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Additivity of singular cochains and singular cohomology

The singular chains of a disjoint union form the coproduct of the singular chains of its
summands. Applying the contravariant functor `Hom(-, M)` therefore identifies the singular
cochain complex of the disjoint union with the product of the cochain complexes of the summands.

Products of modules over a ring are always exact, so taking cohomology preserves this product:
the singular cohomology of a disjoint union is the product of the singular cohomologies of its
summands. Both universal properties use the maps induced by the canonical inclusions into the
disjoint union.

## Main results

* `TauCeti.isLimitFanSingularCochainComplex`: singular cochains take a disjoint union to a
  product of cochain complexes.
* `TauCeti.isLimitFanSingularCohomology`: singular cohomology takes a disjoint union to a product
  in every degree.

## Sources

The informal source is S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*,
Chapter I, Section 3.

The coproduct decomposition of the singular chains is
`TauCeti.isColimitCofanSingularChainComplex`, in `TauCeti/AlgebraicTopology/Singular/Additivity`,
and the passage from cochains to cohomology is
`TauCeti.homologicalComplexHomologyFunctor_preservesLimitsOfShape`, in
`TauCeti/Algebra/Homology/ShortComplex/Limit`. The formal inputs from Mathlib are the linear Yoneda
embedding `linearYoneda` and its comparison `whiskering_linearYoneda` with the ordinary Yoneda
embedding, by Kim Morrison in `Mathlib/CategoryTheory/Linear/Yoneda`; the fact that `Hom(-, M)`
takes coproducts to products, by Markus Himmel in
`Mathlib/CategoryTheory/Preadditive/Yoneda/Limits`; the transfer of (co)limit preservation across
opposite categories, by Markus Himmel in `Mathlib/CategoryTheory/Limits/Preserves/Opposites` and by
Kim Morrison and Floris van Doorn in
`Mathlib/CategoryTheory/Limits/Shapes/Opposites/Products`; and the AB4* instance making products of
abelian groups exact, by David Kurniadi Angdinata, Moritz Firsching, Nikolas Kuhn and Amelia
Livingston in `Mathlib/Algebra/Category/Grp/AB`, from which exactness of products of modules is
transferred along the forgetful functor.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopCat

universe w v u

namespace TauCeti

-- `Small.{v} ι` is stated after `Category.{v} C` so that `v` is already determined when it is
-- synthesised; declaring it first makes Lean solve it by `small_self` and collapse `w` into `v`.
variable {ι : Type w} (X : ι → TopCat.{w})
  (C : Type u) [Category.{v} C] [Small.{v} ι] [HasCoproducts.{w} C] [Abelian C] (R : C)
  (k : Type*) [Ring k] [Linear k C] (M : C)

/-- **Additivity of singular cochains.** The singular cochain complex of a disjoint union is the
product of the singular cochain complexes of its summands. The projections are the cochain maps
induced by the canonical inclusions of the summands. -/
def isLimitFanSingularCochainComplex :
    IsLimit (Fan.mk ((TopCat.of (Σ i, X i)).singularCochainComplex R k M)
      (fun i ↦ TopCat.singularCochainComplexMap (sigmaι X i)) :
      Fan fun i ↦ (X i).singularCochainComplex R k M) :=
  isLimitFanMkObjOfIsLimit (ChainComplex.linearYonedaFunctor (α := ℕ) k M) _ _
    (Cofan.IsColimit.op (isColimitCofanSingularChainComplex X C R))

/-- **Additivity of singular cohomology.** In every degree, the singular cohomology of a
disjoint union is the product of the singular cohomologies of its summands. The projections are
the maps on cohomology induced by the canonical inclusions of the summands. -/
def isLimitFanSingularCohomology (n : ℕ) :
    IsLimit (Fan.mk ((TopCat.of (Σ i, X i)).singularCohomology R k M n)
      (fun i ↦ TopCat.singularCohomologyMap (sigmaι X i) n) :
      Fan fun i ↦ (X i).singularCohomology R k M n) :=
  have : HasLimitsOfShape (Discrete ι) (ModuleCat.{v} k) := ModuleCat.hasLimitsOfShape
  isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor
    (ModuleCat.{v} k) (ComplexShape.up ℕ) n) _ _
      (isLimitFanSingularCochainComplex X C R k M)

end TauCeti
