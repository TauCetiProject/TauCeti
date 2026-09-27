/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ShortComplex.Limit
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.Additivity
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Additivity of singular cochains and singular cohomology

The singular chains of a disjoint union form the coproduct of the singular chains of its
summands. Applying the contravariant functor `Hom(-, M)` therefore identifies the singular
cochain complex of the disjoint union with the product of the cochain complexes of the summands.

Products of modules are exact, so taking cohomology preserves this product. Consequently the
singular cohomology of a disjoint union is the product of the singular cohomologies of its
summands. Both universal properties use the maps induced by the canonical inclusions into the
disjoint union.

## Main results

* `TauCeti.isLimitFanSingularCochainComplex`: singular cochains take a disjoint union to a
  product of cochain complexes.
* `TauCeti.isLimitFanSingularCohomology`: singular cohomology takes a disjoint union to a product
  in every degree.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter I, Section 3.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopCat

universe v u

namespace TauCeti

variable {ι : Type v} (X : ι → TopCat.{v})
  (C : Type u) [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] (R : C)
  (k : Type v) [Ring k] [Linear k C] (M : C)

/-- **Additivity of singular cochains.** The singular cochain complex of a disjoint union is the
product of the singular cochain complexes of its summands. The projections are the cochain maps
induced by the canonical inclusions of the summands. -/
def isLimitFanSingularCochainComplex :
    IsLimit (Fan.mk ((TopCat.of (Σ i, X i)).singularCochainComplex R k M)
      (fun i ↦ TopCat.singularCochainComplexMap (sigmaι X i)) :
      Fan fun i ↦ (X i).singularCochainComplex R k M) := by
  let _ : PreservesLimitsOfShape (Discrete ι)ᵒᵖ ((linearYoneda k C).obj M) := by
    let _ : PreservesLimitsOfShape (Discrete ι)ᵒᵖ
        ((linearYoneda k C).obj M ⋙ forget (ModuleCat k)) := by
      change PreservesLimitsOfShape (Discrete ι)ᵒᵖ (yoneda.obj M)
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves _ (forget (ModuleCat k))
  let _ : HasColimitsOfShape (Discrete ι) C := inferInstance
  let _ : PreservesColimitsOfShape (Discrete ι) ((linearYoneda k C).obj M).rightOp :=
    preservesColimitsOfShape_rightOp _ _
  let _ : PreservesColimitsOfShape (Discrete ι)
      (((linearYoneda k C).obj M).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)) :=
    inferInstance
  let _ : PreservesLimitsOfShape (Discrete ι)
      (((linearYoneda k C).obj M).rightOp.mapHomologicalComplex (ComplexShape.down ℕ)).op :=
    preservesLimitsOfShape_op _ _
  let _ : PreservesLimitsOfShape (Discrete ι)
      (HomologicalComplex.unopFunctor (ModuleCat k) (ComplexShape.down ℕ)) := inferInstance
  let _ : PreservesLimitsOfShape (Discrete ι)
      (ChainComplex.linearYonedaFunctor (α := ℕ) k M) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ι)
      ((((linearYoneda k C).obj M).rightOp.mapHomologicalComplex _).op ⋙
        HomologicalComplex.unopFunctor _ _))
  exact isLimitFanMkObjOfIsLimit (ChainComplex.linearYonedaFunctor (α := ℕ) k M) _ _
    (Cofan.IsColimit.op (isColimitCofanSingularChainComplex X C R))

/-- **Additivity of singular cohomology.** In every degree, the singular cohomology of a
disjoint union is the product of the singular cohomologies of its summands. The projections are
the maps on cohomology induced by the canonical inclusions of the summands. -/
def isLimitFanSingularCohomology (n : ℕ) :
    IsLimit (Fan.mk ((TopCat.of (Σ i, X i)).singularCohomology R k M n)
      (fun i ↦ TopCat.singularCohomologyMap (sigmaι X i) n) :
      Fan fun i ↦ (X i).singularCohomology R k M n) :=
  isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor
    (ModuleCat.{v} k) (ComplexShape.up ℕ) n) _ _
      (isLimitFanSingularCochainComplex X C R k M)

end TauCeti
