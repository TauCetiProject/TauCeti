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

Whenever `ι`-indexed products of the coefficient modules are exact, taking cohomology preserves
this product. Consequently the singular cohomology of a disjoint union is the product of the
singular cohomologies of its summands. Products of modules over a ring are always exact, so for a
`v`-small index type and a coefficient ring in universe `v` the exactness hypothesis is supplied by
Mathlib's AB4* instance. Both universal properties use the maps induced by the canonical inclusions
into the disjoint union.

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
modules exact, which discharges the exactness hypothesis in the same-universe case, by Dagur
Asgeirsson in `Mathlib/Algebra/Category/ModuleCat/AB`.
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
      Fan fun i ↦ (X i).singularCochainComplex R k M) := by
  let _ : PreservesLimitsOfShape (Discrete ι)ᵒᵖ ((linearYoneda k C).obj M) := by
    -- Forgetting the `k`-module structure turns `Hom(-, M)` into the ordinary hom functor
    -- `yoneda.obj M`, which takes coproducts in `C` to products of types.
    have hforget : (linearYoneda k C).obj M ⋙ forget (ModuleCat.{v} k) = yoneda.obj M :=
      Functor.congr_obj (whiskering_linearYoneda k C) M
    let _ : PreservesLimitsOfShape (Discrete (Shrink.{v} ι))ᵒᵖ
        ((linearYoneda k C).obj M ⋙ forget (ModuleCat.{v} k)) :=
      hforget ▸ inferInstance
    -- `forget (ModuleCat.{v} k)` reflects limits only of `v`-small shape, so the reflection step
    -- runs over a `v`-small copy of `ι` and is transported back along the induced equivalence.
    let _ : PreservesLimitsOfShape (Discrete (Shrink.{v} ι))ᵒᵖ ((linearYoneda k C).obj M) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ (forget (ModuleCat.{v} k))
    exact preservesLimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{v} ι)).symm.op _
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
      (HomologicalComplex.unopFunctor (ModuleCat.{v} k) (ComplexShape.down ℕ)) := inferInstance
  let _ : PreservesLimitsOfShape (Discrete ι)
      (ChainComplex.linearYonedaFunctor (α := ℕ) k M) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ι)
      ((((linearYoneda k C).obj M).rightOp.mapHomologicalComplex _).op ⋙
        HomologicalComplex.unopFunctor _ _))
  exact isLimitFanMkObjOfIsLimit (ChainComplex.linearYonedaFunctor (α := ℕ) k M) _ _
    (Cofan.IsColimit.op (isColimitCofanSingularChainComplex X C R))

section Cohomology

variable [HasLimitsOfShape (Discrete ι) (ModuleCat.{v} k)]
  [HasExactLimitsOfShape (Discrete ι) (ModuleCat.{v} k)]

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

end Cohomology

end TauCeti
