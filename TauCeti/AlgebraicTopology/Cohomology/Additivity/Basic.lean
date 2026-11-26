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
public import TauCeti.Topology.Category.TopCat.Monoidal
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Additivity of singular cochains and singular cohomology

The singular chains of a disjoint union form the coproduct of the singular chains of its
summands. Applying the contravariant functor `Hom(-, M)` therefore identifies the singular
cochain complex of the disjoint union with the product of the cochain complexes of the summands.

Products of modules over a ring are always exact, so taking cohomology preserves this product:
the singular cohomology of a disjoint union is the product of the singular cohomologies of its
summands. Both universal properties use the maps induced by the canonical inclusions into the
disjoint union. In particular, when `X` is a discrete `Small.{v}` space, the product decomposition
`TopCat.sigmaConstIsoProd` implies that classes in `Hⁿ(X × Y; R, M)` are determined by their
restrictions along the fibre inclusions `TopCat.prodFiberInclusion X Y x`
(`TopCat.singularCohomology_prod_ext_of_discreteTopology`).

The same holds for a union of pairwise disjoint open subsets `s i` of a space, whose singular
chains are the coproduct of those of the `s i` (`TauCeti.isColimitCofanSingularChainComplexOpens`):
its singular cochains and cohomology are the products of those of the `s i`, with the restrictions
as projections, and a class on the union is determined by its restrictions to the `s i`
(`TauCeti.singularCohomology_iSup_ext`).

## Main results

* `TauCeti.isLimitFanSingularCochainComplex`: singular cochains take a disjoint union to a
  product of cochain complexes.
* `TauCeti.isLimitFanSingularCohomology`: singular cohomology takes a disjoint union to a product
  in every degree.
* `TauCeti.isLimitFanSingularCochainComplexOpens`, `TauCeti.isLimitFanSingularCohomologyOpens`:
  the same for a union of pairwise disjoint open sets.
* `TauCeti.singularCohomology_iSup_ext`: a class on such a union is determined by its
  restrictions to the members.
* `TauCeti.singularCohomology_prod_ext_of_discreteTopology`: for a discrete space `X`, a class on
  `X × Y` is determined by its restrictions to the slices `{x} × Y`, since `X × Y` is the disjoint
  union of these slices.

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

variable {ι : Type w} (X : ι → TopCat.{w})
  (C : Type u) [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
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
def isLimitFanSingularCohomology [Small.{v} ι] (n : ℕ) :
    IsLimit (Fan.mk ((TopCat.of (Σ i, X i)).singularCohomology R k M n)
      (fun i ↦ TopCat.singularCohomologyMap (sigmaι X i) n) :
      Fan fun i ↦ (X i).singularCohomology R k M n) :=
  have : HasLimitsOfShape (Discrete ι) (ModuleCat.{v} k) := ModuleCat.hasLimitsOfShape
  isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor
    (ModuleCat.{v} k) (ComplexShape.up ℕ) n) _ _
      (isLimitFanSingularCochainComplex X C R k M)

section Opens

open Function TopologicalSpace

variable {Y : Type w} [TopologicalSpace Y] (s : ι → Opens Y)

/-- **Additivity of singular cochains over disjoint open sets.** The singular cochain complex of a
union of pairwise disjoint open sets `s i` is the product of the singular cochain complexes of the
`s i`. The projections are the cochain maps induced by the inclusions. -/
def isLimitFanSingularCochainComplexOpens (hs : Pairwise (Disjoint on s)) :
    IsLimit (Fan.mk ((TopCat.of ↥(⨆ i, s i)).singularCochainComplex R k M)
      (fun i ↦ TopCat.singularCochainComplexMap
        (ofHom ⟨Opens.inclusion (le_iSup s i), continuous_inclusion _⟩)) :
      Fan fun i ↦ (TopCat.of (s i)).singularCochainComplex R k M) :=
  isLimitFanMkObjOfIsLimit (ChainComplex.linearYonedaFunctor (α := ℕ) k M) _ _
    (Cofan.IsColimit.op (isColimitCofanSingularChainComplexOpens s C R hs))

/-- **Additivity of singular cohomology over disjoint open sets.** In every degree, the singular
cohomology of a union of pairwise disjoint open sets `s i` is the product of the singular
cohomologies of the `s i`. The projections are the restrictions to the `s i`. -/
def isLimitFanSingularCohomologyOpens [Small.{v} ι] (hs : Pairwise (Disjoint on s)) (n : ℕ) :
    IsLimit (Fan.mk ((TopCat.of ↥(⨆ i, s i)).singularCohomology R k M n)
      (fun i ↦ TopCat.singularCohomologyMap
        (ofHom ⟨Opens.inclusion (le_iSup s i), continuous_inclusion _⟩) n) :
      Fan fun i ↦ (TopCat.of (s i)).singularCohomology R k M n) :=
  have : HasLimitsOfShape (Discrete ι) (ModuleCat.{v} k) := ModuleCat.hasLimitsOfShape
  isLimitFanMkObjOfIsLimit (HomologicalComplex.homologyFunctor
    (ModuleCat.{v} k) (ComplexShape.up ℕ) n) _ _
      (isLimitFanSingularCochainComplexOpens C R k M s hs)

variable {s C R k M} in
/-- **Classes on a disjoint union of open sets are determined by their restrictions.** Two classes
of `Hⁿ(⋃ i, s i; R, M)`, for pairwise disjoint open sets `s i`, are equal when their restrictions
to every `s i` are. -/
theorem singularCohomology_iSup_ext [Small.{v} ι] (hs : Pairwise (Disjoint on s)) {n : ℕ}
    {z z' : (TopCat.of ↥(⨆ i, s i)).singularCohomology R k M n}
    (h : ∀ i, TopCat.singularCohomologyMap
      (ofHom ⟨Opens.inclusion (le_iSup s i), continuous_inclusion _⟩) n z =
        TopCat.singularCohomologyMap
          (ofHom ⟨Opens.inclusion (le_iSup s i), continuous_inclusion _⟩) n z') :
    z = z' :=
  have : PreservesLimitsOfShape (Discrete ι) (forget (ModuleCat.{v} k)) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence (equivShrink.{v} ι)).symm _
  Concrete.isLimit_ext _ (isLimitFanSingularCohomologyOpens C R k M s hs n) _ _ fun ⟨i⟩ ↦ h i

end Opens

section Discrete

open MonoidalCategory

variable {C : Type u} [Category.{w} C] [HasCoproducts.{w} C] [Abelian C] {R M : C}
  {k : Type*} [Ring k] [Linear k C]

/-- **Classes on a product with a discrete space are determined on the slices.** For a discrete
space `X`, two classes of `Hⁿ(X × Y; R, M)` whose restrictions to every slice `{x} × Y`, along
`y ↦ (x, y)`, agree are equal: `X × Y` is the disjoint union of these slices. -/
theorem singularCohomology_prod_ext_of_discreteTopology {X Y : TopCat.{w}} [DiscreteTopology X]
    (n : ℕ) {z z' : (X ⊗ Y).singularCohomology R k M n}
    (h : ∀ x : X, TopCat.singularCohomologyMap
      (CartesianMonoidalCategory.lift (TopCat.ofHom (ContinuousMap.const Y x)) (𝟙 Y)) n z =
        TopCat.singularCohomologyMap
          (CartesianMonoidalCategory.lift (TopCat.ofHom (ContinuousMap.const Y x)) (𝟙 Y)) n z') :
    z = z' := by
  let S : X → TopCat.{w} := fun _ ↦ Y
  -- The identity of `X × Y` factors through the disjoint union `Σ x, Y` of the slices.
  let r : TopCat.of (Σ x, S x) ⟶ X ⊗ Y :=
    TopCat.ofHom ⟨fun p ↦ (p.1, p.2), continuous_sigma fun _ ↦ by fun_prop⟩
  let q : X ⊗ Y ⟶ TopCat.of (Σ x, S x) :=
    TopCat.ofHom ⟨fun p ↦ ⟨p.1, p.2⟩,
      continuous_prod_of_discrete_left.2 fun _ ↦ continuous_sigmaMk (σ := fun x ↦ S x)⟩
  -- Both composites below hold by `rfl`: `≫`, `TopCat.ofHom`, `sigmaι` and `lift` all unfold
  -- to the underlying functions, so both sides agree pointwise by definition.
  have hqr : q ≫ r = 𝟙 _ := TopCat.ext fun _ ↦ (rfl)
  have hr : TopCat.singularCohomologyMap r n z = TopCat.singularCohomologyMap r n z' :=
    Concrete.isLimit_ext _ (isLimitFanSingularCohomology S C R k M n) _ _ fun ⟨x⟩ ↦ by
      have hx : sigmaι S x ≫ r =
          CartesianMonoidalCategory.lift (TopCat.ofHom (ContinuousMap.const Y x)) (𝟙 Y) :=
        TopCat.ext fun _ ↦ (rfl)
      simp only [Fan.mk_pt, Fan.mk_π_app, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp, hx]
      exact h x
  calc z = TopCat.singularCohomologyMap (q ≫ r) n z := by
        rw [hqr, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
    _ = TopCat.singularCohomologyMap (q ≫ r) n z' := by
        rw [TopCat.singularCohomologyMap_comp, ConcreteCategory.comp_apply,
          ConcreteCategory.comp_apply, hr]
    _ = z' := by rw [hqr, TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]

end Discrete

end TauCeti

namespace TopCat

open MonoidalCategory CartesianMonoidalCategory

/-- **Fibre-restriction extensionality for a product with a discrete space**: when `X` is a
discrete `Small.{v}` space, classes of `Hⁿ(X × Y; R, M)` are determined by their restrictions along
the fibre inclusions `TopCat.prodFiberInclusion X Y x`. -/
theorem singularCohomology_prod_ext_of_discreteTopology {C : Type u} [Category.{v} C]
    [HasCoproducts.{w} C] [Abelian C] {R : C} {k : Type*} [Ring k] [Linear k C] {M : C}
    (X Y : TopCat.{w}) [DiscreteTopology X] [Small.{v} X] {n : ℕ}
    {φ ψ : (X ⊗ Y).singularCohomology R k M n}
    (h : ∀ x : X, TopCat.singularCohomologyMap (prodFiberInclusion X Y x) n φ =
      TopCat.singularCohomologyMap (prodFiberInclusion X Y x) n ψ) : φ = ψ := by
  have : PreservesLimitsOfShape (Discrete (X : Type w)) (forget (ModuleCat.{v} k)) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence (equivShrink.{v} (X : Type w))).symm _
  let e := sigmaConstIsoProd X Y
  let L := TauCeti.isLimitFanSingularCohomology (fun _ : X ↦ Y) C R k M n
  have heq : TopCat.singularCohomologyMap e.hom n φ = TopCat.singularCohomologyMap e.hom n ψ :=
    Concrete.isLimit_ext _ L _ _ fun ⟨x⟩ ↦ by
      dsimp only [Fan.mk_pt, Fan.mk_π_app]
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← TopCat.singularCohomologyMap_comp, sigmaι_comp_sigmaConstIsoProd_hom]
      exact h x
  have hinv (z : (X ⊗ Y).singularCohomology R k M n) :
      TopCat.singularCohomologyMap e.inv n (TopCat.singularCohomologyMap e.hom n z) = z := by
    rw [← ConcreteCategory.comp_apply, ← TopCat.singularCohomologyMap_comp, Iso.inv_hom_id,
      TopCat.singularCohomologyMap_id, ConcreteCategory.id_apply]
  rw [← hinv φ, ← hinv ψ, heq]

end TopCat
