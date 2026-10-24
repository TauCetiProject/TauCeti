/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.Point
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Singular cohomology of a point

Singular cochains of a one-point space contract onto the module of coefficient morphisms in
degree zero. In particular positive-degree singular cohomology vanishes over arbitrary
coefficient rings, without an injectivity or hereditary-ring hypothesis. The degree-zero
comparison evaluates a cocycle on the unique vertex, so constant cocycles retain their values.

We apply the contravariant Hom functor to `TauCeti.pointSingularChainHomotopyEquiv`, rather
than deducing this calculation from universal coefficients. This is the point calculation used
to show positive-degree classes restrict to zero on categorical open subsets.
See Hatcher, *Algebraic Topology*, Sections 3.1 and 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]
  (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (X : TopCat.{w}) [Unique X]

/-- The singular cochains of a one-point space contract onto the module of coefficient
morphisms in degree zero. The forward map evaluates on the unique vertex. -/
def pointSingularCochainHomotopyEquiv :
    HomotopyEquiv (X.singularCochainComplex R k M)
      ((CochainComplex.single₀ (ModuleCat.{v} k)).obj (ModuleCat.of k (R ⟶ M))) :=
  ((pointSingularChainHomotopyEquiv R X).linearYonedaFunctorMap k M).symm.trans
    (HomotopyEquiv.ofIso (ChainComplex.linearYonedaObjSingle₀Iso k R M))

/-- The point cochain contraction evaluates a zero-cochain on the unique vertex. -/
lemma pointSingularCochainHomotopyEquiv_hom_f_zero_apply
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) (a : (X.singularCochainComplex R k M).X 0) :
    dsimp% (pointSingularCochainHomotopyEquiv R k M X).hom.f 0 a =
      (TopCat.toSSet.obj X).ιChainComplex σ ≫ a := by
  rw [pointSingularCochainHomotopyEquiv, HomotopyEquiv.trans_hom,
    HomotopyEquiv.symm_hom, HomotopyEquiv.linearYonedaFunctorMap_inv,
    HomologicalComplex.comp_f]
  refine (CategoryTheory.comp_apply _ _ a).trans ?_
  refine (ChainComplex.linearYonedaObjSingle₀Iso_hom_f_zero_apply k R M _).trans ?_
  refine (ChainComplex.linearYonedaFunctor_map_f_hom_apply k M
    (pointSingularChainHomotopyEquiv R X).inv.op 0 a).trans ?_
  refine (congrArg (fun f ↦ f ≫ a)
    (pointSingularChainHomotopyEquiv_inv_f_zero R X σ)).trans ?_
  exact congrArg (fun f ↦ f ≫ a) (Category.id_comp _)

/-- The contraction preserves the value of a constant zero-cochain, including the cup unit. -/
@[simp]
lemma pointSingularCochainHomotopyEquiv_hom_constCochain (f : R ⟶ M) :
    dsimp% (pointSingularCochainHomotopyEquiv R k M X).hom.f 0
      ((TopCat.toSSet.obj X).constCochain f) = f := by
  let σ : (TopCat.toSSet.obj X) _⦋0⦌ :=
    (X.toSSetObjEquiv _).symm (ContinuousMap.const _ (default : X))
  exact (pointSingularCochainHomotopyEquiv_hom_f_zero_apply R k M X σ _).trans
    ((TopCat.toSSet.obj X).ιChainComplex_constCochain f σ)

/-- Positive-degree singular cohomology of a point vanishes, without restrictions on the
coefficient module. -/
theorem isZero_singularCohomology_point {n : ℕ} (hn : n ≠ 0) :
    IsZero (X.singularCohomology R k M n) :=
  (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℕ) 0
    (ModuleCat.of k (R ⟶ M)) n hn).of_iso
      ((pointSingularCochainHomotopyEquiv R k M X).toHomologyIso n)

/-- Degree-zero singular cohomology of a point is the module of coefficient morphisms. -/
def singularCohomologyPointZeroIso :
    X.singularCohomology R k M 0 ≅ ModuleCat.of k (R ⟶ M) :=
  (pointSingularCochainHomotopyEquiv R k M X).toHomologyIso 0 ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 _

/-- The degree-zero cohomology comparison is induced by evaluation on cochains. -/
@[reassoc (attr := simp)]
lemma homologyπ_singularCohomologyPointZeroIso_hom :
    (X.singularCochainComplex R k M).homologyπ 0 ≫
        (singularCohomologyPointZeroIso R k M X).hom =
      (X.singularCochainComplex R k M).iCycles 0 ≫
        (pointSingularCochainHomotopyEquiv R k M X).hom.f 0 ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
            (ModuleCat.of k (R ⟶ M))).hom := by
  simp only [singularCohomologyPointZeroIso, Iso.trans_hom, HomotopyEquiv.toHomologyIso]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom,
    ← Category.assoc, HomologicalComplex.cyclesMap_i, Category.assoc]

end TauCeti
