/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.HomComplex.Cohomology
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic

/-!
# Cohomology of linear Hom complexes

In a linear preadditive category, Mathlib's cohomology-class equivalences show that the
additive Hom complex and `CochainComplex.linearHomComplex` are exact in the same degrees,
and hence are acyclic together. No abelian hypothesis on the category is needed.

The `n`-th cohomology of `CochainComplex.linearHomComplex R K L` is the `R`-module of morphisms
`K ⟶ L⟦n⟧` in the homotopy category (`TauCeti.linearHomComplexHomologyLinearEquiv`). This
identification is natural: the maps induced on cohomology by postcomposition and precomposition
with chain maps correspond to composition in the homotopy category. The naturality rests on
`CochainComplex.HomComplex.homologyLinearEquiv_homologyMap_symm_mk`, which computes the map
induced on cohomology classes by any chain map of linear Hom complexes.
-/

public section

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

universe v u w

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] (R : Type w) [Ring R] [Linear R C]

/-- A chain map `Φ` of linear Hom complexes acts on cohomology classes through its action on
cocycles: under `CochainComplex.HomComplex.homologyLinearEquiv`, the map induced by `Φ` in
degree `n` sends the class of a cocycle `x` to the class of the cocycle `Φ x`. -/
theorem homologyLinearEquiv_homologyMap_symm_mk {K L K' L' : CochainComplex C ℤ}
    (Φ : linearHomComplex R K L ⟶ linearHomComplex R K' L') {n : ℤ} (x : Cocycle K L n)
    (y : Cocycle K' L' n) (hy : (y : Cochain K' L' n) = (Φ.f n).hom (x : Cochain K L n)) :
    homologyLinearEquiv R K' L' n
        ((HomologicalComplex.homologyMap Φ n).hom ((homologyLinearEquiv R K L n).symm
          (CohomologyClass.mk x))) = CohomologyClass.mk y := by
  let γ := ShortComplex.leftHomologyMapData ((HomologicalComplex.shortComplexFunctor _ _ n).map Φ)
    (linearLeftHomologyData R K L n) (linearLeftHomologyData R K' L' n)
  have h := congr(($(γ.homologyMap_comm)).hom ((homologyLinearEquiv R K L n).symm
    (CohomologyClass.mk x)))
  have hπ := congr(($(γ.commπ)).hom x)
  have hK : γ.φK.hom x = y := Cocycle.ext (congr(($(γ.commi)).hom x).trans hy.symm)
  -- `homologyLinearEquiv` is the isomorphism of the left homology data, and the projection of
  -- that left homology data is `CohomologyClass.mk`.
  have he : (linearLeftHomologyData R K L n).homologyIso.hom.hom
      ((homologyLinearEquiv R K L n).symm (CohomologyClass.mk x)) =
        (linearLeftHomologyData R K L n).π.hom x :=
    (homologyLinearEquiv R K L n).apply_symm_apply _
  refine h.trans ?_
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hπ
  exact (congrArg γ.φH.hom he).trans (hπ.trans (congrArg _ hK))

end CochainComplex.HomComplex

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ} (R : Type w) [Ring R] [Linear R C]

/-- The linear and additive Hom complexes are exact in the same integer degrees. -/
theorem exactAt_linearHomComplex_iff (n : ℤ) :
    (CochainComplex.linearHomComplex R K L).ExactAt n ↔ (HomComplex K L).ExactAt n := by
  rw [exactAt_homComplex_iff_subsingleton_cohomologyClass,
    HomologicalComplex.exactAt_iff_isZero_homology,
    ModuleCat.isZero_iff_subsingleton,
    (homologyLinearEquiv R K L n).toEquiv.subsingleton_congr]

/-- The linear Hom complex is acyclic exactly when the additive Hom complex is acyclic. -/
theorem acyclic_linearHomComplex_iff :
    (CochainComplex.linearHomComplex R K L).Acyclic ↔ (HomComplex K L).Acyclic :=
  forall_congr' fun n ↦ exactAt_linearHomComplex_iff R n

/-- The `n`-th cohomology of the linear Hom complex from `F` to `G` is the `R`-module of
morphisms `F ⟶ G⟦n⟧` in the homotopy category. -/
noncomputable def linearHomComplexHomologyLinearEquiv (F G : CochainComplex C ℤ) (n : ℤ) :
    (linearHomComplex R F G).homology n ≃ₗ[R]
      ((HomotopyCategory.quotient C _).obj F ⟶ (HomotopyCategory.quotient C _).obj (G⟦n⟧)) :=
  homologyLinearEquiv R F G n ≪≫ₗ CohomologyClass.homLinearEquiv R F G n

/-- The class of a cocycle `x` of degree `n` corresponds to the homotopy class of the chain map
`K ⟶ L⟦n⟧` defined by `x`. -/
@[simp]
theorem linearHomComplexHomologyLinearEquiv_symm_mk {n : ℤ} (x : Cocycle K L n) :
    linearHomComplexHomologyLinearEquiv R K L n
        ((homologyLinearEquiv R K L n).symm (CohomologyClass.mk x)) =
      (HomotopyCategory.quotient C _).map (Cocycle.equivHomShift.symm x) := by
  simp [linearHomComplexHomologyLinearEquiv]

/-- Postcomposition by a chain map `g : L ⟶ L'` acts on the cohomology of linear Hom complexes
by composition with `g⟦n⟧` in the homotopy category. -/
theorem linearHomComplexHomologyLinearEquiv_homologyMap_postcomp {L' : CochainComplex C ℤ}
    (g : L ⟶ L') {n : ℤ} (z : (linearHomComplex R K L).homology n) :
    linearHomComplexHomologyLinearEquiv R K L' n
        ((HomologicalComplex.homologyMap (linearHomComplexPostcomp R K g) n).hom z) =
      linearHomComplexHomologyLinearEquiv R K L n z ≫
        (HomotopyCategory.quotient C _).map (g⟦n⟧') := by
  obtain ⟨c, rfl⟩ := (homologyLinearEquiv R K L n).symm.surjective z
  induction c using CohomologyClass.rec with | mk x => ?_
  rw [linearHomComplexHomologyLinearEquiv_symm_mk, ← Functor.map_comp,
    ← Cocycle.equivHomShift_symm_postcomp, linearHomComplexHomologyLinearEquiv,
    LinearEquiv.trans_apply, homologyLinearEquiv_homologyMap_symm_mk R _ x (x.postcomp g) (by simp),
    CohomologyClass.homLinearEquiv_mk]

/-- Precomposition by a chain map `f : K' ⟶ K` acts on the cohomology of linear Hom complexes
by precomposition with `f` in the homotopy category. -/
theorem linearHomComplexHomologyLinearEquiv_homologyMap_precomp {K' : CochainComplex C ℤ}
    (f : K' ⟶ K) {n : ℤ} (z : (linearHomComplex R K L).homology n) :
    linearHomComplexHomologyLinearEquiv R K' L n
        ((HomologicalComplex.homologyMap (linearHomComplexPrecomp R f L) n).hom z) =
      (HomotopyCategory.quotient C _).map f ≫ linearHomComplexHomologyLinearEquiv R K L n z := by
  obtain ⟨c, rfl⟩ := (homologyLinearEquiv R K L n).symm.surjective z
  induction c using CohomologyClass.rec with | mk x => ?_
  rw [linearHomComplexHomologyLinearEquiv_symm_mk, ← Functor.map_comp,
    ← Cocycle.equivHomShift_symm_precomp, linearHomComplexHomologyLinearEquiv,
    LinearEquiv.trans_apply, homologyLinearEquiv_homologyMap_symm_mk R _ x (x.precomp f) (by simp),
    CohomologyClass.homLinearEquiv_mk]

end TauCeti
