/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The singular chain contraction of a point

The singular chains of a one-point space are chain homotopy equivalent to the coefficient
object in degree zero. The forward map is augmentation and the inverse includes the unique
vertex. Unlike a homology calculation, this contraction can be applied contravariantly to
cochains without projectivity or injectivity assumptions on the coefficients.

The construction uses Mathlib's `TopCat.toSSetIsoConst` and
`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` for the constant augmented
simplicial object. See Hatcher, *Algebraic Topology*, Section 2.1, for the point calculation.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [HasZeroObject C] (R : C) (X : TopCat.{w}) [Unique X]

/-- The singular chain complex of a one-point space contracts onto its coefficients in degree
zero, with augmentation as forward map and the unique vertex as inverse. -/
def pointSingularChainHomotopyEquiv :
    HomotopyEquiv ((TopCat.toSSet.obj X).chainComplex R) ((ChainComplex.single₀ C).obj R) :=
  (HomotopyEquiv.ofIso ((alternatingFaceMapComplex C).mapIso
    (Functor.isoWhiskerRight (TopCat.toSSetIsoConst X) (sigmaConst.obj R) ≪≫
      Functor.constComp _ _ _))).trans
    ((SimplicialObject.Augmented.ExtraDegeneracy.const (∐ fun _ : X ↦ R)).homotopyEquiv.trans
      (HomotopyEquiv.ofIso ((ChainComplex.single₀ C).mapIso
        (coproductUniqueIso fun _ : X ↦ R))))

/-- Augmentation sends the unique singular vertex to the coefficient identity. -/
@[reassoc (attr := simp)]
lemma ι_pointSingularChainHomotopyEquiv_hom_f_zero
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ (pointSingularChainHomotopyEquiv R X).hom.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).inv := by
  simp [SimplicialObject.Augmented.const, pointSingularChainHomotopyEquiv,
    HomotopyEquiv.ofIso, SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv,
    HomologicalComplex.comp_f, SSet.ιChainComplex, sigmaConst, Sigma.map', Functor.constComp]

/-- The inverse contraction includes the summand indexed by the unique singular vertex. -/
lemma pointSingularChainHomotopyEquiv_inv_f_zero
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (pointSingularChainHomotopyEquiv R X).inv.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).hom ≫
        (TopCat.toSSet.obj X).ιChainComplex σ := by
  have : Subsingleton ((TopCat.toSSet.obj X) _⦋0⦌) :=
    (X.toSSetObjEquiv _).subsingleton
  have hι : (pointSingularChainHomotopyEquiv R X).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 R).hom ≫
        (TopCat.toSSet.obj X).ιChainComplex σ = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext
    intro τ
    rw [← Category.assoc, ι_pointSingularChainHomotopyEquiv_hom_f_zero]
    simp [Subsingleton.elim τ σ]
  have : Mono ((pointSingularChainHomotopyEquiv R X).hom.f 0) := mono_of_mono_fac hι
  apply (cancel_mono ((pointSingularChainHomotopyEquiv R X).hom.f 0)).1
  rw [Category.assoc, ι_pointSingularChainHomotopyEquiv_hom_f_zero, Iso.hom_inv_id]
  have h := (pointSingularChainHomotopyEquiv R X).homotopyInvHomId.comm 0
  rw [Homotopy.prevD_chainComplex, Homotopy.dNext_zero_chainComplex] at h
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    HomologicalComplex.single_obj_d, comp_zero, zero_add] using h

/-- Augmentation is natural in the coefficient object. -/
@[reassoc]
lemma pointSingularChainHomotopyEquiv_hom_naturality {S : C} (f : R ⟶ S) :
    (((SSet.chainComplexFunctor C).map f).app (TopCat.toSSet.obj X)) ≫
        (pointSingularChainHomotopyEquiv S X).hom =
      (pointSingularChainHomotopyEquiv R X).hom ≫ (ChainComplex.single₀ C).map f := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_chainComplexFunctor_map_app_f,
    Category.assoc, ι_pointSingularChainHomotopyEquiv_hom_f_zero,
    ← Category.assoc, ι_pointSingularChainHomotopyEquiv_hom_f_zero,
    HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]

end TauCeti
