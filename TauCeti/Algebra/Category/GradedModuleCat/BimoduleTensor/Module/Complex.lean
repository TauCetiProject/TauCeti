/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Associator
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Coproducts
public import Mathlib.Algebra.Homology.BifunctorAssociator

/-!
# The cochain associator for the graded bimodule action

Mathlib's cochain bifunctor totalizes the balanced tensor action of internally graded
bimodules on graded left modules. Its associator compares two composable bimodule
complexes acting on a left-module complex, using the graded action associator and
coproduct preservation.

The source and target are expressed through the cochain action functor. The two
triple-summand equations identify the forward and inverse maps with the graded action
associator in each cochain degree. This specializes Joël Riou's totalized bifunctor
associator and its summand-inclusion equation.
-/

public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace TauCeti.GradedModuleCat

universe v uk uA uB uC
variable {k : Type uk} {A : Type uA} {B : Type uB}
  [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (Γ : InternalGrading k A) (Δ : InternalGrading k B)
  [GradedAlgebra Γ.piece] [GradedAlgebra Δ.piece]

/-- Balanced tensor action totalized with the usual cochain signs. -/
abbrev bimoduleModuleCochainTensor :
    CochainComplex (GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) ℤ ⥤
      CochainComplex (GradedModuleCat.{v} Δ.piece) ℤ ⥤
        CochainComplex (GradedModuleCat.{v} Γ.piece) ℤ :=
  (bimoduleModuleTensor Γ Δ).map₂CochainComplex

section Associator

variable {C : Type uC} [Ring C] [Algebra k C]
  (Θ : InternalGrading k C) [GradedAlgebra Θ.piece]
  (M : CochainComplex (GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) ℤ)
  (N : CochainComplex (GradedModuleCat.{v} (Δ.tensorProduct Θ.opposite).piece) ℤ)
  (P : CochainComplex (GradedModuleCat.{v} Θ.piece) ℤ)

/-- Reassociation of two graded bimodule complexes acting on a left-module complex. -/
def bimoduleModuleCochainTensorAssociator :
    ((bimoduleModuleCochainTensor Γ Θ).obj
        ((((bimoduleTensor Γ Δ Θ).map₂CochainComplex).obj M).obj N)).obj P ≅
      ((bimoduleModuleCochainTensor Γ Δ).obj M).obj
        (((bimoduleModuleCochainTensor Δ Θ).obj N).obj P) :=
  mapBifunctorAssociator (bimoduleModuleTensorAssociatorNatIso Γ Δ Θ) M N P
    (.up ℤ) (.up ℤ) (.up ℤ)

-- Expose the totalization object in implicit type matching without unfolding the associator.
attribute [local implicit_reducible] Functor.map₂HomologicalComplex

/-- The totalized associator acts on a triple summand by the graded action associator. -/
@[reassoc (attr := simp)]
theorem ι_bimoduleModuleCochainTensorAssociator_hom (p q r j : ℤ) (h : p + q + r = j) :
    mapBifunctor₁₂.ι (bimoduleTensor Γ Δ Θ) (bimoduleModuleTensor Γ Θ)
        M N P (.up ℤ) (.up ℤ) p q r j (by exact Eq.trans (by rfl) h) ≫
        (bimoduleModuleCochainTensorAssociator Γ Δ Θ M N P).hom.f j =
      (bimoduleModuleTensorAssociator Γ Δ Θ (M.X p) (N.X q) (P.X r)).hom ≫
        mapBifunctor₂₃.ι (bimoduleModuleTensor Γ Δ) (bimoduleModuleTensor Δ Θ)
          M N P (.up ℤ) (.up ℤ) (.up ℤ) p q r j (by exact Eq.trans (by rfl) h) := by
  dsimp only [bimoduleModuleCochainTensor, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex]
  simpa only [bimoduleModuleCochainTensorAssociator, mapBifunctorAssociator,
    Hom.isoOfComponents_hom_f, bimoduleModuleTensorAssociatorNatIso_hom_app] using
    ι_mapBifunctorAssociatorX_hom (bimoduleModuleTensorAssociatorNatIso Γ Δ Θ)
      M N P (.up ℤ) (.up ℤ) (.up ℤ) p q r j (by exact Eq.trans (by rfl) h)

/-- The inverse totalized associator acts by the inverse graded action associator. -/
@[reassoc (attr := simp)]
theorem ι_bimoduleModuleCochainTensorAssociator_inv (p q r j : ℤ) (h : p + q + r = j) :
    mapBifunctor₂₃.ι (bimoduleModuleTensor Γ Δ) (bimoduleModuleTensor Δ Θ)
        M N P (.up ℤ) (.up ℤ) (.up ℤ) p q r j (by exact Eq.trans (by rfl) h) ≫
        (bimoduleModuleCochainTensorAssociator Γ Δ Θ M N P).inv.f j =
      (bimoduleModuleTensorAssociator Γ Δ Θ (M.X p) (N.X q) (P.X r)).inv ≫
        mapBifunctor₁₂.ι (bimoduleTensor Γ Δ Θ) (bimoduleModuleTensor Γ Θ)
          M N P (.up ℤ) (.up ℤ) p q r j (by exact Eq.trans (by rfl) h) := by
  dsimp only [bimoduleModuleCochainTensor, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex]
  simp only [bimoduleModuleCochainTensorAssociator, mapBifunctorAssociator,
    Hom.isoOfComponents_inv_f]
  apply (Iso.eq_inv_comp
    (bimoduleModuleTensorAssociator Γ Δ Θ (M.X p) (N.X q) (P.X r))).2
  rw [← Category.assoc]
  apply (Iso.comp_inv_eq
    (mapBifunctorAssociatorX (bimoduleModuleTensorAssociatorNatIso Γ Δ Θ)
      M N P (.up ℤ) (.up ℤ) (.up ℤ) j)).2
  simpa only [bimoduleModuleTensorAssociatorNatIso_hom_app] using
    (ι_mapBifunctorAssociatorX_hom (bimoduleModuleTensorAssociatorNatIso Γ Δ Θ)
      M N P (.up ℤ) (.up ℤ) (.up ℤ) p q r j (by exact Eq.trans (by rfl) h)).symm

end Associator

end TauCeti.GradedModuleCat
