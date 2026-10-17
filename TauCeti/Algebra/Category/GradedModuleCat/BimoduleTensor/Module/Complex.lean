/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Coproducts
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Associator
public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Module.Coproducts
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy
public import Mathlib.Algebra.Homology.BifunctorAssociator

/-!
# The totalized action of graded bimodule complexes on graded left-module complexes

Mathlib's cochain bifunctor totalizes the balanced tensor action. The inclusion of
an internally graded tensor summand has degree zero, and its differential has the
cohomological sign `(-1)^p` on the second factor. Internal degrees introduce no sign.
The existing additive bifunctor homotopy construction preserves homotopy equivalences.
The totalization and associator reuse Joël Riou's Mathlib bifunctor constructions.

The associator is Mathlib's totalized bifunctor associator, using the graded module
associator and coproduct preservation. Unit and coherence comparisons on complexes
are needed before deducing the Artin group action.
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

variable (M : CochainComplex
    (GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) ℤ)
  (N : CochainComplex (GradedModuleCat.{v} Δ.piece) ℤ)

/-- Include the `(p,q)` summand in degree `p+q` of the totalized module action. -/
def bimoduleModuleCochainTensorι (p q j : ℤ) (h : p + q = j) :
    bimoduleModuleTensorObj Γ Δ (M.X p) (N.X q) ⟶
      (((bimoduleModuleCochainTensor Γ Δ).obj M).obj N).X j :=
  ιMapBifunctor M N (bimoduleModuleTensor Γ Δ) (.up ℤ) p q j h

/-- The total differential acts on the second cochain factor with sign `(-1)^p`. -/
@[reassoc]
theorem bimoduleModuleCochainTensorι_d (p q j : ℤ) (h : p + q = j) :
    bimoduleModuleCochainTensorι Γ Δ M N p q j h ≫
        (((bimoduleModuleCochainTensor Γ Δ).obj M).obj N).d j (j + 1) =
      bimoduleModuleTensorMap Γ Δ (M.d p (p + 1)) (𝟙 (N.X q)) ≫
          bimoduleModuleCochainTensorι Γ Δ M N (p + 1) q (j + 1) (by omega) +
        p.negOnePow • (bimoduleModuleTensorMap Γ Δ (𝟙 (M.X p)) (N.d q (q + 1)) ≫
          bimoduleModuleCochainTensorι Γ Δ M N p (q + 1) (j + 1) (by omega)) := by
  dsimp only [bimoduleModuleCochainTensor, Functor.map₂CochainComplex,
    Functor.map₂HomologicalComplex, bimoduleModuleCochainTensorι]
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
  rw [mapBifunctor.d₁_eq _ _ _ _ (by rfl) _ _ (by dsimp; omega),
    mapBifunctor.d₂_eq _ _ _ _ _ (by rfl) _ (by dsimp; omega)]
  simp only [show ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = 1 from rfl,
    show ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = p.negOnePow from rfl,
    one_smul, bimoduleModuleTensor]

variable {M N}
  {M' : CochainComplex (GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) ℤ}
  {N' : CochainComplex (GradedModuleCat.{v} Δ.piece) ℤ}

/-- Homotopy equivalences of either input induce a homotopy equivalence of the total action. -/
def bimoduleModuleCochainTensorHomotopyEquiv
    (eM : HomotopyEquiv M M') (eN : HomotopyEquiv N N') :
    HomotopyEquiv (((bimoduleModuleCochainTensor Γ Δ).obj M).obj N)
      (((bimoduleModuleCochainTensor Γ Δ).obj M').obj N') :=
  HomotopyEquiv.mapBifunctor (bimoduleModuleTensor Γ Δ) (.up ℤ) eM eN

section Associator

variable {C : Type uC} [Ring C] [Algebra k C]
  (Θ : InternalGrading k C) [GradedAlgebra Θ.piece]
  (M : CochainComplex (GradedModuleCat.{v} (Γ.tensorProduct Δ.opposite).piece) ℤ)
  (N : CochainComplex (GradedModuleCat.{v} (Δ.tensorProduct Θ.opposite).piece) ℤ)
  (P : CochainComplex (GradedModuleCat.{v} Θ.piece) ℤ)

/-- Reassociation of two graded bimodule complexes acting on a left-module complex. -/
def bimoduleModuleCochainTensorAssociator :
    mapBifunctor (mapBifunctor M N (bimoduleTensor Γ Δ Θ) (.up ℤ)) P
        (bimoduleModuleTensor Γ Θ) (.up ℤ) ≅
      mapBifunctor M (mapBifunctor N P (bimoduleModuleTensor Δ Θ) (.up ℤ))
        (bimoduleModuleTensor Γ Δ) (.up ℤ) :=
  mapBifunctorAssociator (bimoduleModuleTensorAssociatorNatIso Γ Δ Θ) M N P
    (.up ℤ) (.up ℤ) (.up ℤ)

end Associator

end TauCeti.GradedModuleCat
