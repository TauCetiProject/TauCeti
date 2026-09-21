/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Braiding

/-!
# The monoidal structure of cochain complexes of modules on homogeneous summands

Mathlib's `HomologicalComplex.monoidalCategory` totalizes the degreewise tensor product, so every
structural map of `CochainComplex (ModuleCat R) ℤ` is assembled from maps on the homogeneous
summands `X.X p ⊗ Y.X q` of `X ⊗ Y`.  Mathlib states the component formulas for the auxiliary
constructions the monoidal structure is built from — `HomologicalComplex.mapBifunctorMap`,
`HomologicalComplex.leftUnitor'`, `HomologicalComplex.rightUnitor'` and
`HomologicalComplex.mapBifunctorAssociatorX` — but not for the whiskerings, `λ_`, `ρ_` and `α_`
themselves.  This file supplies that last step, so that a calculation on homogeneous summands
never has to unfold the monoidal structure.

## Main results

* `HomologicalComplex.ι_whiskerLeft` and `HomologicalComplex.ι_whiskerRight`: the two whiskerings
  on a homogeneous summand.
* `HomologicalComplex.leftUnitor_inv_f` and `HomologicalComplex.rightUnitor_inv_f`: the degreewise
  components of the inverse unitors.
* `HomologicalComplex.ι_ι_associator_hom`: the associator on the summand
  `X.X p ⊗ Y.X q ⊗ Z.X r`.

The analogous formula for the differential of a tensor product is
`HomologicalComplex.ι_tensorObj_d` in `TauCeti/Algebra/Homology/Monoidal/TensorDifferential.lean`.
-/

public section

open CategoryTheory MonoidalCategory

universe v

namespace HomologicalComplex

variable {R : Type v} [CommRing R]

/-- Left whiskering of cochain complexes of modules, restricted to a homogeneous summand, is left
whiskering of the summand. -/
@[reassoc (attr := simp)]
lemma ι_whiskerLeft (X : CochainComplex (ModuleCat.{v} R) ℤ)
    {Y Z : CochainComplex (ModuleCat.{v} R) ℤ} (g : Y ⟶ Z) (p q j : ℤ) (h : p + q = j) :
    ιTensorObj X Y p q j h ≫ (X ◁ g).f j = (X.X p ◁ g.f q) ≫ ιTensorObj X Z p q j h := by
  rw [TauCeti.whiskerLeft_eq_mapBifunctorMap, ι_mapBifunctorMap]
  simp

/-- Right whiskering of cochain complexes of modules, restricted to a homogeneous summand, is
right whiskering of the summand. -/
@[reassoc (attr := simp)]
lemma ι_whiskerRight {X Y : CochainComplex (ModuleCat.{v} R) ℤ} (f : X ⟶ Y)
    (Z : CochainComplex (ModuleCat.{v} R) ℤ) (p q j : ℤ) (h : p + q = j) :
    ιTensorObj X Z p q j h ≫ (f ▷ Z).f j = (f.f p ▷ Z.X q) ≫ ιTensorObj Y Z p q j h := by
  rw [TauCeti.whiskerRight_eq_mapBifunctorMap, ι_mapBifunctorMap]
  simp

/-- The degreewise component of the inverse left unitor of cochain complexes of modules is the
component of the auxiliary graded isomorphism `HomologicalComplex.leftUnitor'`, whose value is
recorded by `HomologicalComplex.leftUnitor'_inv`. -/
lemma leftUnitor_inv_f (X : CochainComplex (ModuleCat.{v} R) ℤ) (j : ℤ) :
    (λ_ X).inv.f j = (leftUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.leftUnitor, monoidalCategoryStruct,
    monoidalCategory, leftUnitor, Iso.symm_inv]
  simp only [Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The degreewise component of the inverse right unitor of cochain complexes of modules is the
component of the auxiliary graded isomorphism `HomologicalComplex.rightUnitor'`, whose value is
recorded by `HomologicalComplex.rightUnitor'_inv`. -/
lemma rightUnitor_inv_f (X : CochainComplex (ModuleCat.{v} R) ℤ) (j : ℤ) :
    (ρ_ X).inv.f j = (rightUnitor' X).inv j := by
  dsimp only [MonoidalCategoryStruct.rightUnitor, monoidalCategoryStruct,
    monoidalCategory, rightUnitor, Iso.symm_inv]
  simp only [Hom.isoOfComponents_hom_f, Functor.mapIso_hom, Iso.symm_hom]
  rfl

/-- The associator of cochain complexes of modules, restricted to the summand indexed by the
degrees `p`, `q` and `r`, is the associator of the three summands. -/
@[reassoc]
lemma ι_ι_associator_hom (X Y Z : CochainComplex (ModuleCat.{v} R) ℤ) (p q r j : ℤ)
    (h : p + q + r = j) :
    (ιTensorObj X Y p q (p + q) rfl ▷ Z.X r) ≫
        ιTensorObj (X ⊗ Y) Z (p + q) r j h ≫ (α_ X Y Z).hom.f j =
      (α_ (X.X p) (Y.X q) (Z.X r)).hom ≫ (X.X p ◁ ιTensorObj Y Z q r (q + r) rfl) ≫
        ιTensorObj X (Y ⊗ Z) p (q + r) j (by omega) := by
  -- The totalization index of a triple tensor product is definitionally the sum of the three
  -- degrees; naming the reindexed hypothesis keeps every later term type-correct.
  have hr : ComplexShape.r (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q, r) = j := h
  have e₁ : mapBifunctor₁₂.ι (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r j hr =
      (ιTensorObj X Y p q (p + q) rfl ▷ Z.X r) ≫ ιTensorObj (X ⊗ Y) Z (p + q) r j h := by
    rw [mapBifunctor₁₂.ι_eq (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r (p + q) j rfl h]
    rfl
  have e₂ : mapBifunctor₂₃.ι (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r j hr =
      (X.X p ◁ ιTensorObj Y Z q r (q + r) rfl) ≫ ιTensorObj X (Y ⊗ Z) p (q + r) j (by omega) := by
    rw [mapBifunctor₂₃.ι_eq (curriedTensor (ModuleCat.{v} R)) (curriedTensor (ModuleCat.{v} R))
      X Y Z (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r (q + r) j rfl
      (by dsimp; omega)]
    rfl
  rw [← Category.assoc, ← e₁, ← e₂]
  -- Mathlib assembles the associator of homological complexes from
  -- `HomologicalComplex.mapBifunctorAssociatorX`, but states no component lemma for `α_`.
  have ha : (α_ X Y Z).hom.f j =
      (mapBifunctorAssociatorX (curriedAssociatorNatIso (ModuleCat.{v} R)) X Y Z
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) j).hom := rfl
  rw [ha]
  simp only [ι_mapBifunctorAssociatorX_hom, curriedAssociatorNatIso_hom_app_app_app]
  -- Both sides are now the same inclusion; they carry different proofs of the totalization index
  -- equation, which `simp` does not identify syntactically.
  rfl

end HomologicalComplex
