/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.LinearHomComplex.Single
public import TauCeti.Algebra.Homology.LinearYoneda
import TauCeti.Algebra.Homology.LinearHomComplex.Single.Basic

/-!
# Naturality and cohomology comparison for `linearHomComplexSingleIso`

`CochainComplex.linearHomComplexSingleIso` (`TauCeti.Algebra.Homology.LinearHomComplex.Single`)
identifies `linearHomComplex k K ((singleFunctor C 0).obj Y)` with
`ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y` by scaling
degree `i` by `(-1)^(i(i + 1) / 2)`.

This file records the naturality of `CochainComplex.linearHomComplexSingleIso` in both `K` and `Y`,
and defines the unsigned cohomology comparison isomorphism
`CochainComplex.linearHomComplexSingleHomologyIso` obtained by scaling the induced cohomology map by
`(-1)^(i(i + 1) / 2)` again.

## Main definitions and results

* `CochainComplex.linearHomComplexPrecomp_linearHomComplexSingleIso_hom` and
  `CochainComplex.linearHomComplexPostcomp_linearHomComplexSingleIso_hom`: naturality of
  `CochainComplex.linearHomComplexSingleIso` in `K` and `Y`.
* `CochainComplex.linearHomComplexSingleHomologyIso`,
  `CochainComplex.homologyMap_precomp_linearHomComplexSingleHomologyIso_hom`,
  `CochainComplex.homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom`,
  `CochainComplex.linearHomComplexSingleHomologyIso_hom_homologyπ`, and
  `CochainComplex.linearHomComplexSingleHomologyIso_inv_homologyπ`: unsigned cohomology comparison
  isomorphism, naturality, and cocycle formulas.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex.HomComplex Opposite TauCeti

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] (k : Type*) [Ring k] [Linear k C]

/-- Precomposition in `K` intertwines `CochainComplex.linearHomComplexSingleIso` with
`TauCeti.ChainComplex.linearYonedaFunctor` on the negated chain map. -/
@[reassoc]
theorem linearHomComplexPrecomp_linearHomComplexSingleIso_hom
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (Y : C) :
    linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
        (linearHomComplexSingleIso k K₁ Y).hom =
      (linearHomComplexSingleIso k K₂ Y).hom ≫
        (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op := by
  ext i (z : Cochain K₂ ((singleFunctor C 0).obj Y) i)
  have hlhs :
      ((linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
        (linearHomComplexSingleIso k K₁ Y).hom).f i).hom z =
      (i * (i + 1) / 2).negOnePow •
        Cochain.toSingleEquiv (neg_add_cancel i)
          (((linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)).f i).hom z) :=
    linearHomComplexSingleIso_hom_f_apply K₁ Y i _
  have hrhs :
      (((linearHomComplexSingleIso k K₂ Y).hom ≫
        (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op).f i).hom z =
      (i * (i + 1) / 2).negOnePow •
        (φ.f (-i) ≫ Cochain.toSingleEquiv (neg_add_cancel i) z) := by
    have hmap :
        (((linearHomComplexSingleIso k K₂ Y).hom ≫
          (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
            (HomologicalComplex.restrictionMap φ
              ComplexShape.embeddingDownIntUpInt).op).f i).hom z =
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).f i ≫
          (linearHomComplexSingleIso k K₂ Y).hom.f i z :=
      TauCeti.ChainComplex.linearYonedaFunctor_map_f_hom_apply k Y
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op i _
    rw [hmap, linearHomComplexSingleIso_hom_f_apply, Units.smul_def, Units.smul_def,
      Preadditive.comp_zsmul]
    rfl
  refine hlhs.trans (Eq.trans ?_ hrhs.symm)
  congr 1
  exact toSingleLinearEquiv_linearHomComplexPrecomp_f_apply φ Y i z

/-- Postcomposition with a coefficient morphism `g : Y₁ ⟶ Y₂` intertwines
`CochainComplex.linearHomComplexSingleIso` with `ChainComplex.linearYonedaObjMap`. -/
@[reassoc]
theorem linearHomComplexPostcomp_linearHomComplexSingleIso_hom
    (K : CochainComplex C ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    linearHomComplexPostcomp k K ((singleFunctor C 0).map g) ≫
        (linearHomComplexSingleIso k K Y₂).hom =
      (linearHomComplexSingleIso k K Y₁).hom ≫
        _root_.ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) g := by
  ext i (z : Cochain K ((singleFunctor C 0).obj Y₁) i)
  have hlhs :
      ((linearHomComplexPostcomp k K ((singleFunctor C 0).map g) ≫
        (linearHomComplexSingleIso k K Y₂).hom).f i).hom z =
      (i * (i + 1) / 2).negOnePow •
        Cochain.toSingleEquiv (neg_add_cancel i)
          (((linearHomComplexPostcomp k K ((singleFunctor C 0).map g)).f i).hom z) :=
    linearHomComplexSingleIso_hom_f_apply K Y₂ i _
  have hrhs :
      (((linearHomComplexSingleIso k K Y₁).hom ≫
        _root_.ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) g).f i).hom z =
      (i * (i + 1) / 2).negOnePow •
        (Cochain.toSingleEquiv (neg_add_cancel i) z ≫ g) := by
    have hmap :
        (((linearHomComplexSingleIso k K Y₁).hom ≫
          _root_.ChainComplex.linearYonedaObjMap k
            (K.restriction ComplexShape.embeddingDownIntUpInt) g).f i).hom z =
        (linearHomComplexSingleIso k K Y₁).hom.f i z ≫ g :=
      _root_.ChainComplex.linearYonedaObjMap_f_hom_apply k
        (K.restriction ComplexShape.embeddingDownIntUpInt) g i _
    rw [hmap, linearHomComplexSingleIso_hom_f_apply, Units.smul_def, Units.smul_def,
      Preadditive.zsmul_comp]
  refine hlhs.trans (Eq.trans ?_ hrhs.symm)
  congr 1
  exact toSingleLinearEquiv_linearHomComplexPostcomp_f_apply K g i z

/-- **Unsigned cohomology comparison** between `linearHomComplex k K ((singleFunctor C 0).obj Y)`
and `_root_.ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y` in
degree `i`. Multiplying the map on cohomology induced by `CochainComplex.linearHomComplexSingleIso`
by `(-1)^(i(i + 1) / 2)` cancels the degree-`i` sign on cocycles while keeping naturality in both
`K` and `Y`. -/
def linearHomComplexSingleHomologyIso (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≅
      (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homology i :=
  (i * (i + 1) / 2).negOnePow •
    HomologicalComplex.homologyMapIso (linearHomComplexSingleIso k K Y) i

@[simp]
lemma linearHomComplexSingleHomologyIso_hom (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplexSingleHomologyIso k K Y i).hom =
      (i * (i + 1) / 2).negOnePow • homologyMap (linearHomComplexSingleIso k K Y).hom i :=
  (rfl)

@[simp]
lemma linearHomComplexSingleHomologyIso_inv (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplexSingleHomologyIso k K Y i).inv =
      (i * (i + 1) / 2).negOnePow • homologyMap (linearHomComplexSingleIso k K Y).inv i := by
  simp [linearHomComplexSingleHomologyIso, Int.units_inv_eq_self]

/-- `CochainComplex.linearHomComplexSingleHomologyIso` is natural with respect to precomposition by
a cochain map `φ : K₁ ⟶ K₂`. -/
@[reassoc]
theorem homologyMap_precomp_linearHomComplexSingleHomologyIso_hom
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (Y : C) (i : ℤ) :
    homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i ≫
        (linearHomComplexSingleHomologyIso k K₁ Y i).hom =
      (linearHomComplexSingleHomologyIso k K₂ Y i).hom ≫
        homologyMap
          (K := _root_.ChainComplex.linearYonedaObj
            (K₂.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          (L := _root_.ChainComplex.linearYonedaObj
            (K₁.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
            (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i := by
  have hcomp := HomologicalComplex.homologyMap_comp
    (K := linearHomComplex k K₂ ((singleFunctor C 0).obj Y))
    (L := _root_.ChainComplex.linearYonedaObj
      (K₂.restriction ComplexShape.embeddingDownIntUpInt) k Y)
    (M := _root_.ChainComplex.linearYonedaObj
      (K₁.restriction ComplexShape.embeddingDownIntUpInt) k Y)
    (linearHomComplexSingleIso k K₂ Y).hom
    ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
      (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i
  rw [linearHomComplexSingleHomologyIso_hom, linearHomComplexSingleHomologyIso_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, ← homologyMap_comp, ← hcomp,
    linearHomComplexPrecomp_linearHomComplexSingleIso_hom]
  rfl

/-- `CochainComplex.linearHomComplexSingleHomologyIso` is natural with respect to postcomposition by
a coefficient morphism `g : Y₁ ⟶ Y₂`. -/
@[reassoc]
theorem homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom
    (K : CochainComplex C ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ) :
    homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i ≫
        (linearHomComplexSingleHomologyIso k K Y₂ i).hom =
      (linearHomComplexSingleHomologyIso k K Y₁ i).hom ≫
        homologyMap
          (_root_.ChainComplex.linearYonedaObjMap k
            (K.restriction ComplexShape.embeddingDownIntUpInt) g) i := by
  rw [linearHomComplexSingleHomologyIso_hom, linearHomComplexSingleHomologyIso_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, ← homologyMap_comp, ← homologyMap_comp,
    linearHomComplexPostcomp_linearHomComplexSingleIso_hom]

/-- On cocycles, `CochainComplex.linearHomComplexSingleHomologyIso` removes the sign
`(-1)^(i(i + 1) / 2)` and sends the class of a cocycle `φ` directly to the class of
`Cochain.toSingleLinearEquiv` applied to its underlying cochain. -/
lemma linearHomComplexSingleHomologyIso_hom_homologyπ {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)) :
    (linearHomComplexSingleHomologyIso k K Y i).hom.hom
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ) =
      (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ := by
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (linearHomComplexSingleIso k K Y).hom i) φ
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hnat
  have hcyc : cyclesMap (linearHomComplexSingleIso k K Y).hom i φ =
      (i * (i + 1) / 2).negOnePow • ψ := by
    apply HomologicalComplex.moduleCat_iCycles_injective
    have hi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (linearHomComplexSingleIso k K Y).hom i) φ
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hi
    rw [hi, linearHomComplexSingleIso_hom_f_apply, map_zsmul_unit, hψ]
    rfl
  rw [linearHomComplexSingleHomologyIso_hom, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, ← Units.smul_def, hnat, hcyc, map_zsmul_unit,
    Int.negOnePow_smul_negOnePow_smul]

/-- Inverse form of `CochainComplex.linearHomComplexSingleHomologyIso_hom_homologyπ`:
`(CochainComplex.linearHomComplexSingleHomologyIso k K Y i).inv` sends the class of `ψ` to the
class of `φ`. -/
lemma linearHomComplexSingleHomologyIso_inv_homologyπ {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)) :
    (linearHomComplexSingleHomologyIso k K Y i).inv.hom
        ((_root_.ChainComplex.linearYonedaObj
          (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ) =
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ := by
  rw [← linearHomComplexSingleHomologyIso_hom_homologyπ K Y i φ ψ hψ, ← ModuleCat.comp_apply,
    Iso.hom_inv_id, ModuleCat.id_apply]

end CochainComplex
