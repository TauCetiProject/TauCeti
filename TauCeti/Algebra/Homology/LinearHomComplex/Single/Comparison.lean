/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.Algebra.Homology.LinearHomComplex.Single.Basic
public import TauCeti.Algebra.Homology.LinearYoneda
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Comparison of `linearHomComplex` into a degree-zero object with `linearYonedaObj`

For a `ℤ`-indexed cochain complex `K` in a `k`-linear abelian category `C` and an object `Y : C`,
reindexing `K` along `n ↦ -n` (`ComplexShape.embeddingDownIntUpInt`) gives a chain complex `K'`
whose unsigned dual `K'.linearYonedaObj k Y` is naturally isomorphic to
`linearHomComplex k K ((singleFunctor C 0).obj Y)` after scaling degree `i` by
`(-1)^(i(i + 1) / 2)` (`TauCeti.linearHomComplexSingle₀Iso`).

Scaling the induced cohomology isomorphism by `(-1)^(i(i + 1) / 2)` again cancels the sign on
cocycles while preserving naturality in `K` and `Y` (`TauCeti.linearHomComplexSingle₀HomologyIso`).

## Main definitions and results

* `TauCeti.linearHomComplexSingle₀Iso`, `TauCeti.linearHomComplexSingle₀Iso_hom_f_apply`, and
  `TauCeti.linearHomComplexSingle₀Iso_inv_f_apply`: signed complex comparison isomorphism and its
  degreewise formulas.
* `TauCeti.linearHomComplexPrecomp_linearHomComplexSingle₀Iso_hom` and
  `TauCeti.linearHomComplexPostcomp_linearHomComplexSingle₀Iso_hom`: naturality in `K` and `Y`.
* `TauCeti.linearHomComplexSingle₀HomologyIso`,
  `TauCeti.homologyMap_precomp_linearHomComplexSingle₀HomologyIso_hom`,
  `TauCeti.homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom`,
  `TauCeti.linearHomComplexSingle₀HomologyIso_hom_homologyπ`, and
  `TauCeti.linearHomComplexSingle₀HomologyIso_inv_homologyπ`: unsigned cohomology comparison
  isomorphism, naturality, and cocycle formulas.

## References

* Joël Riou's Mathlib constructions `CochainComplex.linearHomComplex` and
  `ComplexShape.embeddingDownIntUpInt`.
* `TauCeti.Algebra.Homology.LinearYoneda` for `ChainComplex.linearYonedaObjMap` and
  `ChainComplex.linearYonedaFunctor`.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex Opposite

universe v u

namespace TauCeti

section Comparison

variable {C : Type u} [Category.{v} C] [Abelian C] (k : Type*) [Ring k] [Linear k C]

/-- Reindexing a `ℤ`-indexed cochain complex `K` along `n ↦ -n` as a chain complex. -/
private abbrev negChain (K : CochainComplex C ℤ) : ChainComplex C ℤ :=
  K.restriction ComplexShape.embeddingDownIntUpInt

/-- **Comparison of `linearHomComplex` into a degree-zero object with `linearYonedaObj`.**
Scaling `Cochain.toSingleLinearEquiv (neg_add_cancel i)` by `(-1)^(i(i + 1) / 2)` in degree `i`
gives an isomorphism of cochain complexes from `linearHomComplex k K ((singleFunctor C 0).obj Y)` to
`(K.restriction ComplexShape.embeddingDownIntUpInt).linearYonedaObj k Y`. -/
def linearHomComplexSingle₀Iso (K : CochainComplex C ℤ) (Y : C) :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅
      _root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (i * (i + 1) / 2).negOnePow •
      (Cochain.toSingleLinearEquiv (R := k) (K := K) (X := Y) (neg_add_cancel i)).toModuleIso)
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := by simpa [ComplexShape.up_Rel] using hij
      ext (z : ModuleCat.of k (Cochain K ((singleFunctor C 0).obj Y) i))
      have h1 : (((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1) ≫
            (((i + 1) * (i + 1 + 1) / 2).negOnePow •
              (Cochain.toSingleLinearEquiv (R := k) (K := K) (X := Y)
                (neg_add_cancel (i + 1))).toModuleIso).hom).hom z : K.X (-(i + 1)) ⟶ Y) =
          (i * (i + 1) / 2).negOnePow •
            (K.d (-(i + 1)) (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
        have hz := toSingleLinearEquiv_linearHomComplex_d_apply (k := k) K Y i z
        calc (((i + 1) * (i + 1 + 1) / 2).negOnePow •
              Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel (i + 1))
                (((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom z))
            = ((i + 1) * (i + 1 + 1) / 2).negOnePow • ((i + 1).negOnePow •
                (K.d (-(i + 1)) (-i) ≫
                  Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z)) := by rw [hz]
          _ = (i * (i + 1) / 2).negOnePow •
                (K.d (-(i + 1)) (-i) ≫
                  Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
            rw [Int.negOnePow_mul_succ_div_two_succ i, mul_comm (i + 1).negOnePow, smul_smul,
              mul_assoc, Int.units_mul_self, mul_one]
      exact (Linear.comp_units_smul _ _ _).trans h1.symm)

@[simp]
lemma linearHomComplexSingle₀Iso_hom_f_apply {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (z : ModuleCat.of k (Cochain K ((singleFunctor C 0).obj Y) i)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexSingle₀Iso k K Y).hom.f i) z) =
      (i * (i + 1) / 2).negOnePow • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z :=
  (rfl)

@[simp]
lemma linearHomComplexSingle₀Iso_inv_f_apply {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (f : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexSingle₀Iso k K Y).inv.f i) f) =
      ((i * (i + 1) / 2).negOnePow • Cochain.toSingleMk f (neg_add_cancel i) :
        ModuleCat.of k (Cochain K ((singleFunctor C 0).obj Y) i)) := by
  apply (Cochain.toSingleLinearEquiv (R := k) (K := K) (X := Y) (neg_add_cancel i)).injective
  have hinv := congrArg (fun g ↦ g.hom f)
    (HomologicalComplex.congr_hom (linearHomComplexSingle₀Iso k K Y).inv_hom_id i)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at hinv
  rw [linearHomComplexSingle₀Iso_hom_f_apply] at hinv
  have hinv' : (i * (i + 1) / 2).negOnePow •
      ((i * (i + 1) / 2).negOnePow •
        Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
          (((linearHomComplexSingle₀Iso k K Y).inv.f i).hom f)) =
      (i * (i + 1) / 2).negOnePow • (f : K.X (-i) ⟶ Y) :=
    congrArg (fun x : K.X (-i) ⟶ Y ↦ (i * (i + 1) / 2).negOnePow • x) hinv
  rw [smul_smul, Int.units_mul_self, one_smul] at hinv'
  exact hinv'.trans
    ((congrArg (fun x : K.X (-i) ⟶ Y ↦ (i * (i + 1) / 2).negOnePow • x)
        (Cochain.toSingleEquiv_toSingleMk (f : K.X (-i) ⟶ Y)
          (neg_add_cancel i)).symm).trans
      (map_zsmul_unit (Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i))
        (i * (i + 1) / 2).negOnePow _).symm)

/-- Precomposition in `K` intertwines `linearHomComplexSingle₀Iso` with `linearYonedaFunctor` on
the negated chain map. -/
@[reassoc]
theorem linearHomComplexPrecomp_linearHomComplexSingle₀Iso_hom
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (Y : C) :
    linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
        (linearHomComplexSingle₀Iso k K₁ Y).hom =
      (linearHomComplexSingle₀Iso k K₂ Y).hom ≫
        (ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op := by
  ext i (z : ModuleCat.of k (Cochain K₂ ((singleFunctor C 0).obj Y) i))
  have h1 : (((linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
      (linearHomComplexSingle₀Iso k K₁ Y).hom).f i).hom z : K₁.X (-i) ⟶ Y) =
      (i * (i + 1) / 2).negOnePow •
        (φ.f (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
    rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      linearHomComplexSingle₀Iso_hom_f_apply, toSingleLinearEquiv_linearHomComplexPrecomp_f_apply]
  have h2 : ((((linearHomComplexSingle₀Iso k K₂ Y).hom ≫
      (ChainComplex.linearYonedaFunctor k Y).map
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op).f i).hom z :
        K₁.X (-i) ⟶ Y) =
      φ.f (-i) ≫ ((i * (i + 1) / 2).negOnePow •
        Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) :=
    congrArg (φ.f (-i) ≫ ·) (linearHomComplexSingle₀Iso_hom_f_apply K₂ Y i z)
  exact h1.trans ((Linear.comp_units_smul _ _ _).symm.trans h2.symm)

/-- Postcomposition with a coefficient morphism `g : Y₁ ⟶ Y₂` intertwines
`linearHomComplexSingle₀Iso` with `ChainComplex.linearYonedaObjMap`. -/
@[reassoc]
theorem linearHomComplexPostcomp_linearHomComplexSingle₀Iso_hom
    (K : CochainComplex C ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    linearHomComplexPostcomp k K ((singleFunctor C 0).map g) ≫
        (linearHomComplexSingle₀Iso k K Y₂).hom =
      (linearHomComplexSingle₀Iso k K Y₁).hom ≫
        _root_.ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) g := by
  ext i (z : ModuleCat.of k (Cochain K ((singleFunctor C 0).obj Y₁) i))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [linearHomComplexSingle₀Iso_hom_f_apply, linearHomComplexSingle₀Iso_hom_f_apply,
    toSingleLinearEquiv_linearHomComplexPostcomp_f_apply, ← Linear.units_smul_comp]
  exact (_root_.ChainComplex.linearYonedaObjMap_f_hom_apply k (negChain K) g i _).symm

/-- **Unsigned cohomology comparison** between `linearHomComplex k K ((singleFunctor C 0).obj Y)`
and `_root_.ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y` in
degree `i`. Multiplying the map on cohomology induced by `linearHomComplexSingle₀Iso` by
`(-1)^(i(i + 1) / 2)` cancels the degree-`i` sign on cocycles while keeping naturality in both `K`
and `Y`. -/
def linearHomComplexSingle₀HomologyIso (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≅
      (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homology i :=
  (i * (i + 1) / 2).negOnePow •
    HomologicalComplex.homologyMapIso (linearHomComplexSingle₀Iso k K Y) i

@[simp]
lemma linearHomComplexSingle₀HomologyIso_hom (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplexSingle₀HomologyIso k K Y i).hom =
      (i * (i + 1) / 2).negOnePow • homologyMap (linearHomComplexSingle₀Iso k K Y).hom i :=
  (rfl)

@[simp]
lemma linearHomComplexSingle₀HomologyIso_inv (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplexSingle₀HomologyIso k K Y i).inv =
      (i * (i + 1) / 2).negOnePow • homologyMap (linearHomComplexSingle₀Iso k K Y).inv i := by
  simp [linearHomComplexSingle₀HomologyIso, Int.units_inv_eq_self]

/-- `linearHomComplexSingle₀HomologyIso` is natural with respect to precomposition by a cochain
map `φ : K₁ ⟶ K₂`. -/
@[reassoc]
theorem homologyMap_precomp_linearHomComplexSingle₀HomologyIso_hom
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (Y : C) (i : ℤ) :
    homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i ≫
        (linearHomComplexSingle₀HomologyIso k K₁ Y i).hom =
      (linearHomComplexSingle₀HomologyIso k K₂ Y i).hom ≫
        homologyMap
          (K := _root_.ChainComplex.linearYonedaObj
            (K₂.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          (L := _root_.ChainComplex.linearYonedaObj
            (K₁.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          ((ChainComplex.linearYonedaFunctor k Y).map
            (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i := by
  have hcomp := HomologicalComplex.homologyMap_comp
    (K := linearHomComplex k K₂ ((singleFunctor C 0).obj Y))
    (L := (negChain K₂).linearYonedaObj k Y) (M := (negChain K₁).linearYonedaObj k Y)
    (linearHomComplexSingle₀Iso k K₂ Y).hom
    ((ChainComplex.linearYonedaFunctor k Y).map
      (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i
  rw [linearHomComplexSingle₀HomologyIso_hom, linearHomComplexSingle₀HomologyIso_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, ← homologyMap_comp, ← hcomp,
    linearHomComplexPrecomp_linearHomComplexSingle₀Iso_hom]
  rfl

/-- `linearHomComplexSingle₀HomologyIso` is natural with respect to postcomposition by a
coefficient morphism `g : Y₁ ⟶ Y₂`. -/
@[reassoc]
theorem homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom
    (K : CochainComplex C ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ) :
    homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i ≫
        (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom =
      (linearHomComplexSingle₀HomologyIso k K Y₁ i).hom ≫
        homologyMap
          (_root_.ChainComplex.linearYonedaObjMap k
            (K.restriction ComplexShape.embeddingDownIntUpInt) g) i := by
  rw [linearHomComplexSingle₀HomologyIso_hom, linearHomComplexSingle₀HomologyIso_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, ← homologyMap_comp, ← homologyMap_comp,
    linearHomComplexPostcomp_linearHomComplexSingle₀Iso_hom]

/-- On cocycles, `linearHomComplexSingle₀HomologyIso` removes the sign `(-1)^(i(i + 1) / 2)` and
sends the class of a cocycle `φ` directly to the class of `Cochain.toSingleLinearEquiv` applied to
its underlying cochain. -/
lemma linearHomComplexSingle₀HomologyIso_hom_homologyπ {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)) :
    (linearHomComplexSingle₀HomologyIso k K Y i).hom.hom
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ) =
      (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ := by
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (linearHomComplexSingle₀Iso k K Y).hom i) φ
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hnat
  have hcyc : cyclesMap (linearHomComplexSingle₀Iso k K Y).hom i φ =
      (i * (i + 1) / 2).negOnePow • ψ := by
    apply HomologicalComplex.moduleCat_iCycles_injective
    have hi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (linearHomComplexSingle₀Iso k K Y).hom i) φ
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, linearHomComplexSingle₀Iso_hom_f_apply] at hi
    rw [map_zsmul_unit, hψ]
    exact hi
  rw [linearHomComplexSingle₀HomologyIso_hom, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, ← Units.smul_def, hnat, hcyc, map_zsmul_unit,
    negOnePow_smul_negOnePow_smul]

/-- Inverse form of `linearHomComplexSingle₀HomologyIso_hom_homologyπ`:
`(linearHomComplexSingle₀HomologyIso k K Y i).inv` sends the class of `ψ` to the class of `φ`. -/
lemma linearHomComplexSingle₀HomologyIso_inv_homologyπ {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)) :
    (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom
        ((_root_.ChainComplex.linearYonedaObj
          (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ) =
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ := by
  rw [← linearHomComplexSingle₀HomologyIso_hom_homologyπ K Y i φ ψ hψ, ← ModuleCat.comp_apply,
    Iso.hom_inv_id, ModuleCat.id_apply]

end Comparison

end TauCeti
