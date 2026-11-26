/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import TauCeti.Algebra.Homology.CochainComplex.Opposite
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.LinearYoneda
import TauCeti.Algebra.Homology.HomotopyCategory.HomComplex.Single
import TauCeti.Algebra.Homology.LinearHomComplex.Single.Basic
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Algebra.Ring.NegOnePow

/-!
# Comparison between `linearHomComplex` into a degree-zero object and `linearYonedaObj`

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear abelian category `C`, and let `Y : C`.
The `k`-linear Hom complex `Hom(K, Y[0])` (`CochainComplex.linearHomComplex`) into the complex `Y`
concentrated in degree zero is the dual complex of `K` with coefficients in `Y`: in degree `i` its
term is the module of morphisms `K⁻ⁱ ⟶ Y` (`HomComplex.Cochain.toSingleEquiv`), and its
differential is `f ↦ (-1)^(i+1) f ∘ d`.

Reading `K` as the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ` (the restriction along `n ↦ -n`, as in
Mathlib's `ChainComplex.cochainComplexEquivalence`), the dual complex is isomorphic to the linear
Yoneda complex `Hom(K⁻, Y)` (`ChainComplex.linearYonedaObj`), whose differential has no sign. The
isomorphism `CochainComplex.linearHomComplexSingleIso` multiplies by `(-1)^(i(i+1)/2)` in degree
`i`.

This file establishes `CochainComplex.linearHomComplexSingleIso`, its naturality in both `K` and
`Y`, and the unsigned cohomology comparison isomorphism
`CochainComplex.linearHomComplexSingleHomologyIso` obtained by scaling the induced cohomology map by
`(-1)^(i(i+1)/2)` again.

## Main definitions and results

* `CochainComplex.linearHomComplexSingleIso`: the isomorphism `Hom(K, Y[0]) ≅ Hom(K⁻, Y)`, with
  degreewise formulas `CochainComplex.linearHomComplexSingleIso_hom_f_apply` and
  `CochainComplex.linearHomComplexSingleIso_inv_f_apply`.
* `CochainComplex.linearHomComplexPrecomp_linearHomComplexSingleIso_hom` and
  `CochainComplex.linearHomComplexPostcomp_linearHomComplexSingleIso_hom`: naturality of
  `CochainComplex.linearHomComplexSingleIso` in `K` and `Y`.
* `CochainComplex.linearHomComplexSingleCyclesIso`,
  `CochainComplex.iCycles_linearHomComplexSingleCyclesIso_hom_apply`,
  `CochainComplex.restrictionXIso_inv_comp_iCycles_linearHomComplexSingleCyclesIso_hom_apply`:
  unsigned cocycle comparison isomorphism and its underlying-morphism formulas.
* `CochainComplex.linearHomComplexSingleHomologyIso`,
  `CochainComplex.homologyMap_precomp_linearHomComplexSingleHomologyIso_hom`,
  `CochainComplex.homologyMap_precomp_linearHomComplexSingleHomologyIso_inv`,
  `CochainComplex.homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom`,
  `CochainComplex.homologyMap_postcomp_linearHomComplexSingleHomologyIso_inv`,
  `CochainComplex.homologyπ_linearHomComplexSingleHomologyIso_hom`,
  `CochainComplex.homologyπ_linearHomComplexSingleHomologyIso_inv`,
  `CochainComplex.linearHomComplexSingleHomologyIso_hom_homologyπ`, and
  `CochainComplex.linearHomComplexSingleHomologyIso_inv_homologyπ`: unsigned cohomology comparison
  isomorphism, naturality, and cocycle formulas.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex.HomComplex Opposite TauCeti

namespace CochainComplex

variable {C : Type*} [Category* C]

variable [Abelian C] (k : Type*) [Ring k] [Linear k C]

section SingleIso

variable {k} (K : CochainComplex C ℤ) (Y : C)

/-- The sign `(-1)^(i(i+1)/2)` relating the two differentials. -/
private def homSingleSign (i : ℤ) : ℤˣ := (i * (i + 1) / 2).negOnePow

variable (k) in
/-- In degree `i`, a cochain of degree `i` from `K` to `Y` placed in degree `0` is a morphism
`K⁻ⁱ ⟶ Y`, here twisted by the sign `(-1)^(i(i+1)/2)`. -/
private def homSingleXEquiv (i : ℤ) :
    Cochain K ((singleFunctor C 0).obj Y) i ≃ₗ[k]
      ((K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :=
  (Cochain.toSingleLinearEquiv (ComplexShape.embeddingDownIntUpInt_f_add_self i)).trans
    (DistribMulAction.toLinearEquiv k _ (homSingleSign i))

/-- `CochainComplex.homSingleXEquiv` is `HomComplex.Cochain.toSingleEquiv` twisted by the sign. -/
private lemma homSingleXEquiv_apply (i : ℤ) (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    homSingleXEquiv k K Y i α =
      homSingleSign i •
        Cochain.toSingleEquiv (ComplexShape.embeddingDownIntUpInt_f_add_self i) α := by
  simp [homSingleXEquiv]

/-- The inverse of `CochainComplex.homSingleXEquiv` is `HomComplex.Cochain.toSingleMk` twisted by
the sign. -/
private lemma homSingleXEquiv_symm_apply (i : ℤ)
    (f : (K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :
    (homSingleXEquiv k K Y i).symm f =
      homSingleSign i •
        Cochain.toSingleMk f (ComplexShape.embeddingDownIntUpInt_f_add_self i) := by
  simp [homSingleXEquiv, Cochain.toSingleEquiv_symm_apply, Units.smul_def,
    Cochain.toSingleMk_smul]

variable (k) in
/-- `CochainComplex.homSingleXEquiv` as an isomorphism between the terms of degree `i` of the two
complexes. -/
private def homSingleXIso (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i ≅
      (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i :=
  (homSingleXEquiv k K Y i).toModuleIso

/-- The isomorphisms `CochainComplex.homSingleXIso` commute with the differentials. -/
private lemma homSingle_comm {k} [Ring k] [Linear k C] (i : ℤ)
    (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).d (i + 1) i ≫
        (homSingleSign i •
          Cochain.toSingleEquiv (ComplexShape.embeddingDownIntUpInt_f_add_self i) α) =
      homSingleSign (i + 1) •
        Cochain.toSingleEquiv (ComplexShape.embeddingDownIntUpInt_f_add_self (i + 1))
          (δ i (i + 1) α) := by
  rw [← cancel_epi (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f (i + 1))).inv,
    K.restriction_d_eq ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f (i + 1)) (ComplexShape.embeddingDownIntUpInt_f i),
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Units.smul_def, Preadditive.comp_zsmul]
  rw [HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv K Y
      ComplexShape.embeddingDownIntUpInt (ComplexShape.embeddingDownIntUpInt_f i)
      (neg_add_cancel i) (ComplexShape.embeddingDownIntUpInt_f_add_self i),
    HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv K Y
      ComplexShape.embeddingDownIntUpInt (ComplexShape.embeddingDownIntUpInt_f (i + 1))
      (neg_add_cancel (i + 1)) (ComplexShape.embeddingDownIntUpInt_f_add_self (i + 1))]
  have hd := toSingleLinearEquiv_linearHomComplex_d_apply (k := k) K Y i α
  rw [linearHomComplex_d_hom_apply] at hd
  simp only [Cochain.toSingleLinearEquiv_apply, AddEquiv.toFun_eq_coe] at hd
  rw [hd]
  simp only [homSingleSign, Int.negOnePow_mul_succ_div_two_succ, Units.smul_def, smul_smul,
    ← Units.val_mul]
  rw [mul_right_comm]
  simp

variable (k) in
/-- **The Hom complex into an object placed in degree zero is its linear Yoneda complex.** The
`k`-linear Hom complex from a cochain complex `K` indexed by `ℤ` to the single complex `Y[0]` is
isomorphic to `Hom(K⁻, Y)` (`ChainComplex.linearYonedaObj`), where `K⁻` is the chain complex with
`K⁻ᵢ = K⁻ⁱ` (the restriction of `K` along `n ↦ -n`). In degree `i` both terms are the morphisms
`K⁻ⁱ ⟶ Y`; the Hom complex has differential `f ↦ (-1)^(i+1) f ∘ d`, whereas the linear Yoneda
complex has differential `f ↦ f ∘ d`, so the isomorphism multiplies by `(-1)^(i(i+1)/2)` in
degree `i` (`CochainComplex.linearHomComplexSingleIso_hom_f_apply`). -/
def linearHomComplexSingleIso :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅
      _root_.ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
  Hom.isoOfComponents (homSingleXIso k K Y) (by
    rintro i _ rfl
    ext α
    exact homSingle_comm (k := k) K Y i α)

/-- In degree `i`, `CochainComplex.linearHomComplexSingleIso` sends a cochain `α` of degree `i`
to the morphism `K⁻ⁱ ⟶ Y` it consists of (`HomComplex.Cochain.toSingleEquiv`), multiplied by the
sign `(-1)^(i(i+1)/2)`. -/
lemma linearHomComplexSingleIso_hom_f_apply (i : ℤ)
    (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    (linearHomComplexSingleIso k K Y).hom.f i α =
      (i * (i + 1) / 2).negOnePow • Cochain.toSingleEquiv (neg_add_cancel i) α :=
  -- the component in degree `i` is `homSingleXEquiv`, read in `ModuleCat` through
  -- `LinearEquiv.toModuleIso`, whose underlying map is that linear equivalence by definition
  homSingleXEquiv_apply K Y i α

/-- In degree `i`, the inverse of `CochainComplex.linearHomComplexSingleIso` sends a morphism
`f : K⁻ⁱ ⟶ Y` to the cochain of degree `i` it defines (`HomComplex.Cochain.toSingleMk`),
multiplied by the sign `(-1)^(i(i+1)/2)`. -/
lemma linearHomComplexSingleIso_inv_f_apply (i : ℤ)
    (f : (K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :
    (linearHomComplexSingleIso k K Y).inv.f i f =
      (i * (i + 1) / 2).negOnePow • Cochain.toSingleMk (p := -i) f (neg_add_cancel i) :=
  -- as for `CochainComplex.linearHomComplexSingleIso_hom_f_apply`, the inverse of the component in
  -- degree `i` is the inverse of `homSingleXEquiv` by definition
  homSingleXEquiv_symm_apply K Y i f

end SingleIso

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
  refine Eq.trans ?_ (TauCeti.ChainComplex.linearYonedaFunctor_map_f_hom_apply k Y
    (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op i
    ((linearHomComplexSingleIso k K₂ Y).hom.f i z)).symm
  simp only [comp_f, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    linearHomComplexSingleIso_hom_f_apply, Quiver.Hom.unop_op,
    HomologicalComplex.restrictionMap_f, ComplexShape.embeddingDownIntUpInt_f,
    Units.smul_def, Preadditive.comp_zsmul]
  congr 2
  exact toSingleLinearEquiv_linearHomComplexPrecomp_f_apply (k := k) φ Y i z

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
  simp only [comp_f, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    linearHomComplexSingleIso_hom_f_apply,
    _root_.ChainComplex.linearYonedaObjMap_f_hom_apply,
    Units.smul_def, Preadditive.zsmul_comp]
  congr 2
  exact toSingleLinearEquiv_linearHomComplexPostcomp_f_apply K g i z

/-- **Unsigned cocycle comparison** between `linearHomComplex k K ((singleFunctor C 0).obj Y)`
and `_root_.ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y`
in degree `i`. Multiplying the map on cycles induced by `CochainComplex.linearHomComplexSingleIso`
by `(-1)^(i(i + 1) / 2)` cancels the degree-`i` sign on cocycles. -/
def linearHomComplexSingleCyclesIso (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i ≅
      (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i :=
  (i * (i + 1) / 2).negOnePow •
    HomologicalComplex.cyclesMapIso (linearHomComplexSingleIso k K Y) i

@[simp]
lemma linearHomComplexSingleCyclesIso_hom (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplexSingleCyclesIso k K Y i).hom =
      (i * (i + 1) / 2).negOnePow • cyclesMap (linearHomComplexSingleIso k K Y).hom i :=
  (rfl)

@[simp]
lemma linearHomComplexSingleCyclesIso_inv (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplexSingleCyclesIso k K Y i).inv =
      (i * (i + 1) / 2).negOnePow • cyclesMap (linearHomComplexSingleIso k K Y).inv i := by
  simp [linearHomComplexSingleCyclesIso, Int.units_inv_eq_self]

/-- On cocycles, `CochainComplex.linearHomComplexSingleCyclesIso` removes the sign
`(-1)^(i(i + 1) / 2)` and recovers the underlying morphism `K⁻ⁱ ⟶ Y` via
`HomComplex.Cochain.toSingleEquiv`, transported along `restrictionXIso`. -/
lemma iCycles_linearHomComplexSingleCyclesIso_hom_apply {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    ((_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i).hom
        ((linearHomComplexSingleCyclesIso k K Y i).hom.hom φ) =
      (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        Cochain.toSingleEquiv (neg_add_cancel i)
          (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
  rw [linearHomComplexSingleCyclesIso_hom, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, map_zsmul, moduleCat_iCycles_cyclesMap_apply, ← Units.smul_def]
  let f : (K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y :=
    (linearHomComplexSingleIso k K Y).hom.f i
      (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)
  have h1 : (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f i)).inv ≫ f =
      (i * (i + 1) / 2).negOnePow • Cochain.toSingleEquiv (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) :=
    (Category.id_comp _).trans (linearHomComplexSingleIso_hom_f_apply K Y i _)
  have h2 := congrArg (fun x ↦ (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫ ((i * (i + 1) / 2).negOnePow • x)) h1
  rw [Units.smul_def, Preadditive.comp_zsmul, Iso.hom_inv_id_assoc, ← Units.smul_def,
    Int.negOnePow_smul_negOnePow_smul] at h2
  exact h2

/-- `restrictionXIso.inv` composed with the underlying morphism of
`CochainComplex.linearHomComplexSingleCyclesIso` is `HomComplex.Cochain.toSingleEquiv` directly. -/
lemma restrictionXIso_inv_comp_iCycles_linearHomComplexSingleCyclesIso_hom_apply
    {k} [Ring k] [Linear k C] (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).inv ≫
      ((_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i).hom
          ((linearHomComplexSingleCyclesIso k K Y i).hom.hom φ) =
      Cochain.toSingleEquiv (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
  rw [iCycles_linearHomComplexSingleCyclesIso_hom_apply, Iso.inv_hom_id_assoc]

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

/-- The inverse of `CochainComplex.linearHomComplexSingleHomologyIso` is natural with respect to
precomposition by a cochain map `φ : K₁ ⟶ K₂`. -/
@[reassoc]
theorem homologyMap_precomp_linearHomComplexSingleHomologyIso_inv
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (Y : C) (i : ℤ) :
    (linearHomComplexSingleHomologyIso k K₂ Y i).inv ≫
        homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i =
      homologyMap
          (K := _root_.ChainComplex.linearYonedaObj
            (K₂.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          (L := _root_.ChainComplex.linearYonedaObj
            (K₁.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
            (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i ≫
        (linearHomComplexSingleHomologyIso k K₁ Y i).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc,
    ← homologyMap_precomp_linearHomComplexSingleHomologyIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

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

/-- The inverse of `CochainComplex.linearHomComplexSingleHomologyIso` is natural with respect to
postcomposition by a coefficient morphism `g : Y₁ ⟶ Y₂`. -/
@[reassoc]
theorem homologyMap_postcomp_linearHomComplexSingleHomologyIso_inv
    (K : CochainComplex C ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ) :
    (linearHomComplexSingleHomologyIso k K Y₁ i).inv ≫
        homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i =
      homologyMap
          (_root_.ChainComplex.linearYonedaObjMap k
            (K.restriction ComplexShape.embeddingDownIntUpInt) g) i ≫
        (linearHomComplexSingleHomologyIso k K Y₂ i).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc,
    ← homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- `CochainComplex.linearHomComplexSingleHomologyIso` intertwines `homologyπ` with
`CochainComplex.linearHomComplexSingleCyclesIso`. -/
@[reassoc]
lemma homologyπ_linearHomComplexSingleHomologyIso_hom (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i ≫
        (linearHomComplexSingleHomologyIso k K Y i).hom =
      (linearHomComplexSingleCyclesIso k K Y i).hom ≫
        (_root_.ChainComplex.linearYonedaObj
          (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i := by
  rw [linearHomComplexSingleHomologyIso_hom, linearHomComplexSingleCyclesIso_hom,
    Linear.comp_units_smul, Linear.units_smul_comp, HomologicalComplex.homologyπ_naturality]

/-- The inverse of `CochainComplex.linearHomComplexSingleHomologyIso` intertwines `homologyπ` with
the inverse of `CochainComplex.linearHomComplexSingleCyclesIso`. -/
@[reassoc]
lemma homologyπ_linearHomComplexSingleHomologyIso_inv (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ≫
        (linearHomComplexSingleHomologyIso k K Y i).inv =
      (linearHomComplexSingleCyclesIso k K Y i).inv ≫
        (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i := by
  rw [← cancel_mono (linearHomComplexSingleHomologyIso k K Y i).hom, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id,
    homologyπ_linearHomComplexSingleHomologyIso_hom, Iso.inv_hom_id_assoc]

/-- On cocycles, `CochainComplex.linearHomComplexSingleHomologyIso` removes the sign
`(-1)^(i(i + 1) / 2)` and sends the class of a cocycle `φ` directly to the class of
`Cochain.toSingleEquiv` applied to its underlying cochain, transported along `restrictionXIso`. -/
lemma linearHomComplexSingleHomologyIso_hom_homologyπ {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : ((_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i).hom ψ =
      (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        Cochain.toSingleEquiv (neg_add_cancel i)
          (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)) :
    (linearHomComplexSingleHomologyIso k K Y i).hom.hom
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ) =
      (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ := by
  have hψ' : ψ = (linearHomComplexSingleCyclesIso k K Y i).hom.hom φ :=
    HomologicalComplex.moduleCat_iCycles_injective _ _
      (hψ.trans (iCycles_linearHomComplexSingleCyclesIso_hom_apply K Y i φ).symm)
  rw [hψ', ← ModuleCat.comp_apply, homologyπ_linearHomComplexSingleHomologyIso_hom,
    ModuleCat.comp_apply]

/-- Inverse form of `CochainComplex.linearHomComplexSingleHomologyIso_hom_homologyπ`:
`(CochainComplex.linearHomComplexSingleHomologyIso k K Y i).inv` sends the class of `ψ` to the
class of `φ`. -/
lemma linearHomComplexSingleHomologyIso_inv_homologyπ {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : ((_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i).hom ψ =
      (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        Cochain.toSingleEquiv (neg_add_cancel i)
          (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)) :
    (linearHomComplexSingleHomologyIso k K Y i).inv.hom
        ((_root_.ChainComplex.linearYonedaObj
          (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ) =
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ := by
  rw [← linearHomComplexSingleHomologyIso_hom_homologyπ K Y i φ ψ hψ, ← ModuleCat.comp_apply,
    Iso.hom_inv_id, ModuleCat.id_apply]

end CochainComplex
