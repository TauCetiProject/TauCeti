/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.LinearYoneda
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

* `CochainComplex.HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv`: rewriting
  `restrictionXIso.inv` composed with `HomComplex.Cochain.toSingleEquiv`.
* `CochainComplex.linearHomComplexSingleIso`: the isomorphism `Hom(K, Y[0]) ≅ Hom(K⁻, Y)`, with
  degreewise formulas `CochainComplex.linearHomComplexSingleIso_hom_f_apply` and
  `CochainComplex.linearHomComplexSingleIso_inv_f_apply`.
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

variable {C : Type*} [Category* C]

section Preadditive

variable [Preadditive C] [HasZeroObject C] (K : CochainComplex C ℤ) (Y : C)

/-- Precomposing the morphism `(K.restriction e).X i ⟶ Y` of a cochain to `Y[q]` with the
identification `K.X p ≅ (K.restriction e).X i` gives the morphism `K.X p ⟶ Y` of the same
cochain. -/
lemma HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv {ι : Type*}
    {c : ComplexShape ι} (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff] {i : ι} {p n q : ℤ}
    (hi : e.f i = p) (h : p + n = q) (h' : e.f i + n = q)
    (α : Cochain K ((singleFunctor C q).obj Y) n) :
    (K.restrictionXIso e hi).inv ≫ Cochain.toSingleEquiv h' α =
      Cochain.toSingleEquiv h α := by
  subst hi
  -- `restrictionXIso` is defined as an `eqToIso`, which is the identity once `hi` is `rfl`
  simp [restrictionXIso]

end Preadditive

variable [Abelian C] (k : Type*) [Ring k] [Linear k C]

section SingleIso

variable {k} (K : CochainComplex C ℤ) (Y : C)

/-- The sign `(-1)^(i(i+1)/2)` relating the two differentials. -/
private def homSingleSign (i : ℤ) : ℤˣ := (i * (i + 1) / 2).negOnePow

/-- The index of `K⁻ᵢ = K⁻ⁱ` and the degree `i` add up to zero. -/
private lemma embeddingDownIntUpInt_f_add_self (i : ℤ) :
    ComplexShape.embeddingDownIntUpInt.f i + i = 0 := by
  simp

variable (k) in
/-- In degree `i`, a cochain of degree `i` from `K` to `Y` placed in degree `0` is a morphism
`K⁻ⁱ ⟶ Y`, here twisted by the sign `(-1)^(i(i+1)/2)`. -/
private def homSingleXEquiv (i : ℤ) :
    Cochain K ((singleFunctor C 0).obj Y) i ≃ₗ[k]
      ((K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :=
  (Cochain.toSingleLinearEquiv (embeddingDownIntUpInt_f_add_self i)).trans
    (DistribMulAction.toLinearEquiv k _ (homSingleSign i))

/-- `CochainComplex.homSingleXEquiv` is `HomComplex.Cochain.toSingleEquiv` twisted by the sign. -/
private lemma homSingleXEquiv_apply (i : ℤ) (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    homSingleXEquiv k K Y i α =
      homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i) α := by
  simp [homSingleXEquiv]

/-- The inverse of `CochainComplex.homSingleXEquiv` is `HomComplex.Cochain.toSingleMk` twisted by
the sign. -/
private lemma homSingleXEquiv_symm_apply (i : ℤ)
    (f : (K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶ Y) :
    (homSingleXEquiv k K Y i).symm f =
      homSingleSign i • Cochain.toSingleMk f (embeddingDownIntUpInt_f_add_self i) := by
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
private lemma homSingle_comm (i : ℤ) (α : Cochain K ((singleFunctor C 0).obj Y) i) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).d (i + 1) i ≫
        (homSingleSign i • Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self i) α) =
      homSingleSign (i + 1) •
        Cochain.toSingleEquiv (embeddingDownIntUpInt_f_add_self (i + 1)) (δ i (i + 1) α) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective α _ (embeddingDownIntUpInt_f_add_self i)
  rw [Cochain.δ_toSingleMk f (embeddingDownIntUpInt_f_add_self i) (i + 1)
    (ComplexShape.embeddingDownIntUpInt.f (i + 1)) (embeddingDownIntUpInt_f_add_self _)]
  simp [homSingleSign, Int.negOnePow_mul_succ_div_two_succ, smul_smul, mul_right_comm]

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
    exact homSingle_comm K Y i α)

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
