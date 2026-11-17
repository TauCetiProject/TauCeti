/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import TauCeti.Algebra.Homology.CochainComplex.AlternatingDifferential
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.LinearYoneda
import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Linear Hom complexes into an object placed in degree zero

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear category `C`, and let `Y : C`.
Mathlib's `CochainComplex.linearHomComplex k K ((singleFunctor C 0).obj Y)` is the cochain complex
of `k`-modules of cochains from `K` into `Y` placed in degree `0`. In any `k`-linear preadditive
category with a zero object, `CochainComplex.HomComplex.Cochain.toSingleLinearEquiv` identifies its
term in degree `i` with `(K⁻ⁱ ⟶ Y)` and its differential `i → i + 1` with
`f ↦ (-1) ^ (i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`
(`CochainComplex.toSingleLinearEquiv_linearHomComplex_d_apply`).

When `C` is abelian, regrading `K` into the chain complex
`X = K.restriction ComplexShape.embeddingDownIntUpInt` with `Xᵢ = K⁻ⁱ` and unchanged differential
identifies `linearHomComplex k K ((singleFunctor C 0).obj Y)` with
`(X.linearYonedaObj k Y).alternatingDifferential` without signs
(`CochainComplex.linearHomComplexSingleAlternatingIso`), and hence with `X.linearYonedaObj k Y`
through `CochainComplex.alternatingDifferentialIso` (`CochainComplex.linearHomComplexSingleIso`).
Twisting the induced isomorphism on degree-`i` cohomology by `(-1) ^ (i * (i + 1) / 2)` cancels
the alternating-differential sign on degree-`i` cocycles, yielding a sign-free `k`-linear
equivalence `CochainComplex.linearHomComplexSingleHomologyEquiv` natural in both `K` and `Y`.

## Main definitions

* `CochainComplex.linearHomComplexSingleAlternatingIso` and
  `CochainComplex.linearHomComplexSingleIso`: comparisons between
  `linearHomComplex k K ((singleFunctor C 0).obj Y)` and `ChainComplex.linearYonedaObj` on the
  regraded chain complex of `K`.
* `CochainComplex.linearHomComplexSingleHomologyIso` and
  `CochainComplex.linearHomComplexSingleHomologyEquiv`: the resulting sign-free cohomology
  isomorphism and `k`-linear equivalence.

## Main results

* `CochainComplex.toSingleLinearEquiv_linearHomComplex_d_apply`: degreewise formula for the
  differential of `linearHomComplex k K ((singleFunctor C 0).obj Y)`.
* `CochainComplex.linearHomComplexSingleHomologyEquiv_homologyπ`: sign-free evaluation of
  `linearHomComplexSingleHomologyEquiv` on cocycle classes.
* `CochainComplex.linearHomComplexSingleHomologyEquiv_postcomp` and
  `CochainComplex.linearHomComplexSingleHomologyEquiv_precomp`: naturality in `Y` and in `K`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Sections 1.2 and 3.6.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3.
* Mathlib's `CochainComplex.linearHomComplex`,
  `CochainComplex.HomComplex.Cochain.toSingleLinearEquiv`, and `ChainComplex.linearYonedaObj`.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian
open CochainComplex.HomComplex

namespace CochainComplex

universe w v u

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  (K : CochainComplex C ℤ) (k : Type w) [Ring k] [Linear k C]

/-- Under `Cochain.toSingleLinearEquiv`, the differential `i → i + 1` of
`linearHomComplex k K ((singleFunctor C 0).obj Y)` sends `f : K⁻ⁱ ⟶ Y` to
`(-1) ^ (i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`. -/
lemma toSingleLinearEquiv_linearHomComplex_d_apply (Y : C) (i : ℤ)
    (z : (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel (i + 1))
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom z) =
      ((i + 1).negOnePow : ℤ) •
        (K.d (-(i + 1)) (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  -- `linearHomComplex_d_hom_apply` is stated on `Cochain K _ i`, which is the carrier of the
  -- implicitly reducible object `(linearHomComplex k K _).X i`.
  erw [linearHomComplex_d_hom_apply]
  simp only [Cochain.toSingleLinearEquiv_apply, AddEquiv.toFun_eq_coe,
    Cochain.toSingleEquiv_toSingleMk,
    Cochain.δ_toSingleMk f (neg_add_cancel i) (i + 1) (-(i + 1)) (neg_add_cancel (i + 1)),
    Units.smul_def, map_zsmul]

end Preadditive

-- Mathlib's `ChainComplex.linearYonedaObj` requires `[Abelian C]` in its signature.
variable {C : Type u} [Category.{v} C] [Abelian C]

section Receiver

variable (K : CochainComplex C ℤ) (k : Type w) [Ring k] [Linear k C]

private def toSingleLinearYonedaIso (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i ≅
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i :=
  (Cochain.toSingleLinearEquiv (R := k) (X := Y) (K := K) (neg_add_cancel i)).toModuleIso

private lemma toSingleLinearYonedaIso_hom_apply (Y : C) (i : ℤ)
    (z : Cochain K ((singleFunctor C 0).obj Y) i) :
    (dsimp% only [linearHomComplex_X]
      (K.toSingleLinearYonedaIso k Y i).hom.hom z) =
      Cochain.toSingleEquiv (neg_add_cancel i) z :=
  rfl

private lemma toSingleLinearYonedaIso_inv_apply (Y : C) (i : ℤ)
    (f : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i) :
    (dsimp% only [linearHomComplex_X]
      (K.toSingleLinearYonedaIso k Y i).inv.hom f) =
      Cochain.toSingleMk f (neg_add_cancel i) :=
  rfl

/-- Degreewise `Cochain.toSingleLinearEquiv` identifies the `k`-linear Hom complex from `K` into
`Y` placed in degree `0` with the alternating-differential twist of
`ChainComplex.linearYonedaObj (K.restriction e) k Y`, where `e : n ↦ -n` regrades `K` as a chain
complex. -/
def linearHomComplexSingleAlternatingIso (Y : C) :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferential :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ K.toSingleLinearYonedaIso k Y i ≪≫
      ((ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferentialXIso i).symm)
    fun i j hij ↦ by
      obtain rfl : j = i + 1 := hij.symm
      rw [← cancel_mono ((ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferentialXIso
          (i + 1)).hom]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, alternatingDifferential_d,
        Preadditive.comp_zsmul, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
      ext z
      rw [ModuleCat.hom_zsmul, ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.smul_apply,
        LinearMap.comp_apply, LinearMap.comp_apply]
      -- Convert `ModuleCat.Hom.hom` application to `ConcreteCategory.hom` before rewriting through
      -- `linearYonedaObj_d_apply`, while the argument still has type `(linearYonedaObj _).X i`.
      erw [TauCeti.ChainComplex.linearYonedaObj_d_apply]
      rw [HomologicalComplex.restriction_d]
      -- Cross the carrier identification `linearHomComplex_X` to apply `toSingleLinearYonedaIso`.
      erw [K.toSingleLinearYonedaIso_hom_apply k Y (i + 1),
        K.toSingleLinearYonedaIso_hom_apply k Y i]
      have h := K.toSingleLinearEquiv_linearHomComplex_d_apply k Y i z
      rw [Cochain.toSingleLinearEquiv_apply, Cochain.toSingleLinearEquiv_apply,
        AddEquiv.toFun_eq_coe, AddEquiv.toFun_eq_coe] at h
      exact h.symm

@[simp]
lemma linearHomComplexSingleAlternatingIso_hom_f_apply (Y : C) (i : ℤ)
    (z : Cochain K ((singleFunctor C 0).obj Y) i) :
    ((ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferentialXIso i).hom
      (dsimp% only [linearHomComplex_X]
        ((K.linearHomComplexSingleAlternatingIso k Y).hom.f i).hom z) =
      Cochain.toSingleEquiv (neg_add_cancel i) z := by
  simp only [linearHomComplexSingleAlternatingIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    Iso.trans_hom, Iso.symm_hom]
  -- `linearHomComplex_X` turns `dsimp%` into a definitional carrier identification on `z`.
  erw [← ModuleCat.comp_apply]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact K.toSingleLinearYonedaIso_hom_apply k Y i z

@[simp]
lemma linearHomComplexSingleAlternatingIso_inv_f_apply (Y : C) (i : ℤ)
    (f : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferential.X i) :
    (dsimp% only [linearHomComplex_X]
      ((K.linearHomComplexSingleAlternatingIso k Y).inv.f i).hom f) =
      Cochain.toSingleMk
        (((ChainComplex.linearYonedaObj
          (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferentialXIso
            i).hom f) (neg_add_cancel i) := by
  simp only [linearHomComplexSingleAlternatingIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    Iso.trans_inv, Iso.symm_inv, ModuleCat.hom_comp, LinearMap.comp_apply]
  exact K.toSingleLinearYonedaIso_inv_apply k Y i _

/-- **Comparison between `linearHomComplex` into a degree-zero object and `linearYonedaObj`.**
In degree `i`, the forward map applies `Cochain.toSingleLinearEquiv (neg_add_cancel i)` twisted by
`(-1) ^ (i * (i + 1) / 2)` so as to remove the sign from the Hom-complex differential. -/
def linearHomComplexSingleIso (Y : C) :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅
      ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
  K.linearHomComplexSingleAlternatingIso k Y ≪≫
    (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferentialIso.symm

/-- `linearHomComplexSingleIso` factors through `linearHomComplexSingleAlternatingIso` and
`CochainComplex.alternatingDifferentialIso`. -/
lemma linearHomComplexSingleIso_def (Y : C) :
    K.linearHomComplexSingleIso k Y =
      K.linearHomComplexSingleAlternatingIso k Y ≪≫
        (ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt)
          k Y).alternatingDifferentialIso.symm := by
  rfl

private lemma linearHomComplexSingleIso_hom_f (Y : C) (i : ℤ) :
    (K.linearHomComplexSingleIso k Y).hom.f i =
      ((i * (i + 1) / 2).negOnePow : ℤ) • (K.toSingleLinearYonedaIso k Y i).hom := by
  simp only [linearHomComplexSingleIso, linearHomComplexSingleAlternatingIso, Iso.trans_hom,
    Iso.symm_hom, HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
    alternatingDifferentialIso_inv_f, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private lemma linearHomComplexSingleIso_inv_f (Y : C) (i : ℤ) :
    (K.linearHomComplexSingleIso k Y).inv.f i =
      ((i * (i + 1) / 2).negOnePow : ℤ) • (K.toSingleLinearYonedaIso k Y i).inv := by
  simp only [linearHomComplexSingleIso, linearHomComplexSingleAlternatingIso, Iso.trans_inv,
    Iso.symm_inv, HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_inv_f,
    alternatingDifferentialIso_hom_f, Preadditive.zsmul_comp, Iso.inv_hom_id_assoc]

@[simp]
lemma linearHomComplexSingleIso_hom_f_apply (Y : C) (i : ℤ)
    (z : Cochain K ((singleFunctor C 0).obj Y) i) :
    (dsimp% only [linearHomComplex_X]
      ((K.linearHomComplexSingleIso k Y).hom.f i).hom z) =
      ((i * (i + 1) / 2).negOnePow : ℤ) •
        Cochain.toSingleEquiv (neg_add_cancel i) z := by
  rw [linearHomComplexSingleIso_hom_f, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    toSingleLinearYonedaIso_hom_apply]
  rfl

@[simp]
lemma linearHomComplexSingleIso_inv_f_apply (Y : C) (i : ℤ)
    (f : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i) :
    (dsimp% only [linearHomComplex_X]
      ((K.linearHomComplexSingleIso k Y).inv.f i).hom f) =
      (((i * (i + 1) / 2).negOnePow : ℤ) • Cochain.toSingleMk f (neg_add_cancel i) :
        Cochain K ((singleFunctor C 0).obj Y) i) := by
  rw [linearHomComplexSingleIso_inv_f, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    toSingleLinearYonedaIso_inv_apply]

/-- `CochainComplex.linearHomComplexSingleIso` commutes with postcomposition by a coefficient
morphism `g : Y ⟶ Z`. -/
@[reassoc]
lemma linearHomComplexPostcomp_comp_linearHomComplexSingleIso_hom {Y Z : C} (g : Y ⟶ Z) :
    TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g) ≫
        (K.linearHomComplexSingleIso k Z).hom =
      (K.linearHomComplexSingleIso k Y).hom ≫
        ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) g := by
  ext i z
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  -- Each component lemma is stated on the unfolded carrier of `linearHomComplex` or
  -- `linearYonedaObj`.
  erw [ChainComplex.linearYonedaObjMap_f_hom_apply, linearHomComplexSingleIso_hom_f_apply,
    linearHomComplexSingleIso_hom_f_apply, TauCeti.linearHomComplexPostcomp_f_apply]
  rw [← Cochain.toSingleMk_postcomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk]
  exact (Preadditive.zsmul_comp f g _).symm

/-- **Sign-free cohomology isomorphism** between `linearHomComplex k K ((singleFunctor C 0).obj Y)`
and `ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y` in
degree `i`. Multiplying the homology isomorphism of `linearHomComplexSingleIso` by
`(-1) ^ (i * (i + 1) / 2)` cancels the degree-`i` alternating sign, so cocycles go directly to
their `toSingleEquiv` images. -/
def linearHomComplexSingleHomologyIso (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≅
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homology i :=
  (i * (i + 1) / 2).negOnePow •
    HomologicalComplex.homologyMapIso (K.linearHomComplexSingleIso k Y) i

/-- `linearHomComplexSingleHomologyIso` is the sign twist of `homologyMapIso` on
`linearHomComplexSingleIso`. -/
lemma linearHomComplexSingleHomologyIso_def (Y : C) (i : ℤ) :
    K.linearHomComplexSingleHomologyIso k Y i =
      (i * (i + 1) / 2).negOnePow •
        HomologicalComplex.homologyMapIso (K.linearHomComplexSingleIso k Y) i := by
  rfl

/-- `CochainComplex.linearHomComplexSingleHomologyIso` as a `k`-linear equivalence. -/
def linearHomComplexSingleHomologyEquiv (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homology i :=
  (K.linearHomComplexSingleHomologyIso k Y i).toLinearEquiv

@[simp]
lemma toLinearEquiv_linearHomComplexSingleHomologyIso (Y : C) (i : ℤ) :
    (K.linearHomComplexSingleHomologyIso k Y i).toLinearEquiv =
      K.linearHomComplexSingleHomologyEquiv k Y i := by
  rfl

@[simp]
lemma linearHomComplexSingleHomologyIso_hom_apply (Y : C) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    (K.linearHomComplexSingleHomologyIso k Y i).hom x =
      K.linearHomComplexSingleHomologyEquiv k Y i x := by
  rfl

@[simp]
lemma linearHomComplexSingleHomologyIso_inv_apply (Y : C) (i : ℤ)
    (x : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homology i) :
    (K.linearHomComplexSingleHomologyIso k Y i).inv x =
      (K.linearHomComplexSingleHomologyEquiv k Y i).symm x := by
  rfl

/-- Naturality of `linearHomComplexSingleHomologyEquiv` in `Y`. -/
lemma linearHomComplexSingleHomologyEquiv_postcomp {Y Z : C} (g : Y ⟶ Z) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K.linearHomComplexSingleHomologyEquiv k Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      homologyMap (ChainComplex.linearYonedaObjMap k
        (K.restriction ComplexShape.embeddingDownIntUpInt) g) i
        (K.linearHomComplexSingleHomologyEquiv k Y i x) := by
  simp only [linearHomComplexSingleHomologyEquiv, Iso.toLinearEquiv_apply,
    linearHomComplexSingleHomologyIso, Preadditive.smul_iso_hom,
    HomologicalComplex.homologyMapIso_hom, Units.smul_def, ← ModuleCat.comp_apply,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← homologyMap_comp,
    linearHomComplexPostcomp_comp_linearHomComplexSingleIso_hom]

end Receiver

section Morphism

variable (k : Type w) [Ring k] [Linear k C]

/-- `CochainComplex.linearHomComplexSingleIso` commutes with precomposition by a cochain map
`φ : K' ⟶ K`. -/
@[reassoc]
lemma linearHomComplexPrecomp_comp_linearHomComplexSingleIso_hom
    {K' K : CochainComplex C ℤ} (φ : K' ⟶ K) (Y : C) :
    TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
        (K'.linearHomComplexSingleIso k Y).hom =
      (K.linearHomComplexSingleIso k Y).hom ≫
        (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op := by
  ext i z
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  rw [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  -- On the right, `(linearYonedaFunctor k Y).obj (op _)` is `(restriction _).linearYonedaObj k Y`
  -- via `linearYonedaFunctor`'s `@[expose]` definition; `erw` crosses this carrier identification
  -- and applies the component evaluation lemmas.
  erw [HomologicalComplex.comp_f, ModuleCat.hom_comp]
  rw [LinearMap.comp_apply]
  erw [TauCeti.ChainComplex.linearYonedaFunctor_map_f_hom_apply,
    linearHomComplexSingleIso_hom_f_apply, linearHomComplexSingleIso_hom_f_apply,
    TauCeti.linearHomComplexPrecomp_f_apply]
  rw [Quiver.Hom.unop_op, HomologicalComplex.restrictionMap_f,
    ← Cochain.toSingleMk_precomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk]
  exact (Preadditive.comp_zsmul _ f _).symm

/-- `linearHomComplexSingleHomologyEquiv` sends the class of a cocycle `φ` to the class of the
cocycle `ψ` with underlying morphism `Cochain.toSingleEquiv (neg_add_cancel i) (iCycles φ)`, with
no sign. -/
lemma linearHomComplexSingleHomologyEquiv_homologyπ {K : CochainComplex C ℤ} {Y : C}
    (i : ℤ) (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ)) :
    K.linearHomComplexSingleHomologyEquiv k Y i
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ := by
  simp only [linearHomComplexSingleHomologyEquiv, Iso.toLinearEquiv_apply,
    linearHomComplexSingleHomologyIso, Preadditive.smul_iso_hom,
    HomologicalComplex.homologyMapIso_hom, Units.smul_def, ModuleCat.hom_zsmul,
    LinearMap.smul_apply, HomologicalComplex.moduleCat_homologyMap_homologyπ, ← map_zsmul]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simp only [map_zsmul, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, hψ]
  have hsign : ((i * (i + 1) / 2).negOnePow : ℤ) • (((i * (i + 1) / 2).negOnePow : ℤ) •
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ)) =
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
    rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  exact (congrArg (((i * (i + 1) / 2).negOnePow : ℤ) • ·)
    (K.linearHomComplexSingleIso_hom_f_apply k Y i _)).trans hsign

/-- Naturality of `linearHomComplexSingleHomologyEquiv` in `K`. -/
lemma linearHomComplexSingleHomologyEquiv_precomp {K' K : CochainComplex C ℤ}
    (φ : K' ⟶ K) (Y : C) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K'.linearHomComplexSingleHomologyEquiv k Y i
        (homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i x) =
      homologyMap
        (K := ChainComplex.linearYonedaObj
          (K.restriction ComplexShape.embeddingDownIntUpInt) k Y)
        (L := ChainComplex.linearYonedaObj
          (K'.restriction ComplexShape.embeddingDownIntUpInt) k Y)
        ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i
        (K.linearHomComplexSingleHomologyEquiv k Y i x) := by
  let ψ : ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y ⟶
      ChainComplex.linearYonedaObj
        (K'.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
    (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
      (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op
  have hcomm : TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
      (K'.linearHomComplexSingleIso k Y).hom =
      (K.linearHomComplexSingleIso k Y).hom ≫ ψ :=
    linearHomComplexPrecomp_comp_linearHomComplexSingleIso_hom k φ Y
  have hhom : homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i ≫
      (((i * (i + 1) / 2).negOnePow : ℤ) •
        homologyMap (K'.linearHomComplexSingleIso k Y).hom i) =
      (((i * (i + 1) / 2).negOnePow : ℤ) • homologyMap (K.linearHomComplexSingleIso k Y).hom i) ≫
        homologyMap ψ i := by
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← homologyMap_comp, ← homologyMap_comp,
      hcomm]
  simp only [linearHomComplexSingleHomologyEquiv, Iso.toLinearEquiv_apply,
    linearHomComplexSingleHomologyIso, Preadditive.smul_iso_hom,
    HomologicalComplex.homologyMapIso_hom, Units.smul_def, ← ModuleCat.comp_apply]
  exact congrArg (fun f ↦ f x) hhom

end Morphism

end CochainComplex
