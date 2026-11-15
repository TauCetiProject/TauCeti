/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Homology.CochainComplex.AlternatingDifferential
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.PrincipalIdealRing
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
import Mathlib.Algebra.Module.PID

/-!
# The universal coefficient sequence for cochain complexes

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear abelian category `C`, and let `Y : C`.
Mathlib's `CochainComplex.linearHomComplex k K ((singleFunctor C 0).obj Y)` is the cochain complex
of `k`-modules of cochains from `K` into `Y` placed in degree `0`. Under
`CochainComplex.HomComplex.Cochain.toSingleLinearEquiv`, its term in degree `i` is `(K⁻ⁱ ⟶ Y)` and
its differential `i → i + 1` is `f ↦ (-1) ^ (i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`.

Regrading `K` into the chain complex `X = K.restriction ComplexShape.embeddingDownIntUpInt` with
`Xᵢ = K⁻ⁱ` and unchanged differential identifies `linearHomComplex k K ((singleFunctor C 0).obj Y)`
with `(X.linearYonedaObj k Y).alternatingDifferential` without signs
(`TauCeti.CochainComplex.linearHomComplexSingle₀AlternatingIso`), and hence with
`X.linearYonedaObj k Y` through `CochainComplex.alternatingDifferentialIso`
(`TauCeti.CochainComplex.linearHomComplexSingle₀Iso`). Twisting the induced map on degree-`i`
cohomology by `(-1) ^ (i * (i + 1) / 2)` cancels the alternating-differential sign on degree-`i`
cocycles, yielding a sign-free `k`-linear equivalence
`TauCeti.CochainComplex.linearHomComplexSingle₀HomologyEquiv` that is natural in both `K` and `Y`.

Transporting `TauCeti.ChainComplex` along this equivalence and
`HomologicalComplex.restrictionHomologyIso` gives the universal coefficient sequence for cochain
complexes:

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`

when `K.cycles (1 - i)` is projective and `K.iCycles (1 - i)` and `K.iCycles (-i)` are split
monomorphisms (`TauCeti.CochainComplex.extToHomology`, `TauCeti.CochainComplex.kronecker`,
`TauCeti.CochainComplex.kroneckerSection`, `TauCeti.CochainComplex.universalCoefficientEquiv`).
Both maps in the sequence are natural in `K` and `Y`, and the chosen splitting commutes with
morphisms in `Y`. When `Y` is injective or `H¹⁻ⁱ(K)` is projective, the Kronecker map is a
`k`-linear equivalence.

For `C = ModuleCat k` and a module `M` carrying a ring action of `S` commuting with `k`, scalar
multiplication on `M` acts on `linearHomComplex` via `TauCeti.linearHomComplexPostcomp` and on
`Ext` via `CategoryTheory.Abelian.Ext.postcompOfLinear`, lifting `Hom_k(K, M)` to a cochain complex
`TauCeti.CochainComplex.bimoduleHomComplex` in `ModuleCat S`; both universal coefficient maps and
the splitting induced by `k`-linear cycle retractions preserve the `S`-action.

Over a principal ideal domain `R` with `Y = R`, when `H¹⁻ⁱ(K)` is finitely generated, `Ext¹` is
torsion while `Dual R (H⁻ⁱ(K))` is torsion-free, so the universal coefficient sequence canonically
identifies `Ext¹(H¹⁻ⁱ(K), R)` with the torsion submodule of `Hⁱ(Hom(K, R[0]))` and
`Dual R (H⁻ⁱ(K))` with the torsion-free quotient, and equates `finrank` when `H⁻ⁱ(K)` is also
finitely generated.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 3.6.5.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.3.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian
open _root_.CochainComplex _root_.CochainComplex.HomComplex
open scoped nonZeroDivisors

namespace TauCeti.CochainComplex

universe w' w v u

section Comparison

variable {C : Type u} [Category.{v} C] [Abelian C] (k : Type w) [Ring k] [Linear k C]

/-- Under `Cochain.toSingleLinearEquiv`, the differential `i → i + 1` of
`linearHomComplex k K ((singleFunctor C 0).obj Y)` sends `f : K⁻ⁱ ⟶ Y` to
`(-1) ^ (i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`. -/
lemma toSingleLinearEquiv_linearHomComplex_d_apply (K : _root_.CochainComplex C ℤ) (Y : C)
    (i : ℤ) (z : (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel (i + 1))
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom z) =
      ((i + 1).negOnePow : ℤ) •
        (K.d (-(i + 1)) (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  erw [linearHomComplex_d_hom_apply]
  simp only [Cochain.toSingleLinearEquiv_apply, AddEquiv.toFun_eq_coe,
    Cochain.toSingleEquiv_toSingleMk,
    Cochain.δ_toSingleMk f (neg_add_cancel i) (i + 1) (-(i + 1)) (neg_add_cancel (i + 1)),
    Units.smul_def, map_zsmul]

private def toSingleLinearYonedaIso (K : _root_.CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i ≅
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i :=
  (Cochain.toSingleLinearEquiv (R := k) (X := Y) (K := K) (neg_add_cancel i)).toModuleIso

/-- Degreewise `Cochain.toSingleLinearEquiv` identifies the `k`-linear Hom complex from `K` into
`Y` placed in degree `0` with the alternating-differential twist of
`ChainComplex.linearYonedaObj (K.restriction e) k Y`, where `e : n ↦ -n` regrades `K` as a chain
complex. -/
def linearHomComplexSingle₀AlternatingIso (K : _root_.CochainComplex C ℤ) (Y : C) :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferential :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ toSingleLinearYonedaIso k K Y i ≪≫
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
      exact (toSingleLinearEquiv_linearHomComplex_d_apply k K Y i z).symm

/-- **Comparison between `linearHomComplex` into a degree-zero object and `linearYonedaObj`.**
In degree `i`, the forward map applies `Cochain.toSingleLinearEquiv (neg_add_cancel i)` twisted by
`(-1) ^ (i * (i + 1) / 2)` so as to remove the sign from the Hom-complex differential. -/
def linearHomComplexSingle₀Iso (K : _root_.CochainComplex C ℤ) (Y : C) :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅
      ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
  linearHomComplexSingle₀AlternatingIso k K Y ≪≫
    (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).alternatingDifferentialIso.symm

private lemma linearHomComplexSingle₀Iso_hom_f (K : _root_.CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplexSingle₀Iso k K Y).hom.f i =
      ((i * (i + 1) / 2).negOnePow : ℤ) • (toSingleLinearYonedaIso k K Y i).hom := by
  simp only [linearHomComplexSingle₀Iso, linearHomComplexSingle₀AlternatingIso, Iso.trans_hom,
    Iso.symm_hom, HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
    alternatingDifferentialIso_inv_f, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

private lemma linearHomComplexSingle₀Iso_inv_f (K : _root_.CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplexSingle₀Iso k K Y).inv.f i =
      ((i * (i + 1) / 2).negOnePow : ℤ) • (toSingleLinearYonedaIso k K Y i).inv := by
  simp only [linearHomComplexSingle₀Iso, linearHomComplexSingle₀AlternatingIso, Iso.trans_inv,
    Iso.symm_inv, HomologicalComplex.comp_f, HomologicalComplex.Hom.isoOfComponents_inv_f,
    alternatingDifferentialIso_hom_f, Preadditive.zsmul_comp, Iso.inv_hom_id_assoc]

@[simp]
lemma linearHomComplexSingle₀Iso_hom_f_apply (K : _root_.CochainComplex C ℤ) (Y : C) (i : ℤ)
    (z : Cochain K ((singleFunctor C 0).obj Y) i) :
    (dsimp% only [linearHomComplex_X]
      ((linearHomComplexSingle₀Iso k K Y).hom.f i).hom z) =
      ((i * (i + 1) / 2).negOnePow : ℤ) •
        Cochain.toSingleEquiv (neg_add_cancel i) z := by
  change (((linearHomComplexSingle₀Iso k K Y).hom.f i).hom z) = _
  rw [linearHomComplexSingle₀Iso_hom_f, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rfl

@[simp]
lemma linearHomComplexSingle₀Iso_inv_f_apply (K : _root_.CochainComplex C ℤ) (Y : C) (i : ℤ)
    (f : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i) :
    (dsimp% only [linearHomComplex_X]
      ((linearHomComplexSingle₀Iso k K Y).inv.f i).hom f) =
      (((i * (i + 1) / 2).negOnePow : ℤ) • Cochain.toSingleMk f (neg_add_cancel i) :
        Cochain K ((singleFunctor C 0).obj Y) i) := by
  change (((linearHomComplexSingle₀Iso k K Y).inv.f i).hom f) = _
  rw [linearHomComplexSingle₀Iso_inv_f, ModuleCat.hom_zsmul, LinearMap.smul_apply]
  rfl

/-- `TauCeti.CochainComplex.linearHomComplexSingle₀Iso` commutes with precomposition by a cochain
map `φ : K' ⟶ K`. -/
@[reassoc]
lemma linearHomComplexPrecomp_comp_linearHomComplexSingle₀Iso_hom
    {K' K : _root_.CochainComplex C ℤ} (φ : K' ⟶ K) (Y : C) :
    TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
        (linearHomComplexSingle₀Iso k K' Y).hom =
      (linearHomComplexSingle₀Iso k K Y).hom ≫
        (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op := by
  ext i z
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  change (((linearHomComplexSingle₀Iso k K' Y).hom.f i).hom
      (((TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)).f i).hom
        (Cochain.toSingleMk f (neg_add_cancel i))) : K'.X (-i) ⟶ Y) =
    (φ.f (-i) : K'.X (-i) ⟶ K.X (-i)) ≫
      ((linearHomComplexSingle₀Iso k K Y).hom.f i).hom (Cochain.toSingleMk f (neg_add_cancel i))
  erw [linearHomComplexSingle₀Iso_hom_f_apply, linearHomComplexSingle₀Iso_hom_f_apply,
    TauCeti.linearHomComplexPrecomp_f_apply]
  rw [← Cochain.toSingleMk_precomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk]
  exact (Preadditive.comp_zsmul ((φ.f (-i)) : K'.X (-i) ⟶ K.X (-i)) f _).symm

/-- `TauCeti.CochainComplex.linearHomComplexSingle₀Iso` commutes with postcomposition by a
coefficient morphism `g : Y ⟶ Z`. -/
@[reassoc]
lemma linearHomComplexPostcomp_comp_linearHomComplexSingle₀Iso_hom
    (K : _root_.CochainComplex C ℤ) {Y Z : C} (g : Y ⟶ Z) :
    TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g) ≫
        (linearHomComplexSingle₀Iso k K Z).hom =
      (linearHomComplexSingle₀Iso k K Y).hom ≫
        ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) g := by
  ext i z
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  erw [ChainComplex.linearYonedaObjMap_f_hom_apply, linearHomComplexSingle₀Iso_hom_f_apply,
    linearHomComplexSingle₀Iso_hom_f_apply, TauCeti.linearHomComplexPostcomp_f_apply]
  rw [← Cochain.toSingleMk_postcomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk]
  exact (Preadditive.zsmul_comp f g _).symm

/-- **Sign-free cohomology isomorphism** between `linearHomComplex k K ((singleFunctor C 0).obj Y)`
and `ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y` in
degree `i`. Multiplying the homology isomorphism of `linearHomComplexSingle₀Iso` by
`(-1) ^ (i * (i + 1) / 2)` cancels the degree-`i` alternating sign, so cocycles go directly to
their `toSingleEquiv` images. -/
def linearHomComplexSingle₀HomologyIso (K : _root_.CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≅
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homology i :=
  (i * (i + 1) / 2).negOnePow •
    (HomologicalComplex.homologyFunctor _ _ i).mapIso (linearHomComplexSingle₀Iso k K Y)

/-- `TauCeti.CochainComplex.linearHomComplexSingle₀HomologyIso` as a `k`-linear equivalence. -/
def linearHomComplexSingle₀HomologyEquiv (K : _root_.CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homology i :=
  (linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv

/-- `linearHomComplexSingle₀HomologyEquiv` sends the class of a cocycle `φ` to the class of the
cocycle `ψ` with underlying morphism `Cochain.toSingleEquiv (neg_add_cancel i) (iCycles φ)`, with
no sign. -/
lemma linearHomComplexSingle₀HomologyEquiv_homologyπ {K : _root_.CochainComplex C ℤ} {Y : C}
    (i : ℤ) (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (ψ : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i)
    (hψ : (ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ)) :
    linearHomComplexSingle₀HomologyEquiv k K Y i
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      (ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homologyπ i ψ := by
  change ModuleCat.Hom.hom (((i * (i + 1) / 2).negOnePow : ℤ) •
    homologyMap (linearHomComplexSingle₀Iso k K Y).hom i)
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) = _
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply,
    HomologicalComplex.moduleCat_homologyMap_homologyπ, ← map_zsmul]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [map_zsmul, HomologicalComplex.moduleCat_iCycles_cyclesMap_apply, hψ]
  have hsign : ((i * (i + 1) / 2).negOnePow : ℤ) • (((i * (i + 1) / 2).negOnePow : ℤ) •
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ)) =
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
    rw [smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  exact (congrArg (((i * (i + 1) / 2).negOnePow : ℤ) • ·)
    (linearHomComplexSingle₀Iso_hom_f_apply k K Y i _)).trans hsign

/-- Naturality of `linearHomComplexSingle₀HomologyEquiv` in `K`. -/
lemma linearHomComplexSingle₀HomologyEquiv_precomp {K' K : _root_.CochainComplex C ℤ}
    (φ : K' ⟶ K) (Y : C) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingle₀HomologyEquiv k K' Y i
        (homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i x) =
      homologyMap
        (K := ChainComplex.linearYonedaObj
          (K.restriction ComplexShape.embeddingDownIntUpInt) k Y)
        (L := ChainComplex.linearYonedaObj
          (K'.restriction ComplexShape.embeddingDownIntUpInt) k Y)
        ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i
        (linearHomComplexSingle₀HomologyEquiv k K Y i x) := by
  let ψ : ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y ⟶
      ChainComplex.linearYonedaObj
        (K'.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
    (TauCeti.ChainComplex.linearYonedaFunctor k Y).map
      (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op
  have hcomm : TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y) ≫
      (linearHomComplexSingle₀Iso k K' Y).hom =
      (linearHomComplexSingle₀Iso k K Y).hom ≫ ψ :=
    linearHomComplexPrecomp_comp_linearHomComplexSingle₀Iso_hom k φ Y
  have hhom : homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i ≫
      (((i * (i + 1) / 2).negOnePow : ℤ) •
        homologyMap (linearHomComplexSingle₀Iso k K' Y).hom i) =
      (((i * (i + 1) / 2).negOnePow : ℤ) • homologyMap (linearHomComplexSingle₀Iso k K Y).hom i) ≫
        homologyMap ψ i := by
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← homologyMap_comp, ← homologyMap_comp,
      hcomm]
  exact congrArg (fun f ↦ f.hom x) hhom

/-- Naturality of `linearHomComplexSingle₀HomologyEquiv` in `Y`. -/
lemma linearHomComplexSingle₀HomologyEquiv_postcomp (K : _root_.CochainComplex C ℤ)
    {Y Z : C} (g : Y ⟶ Z) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingle₀HomologyEquiv k K Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      homologyMap (ChainComplex.linearYonedaObjMap k
        (K.restriction ComplexShape.embeddingDownIntUpInt) g) i
        (linearHomComplexSingle₀HomologyEquiv k K Y i x) := by
  change (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i ≫
      (((i * (i + 1) / 2).negOnePow : ℤ) •
        homologyMap (linearHomComplexSingle₀Iso k K Z).hom i)).hom x =
    ((((i * (i + 1) / 2).negOnePow : ℤ) • homologyMap (linearHomComplexSingle₀Iso k K Y).hom i) ≫
      homologyMap (ChainComplex.linearYonedaObjMap k
        (K.restriction ComplexShape.embeddingDownIntUpInt) g) i).hom x
  rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, ← homologyMap_comp, ← homologyMap_comp,
    linearHomComplexPostcomp_comp_linearHomComplexSingle₀Iso_hom]

end Comparison

section RegradeHelpers

variable {C : Type u} [Category.{v} C] [Abelian C]

private def regradeCyclesIso (K : _root_.CochainComplex C ℤ) {j j' : ℤ} (hj' : -j = j') :
    (K.restriction ComplexShape.embeddingDownIntUpInt).cycles j ≅ K.cycles j' :=
  K.restrictionCyclesIso ComplexShape.embeddingDownIntUpInt j (j - 1) (by simp)
    (hj' := show ComplexShape.embeddingDownIntUpInt.f j = j' by simpa using hj')
    (hk' := show ComplexShape.embeddingDownIntUpInt.f (j - 1) = j' + 1 by simp; omega)
    (by simp)

private def regradeHomologyIso (K : _root_.CochainComplex C ℤ) {j j' : ℤ} (hj' : -j = j') :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homology j ≅ K.homology j' :=
  K.restrictionHomologyIso ComplexShape.embeddingDownIntUpInt (j + 1) j (j - 1) (by simp) (by simp)
    (hi' := show ComplexShape.embeddingDownIntUpInt.f (j + 1) = j' - 1 by simp; omega)
    (hj' := show ComplexShape.embeddingDownIntUpInt.f j = j' by simpa using hj')
    (hk' := show ComplexShape.embeddingDownIntUpInt.f (j - 1) = j' + 1 by simp; omega)
    (by simp) (by simp)

@[reassoc]
private lemma homologyπ_regradeHomologyIso_hom (K : _root_.CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ j ≫
        (regradeHomologyIso K hj').hom =
      (regradeCyclesIso K hj').hom ≫ K.homologyπ j' :=
  K.homologyπ_restrictionHomologyIso_hom _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
private lemma homologyπ_regradeHomologyIso_inv (K : _root_.CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') :
    K.homologyπ j' ≫ (regradeHomologyIso K hj').inv =
      (regradeCyclesIso K hj').inv ≫
        (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ j :=
  K.homologyπ_restrictionHomologyIso_inv _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
private lemma regradeHomologyIso_hom_naturality {K' K : _root_.CochainComplex C ℤ} (φ : K' ⟶ K)
    {j j' : ℤ} (hj' : -j = j') :
    homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) j ≫
        (regradeHomologyIso K hj').hom =
      (regradeHomologyIso K' hj').hom ≫ homologyMap φ j' := by
  have hj'' : ComplexShape.embeddingDownIntUpInt.f j = j' := by simpa using hj'
  rw [← cancel_epi ((K'.restriction ComplexShape.embeddingDownIntUpInt).homologyπ j),
    homologyπ_naturality_assoc, homologyπ_regradeHomologyIso_hom,
    homologyπ_regradeHomologyIso_hom_assoc, homologyπ_naturality,
    ← Category.assoc, ← Category.assoc]
  refine congrArg (· ≫ K.homologyπ j') ?_
  rw [← cancel_mono (K.iCycles j'), Category.assoc, Category.assoc, regradeCyclesIso,
    restrictionCyclesIso_hom_iCycles, cyclesMap_i_assoc, cyclesMap_i,
    regradeCyclesIso, restrictionCyclesIso_hom_iCycles_assoc,
    restrictionMap_f'_assoc φ ComplexShape.embeddingDownIntUpInt hj'',
    Iso.inv_hom_id, Category.comp_id]

private lemma projective_restriction_cycles (K : _root_.CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') [Projective (K.cycles j')] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles j) :=
  Projective.of_iso (regradeCyclesIso K hj').symm inferInstance

private lemma projective_restriction_homology (K : _root_.CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') [Projective (K.homology j')] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).homology j) :=
  Projective.of_iso (regradeHomologyIso K hj').symm inferInstance

private lemma isSplitMono_restriction_iCycles (K : _root_.CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') [IsSplitMono (K.iCycles j')] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles j) :=
  ⟨⟨{ retraction := (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (show ComplexShape.embeddingDownIntUpInt.f j = j' by simpa using hj')).hom ≫
        retraction (K.iCycles j') ≫ (regradeCyclesIso K hj').inv
      id := by
        let e := ComplexShape.embeddingDownIntUpInt
        have hj'' : e.f j = j' := by simpa [e] using hj'
        have hk'' : e.f (j - 1) = j' + 1 := by simp [e]; omega
        rw [← restrictionCyclesIso_hom_iCycles_assoc K e j (j - 1) (by simp) hj'' hk'' (by simp),
          IsSplitMono.id_assoc]
        exact (regradeCyclesIso K hj').hom_inv_id }⟩⟩

end RegradeHelpers

section UniversalCoefficient

variable {C : Type u} [Category.{v} C] [Abelian C]

section Ring

variable {k : Type w} [Ring k] [Linear k C] {K : _root_.CochainComplex C ℤ} {Y : C}

variable (k K Y) in
/-- **The Kronecker map for cochain complexes**
`Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`: evaluates a degree-`i` cohomology class of
`linearHomComplex k K ((singleFunctor C 0).obj Y)` on homology classes of `K` in degree `-i`. -/
def kronecker (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i →ₗ[k] (K.homology (-i) ⟶ Y) :=
  Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).inv ∘ₗ
    TauCeti.ChainComplex.kronecker k (K.restriction ComplexShape.embeddingDownIntUpInt) Y i ∘ₗ
    (linearHomComplexSingle₀HomologyEquiv k K Y i).toLinearMap

/-- **The Kronecker map on cocycle classes**: evaluating the class of a cocycle `φ` on the class
of a cycle of `K` in degree `-i` applies `Cochain.toSingleEquiv (neg_add_cancel i)` to `φ`. -/
@[reassoc (attr := simp)]
lemma kronecker_homologyπ (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    K.homologyπ (-i) ≫
        kronecker k K Y i ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      K.iCycles (-i) ≫ Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
  let X : ChainComplex C ℤ := K.restriction ComplexShape.embeddingDownIntUpInt
  have hd' : K.d (-(i + 1)) (-i) ≫ Cochain.toSingleEquiv (neg_add_cancel i)
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) = 0 := by
    have h0 := (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_d_iCycles_apply i
      (i + 1) φ
    have h1 := toSingleLinearEquiv_linearHomComplex_d_apply k K Y i
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ)
    rw [h0, map_zero] at h1
    have h2 := congrArg (((i + 1).negOnePow : ℤ) • ·) h1.symm
    simpa only [Cochain.toSingleLinearEquiv_apply, AddEquiv.toFun_eq_coe, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, smul_zero] using h2
  have hd : (X.linearYonedaObj k Y).d i (i + 1)
      (Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ)) = 0 := hd'
  let ψ := (X.linearYonedaObj k Y).moduleCatCyclesMk _ (i + 1) (by simp) hd
  have hψ := (X.linearYonedaObj k Y).iCycles_moduleCatCyclesMk i _ (i + 1) (by simp) hd
  rw [kronecker, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    linearHomComplexSingle₀HomologyEquiv_homologyπ k i φ ψ hψ, Linear.leftComp_apply,
    homologyπ_regradeHomologyIso_inv_assoc, TauCeti.ChainComplex.kronecker_homologyπ]
  dsimp only [regradeCyclesIso, X]
  refine (K.restrictionCyclesIso_inv_iCycles_assoc _ _ _ _ _ _ _ _).trans
    (congrArg (K.iCycles (-i) ≫ ·) ?_)
  rw [restrictionXIso, eqToIso.inv]
  erw [eqToHom_refl, Category.id_comp]
  exact hψ

/-- **Naturality of the cochain Kronecker map** in the source cochain complex `K`. -/
lemma kronecker_naturality {K' : _root_.CochainComplex C ℤ} (φ : K' ⟶ K) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    kronecker k K' Y i
        (homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i x) =
      homologyMap φ (-i) ≫ kronecker k K Y i x := by
  have hnat := regradeHomologyIso_hom_naturality φ (rfl : -i = -i)
  have hinv : (regradeHomologyIso K' (rfl : -i = -i)).inv ≫
      homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i =
      homologyMap φ (-i) ≫ (regradeHomologyIso K (rfl : -i = -i)).inv := by
    rw [← cancel_epi (regradeHomologyIso K' (rfl : -i = -i)).hom, Iso.hom_inv_id_assoc,
      ← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [kronecker, LinearMap.comp_apply, LinearEquiv.coe_coe, Linear.leftComp_apply,
    linearHomComplexSingle₀HomologyEquiv_precomp, TauCeti.ChainComplex.kronecker_naturality,
    reassoc_of% hinv]

/-- **Coefficient naturality of the cochain Kronecker map** in `Y`. -/
lemma kronecker_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    kronecker k K Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      kronecker k K Y i x ≫ g := by
  simp only [kronecker, LinearMap.comp_apply, LinearEquiv.coe_coe, Linear.leftComp_apply,
    linearHomComplexSingle₀HomologyEquiv_postcomp,
    TauCeti.ChainComplex.kronecker_coefficient_naturality, Category.assoc]

/-- For an injective object `Y`, the cochain Kronecker map is bijective. -/
theorem kronecker_bijective [Injective Y] (i : ℤ) :
    Function.Bijective (kronecker k K Y i) := by
  have h1 : Function.Bijective (Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).inv) :=
    ⟨fun a b h ↦ (cancel_epi _).1 h, fun f ↦ ⟨(regradeHomologyIso K rfl).hom ≫ f, by simp⟩⟩
  exact h1.comp ((TauCeti.ChainComplex.kronecker_bijective i).comp
    (linearHomComplexSingle₀HomologyEquiv k K Y i).bijective)

variable (k K Y) in
/-- For an injective object `Y`, the cochain Kronecker map as a `k`-linear equivalence
`Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def kroneckerEquiv [Injective Y] (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (kronecker k K Y i) (kronecker_bijective i)

@[simp]
lemma kroneckerEquiv_apply [Injective Y] (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    kroneckerEquiv k K Y i x = kronecker k K Y i x :=
  (rfl)

variable (k K Y) in
/-- **The splitting of the cochain universal coefficient sequence**: given a retraction of
`K.iCycles (-i)`, the `k`-linear right inverse `(H⁻ⁱ(K) ⟶ Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` of
`TauCeti.CochainComplex.kronecker` sending `g` to the cocycle class induced by the retraction on
cycles. -/
def kroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    (K.homology (-i) ⟶ Y) →ₗ[k] (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  have := isSplitMono_restriction_iCycles K (rfl : -i = -i)
  (linearHomComplexSingle₀HomologyEquiv k K Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.kroneckerSection k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i ∘ₗ
    Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).hom

/-- `TauCeti.CochainComplex.kroneckerSection` is a right inverse of `kronecker`. -/
@[simp]
lemma kronecker_kroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y) :
    kronecker k K Y i (kroneckerSection k K Y i g) = g := by
  have := isSplitMono_restriction_iCycles K (rfl : -i = -i)
  simp only [kronecker, kroneckerSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, TauCeti.ChainComplex.kronecker_kroneckerSection,
    Linear.leftComp_apply, Iso.inv_hom_id_assoc]

/-- `TauCeti.CochainComplex.kroneckerSection` commutes with postcomposition by a coefficient
morphism `g : Y ⟶ Z`, for the same chosen retraction of `K.iCycles (-i)`. -/
lemma kroneckerSection_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (f : K.homology (-i) ⟶ Y) :
    homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i
        (kroneckerSection k K Y i f) =
      kroneckerSection k K Z i (f ≫ g) := by
  have := isSplitMono_restriction_iCycles K (rfl : -i = -i)
  apply (linearHomComplexSingle₀HomologyEquiv k K Z i).injective
  rw [linearHomComplexSingle₀HomologyEquiv_postcomp]
  simp only [kroneckerSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, TauCeti.ChainComplex.kroneckerSection_coefficient_naturality,
    Linear.leftComp_apply, Category.assoc]

/-- When `K.iCycles (-i)` is a split monomorphism, `TauCeti.CochainComplex.kronecker` is
surjective. -/
theorem kronecker_surjective_of_isSplitMono (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    Function.Surjective (kronecker k K Y i) :=
  fun g ↦ ⟨kroneckerSection k K Y i g, kronecker_kroneckerSection i g⟩

/-- **The cochain universal coefficient theorem with projective `(1 - i)`-th cohomology**: when
`K.iCycles (1 - i)` and `K.iCycles (-i)` split and `K.homology (1 - i)` is projective, the
Kronecker map `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` is bijective over any ring `k`. -/
theorem kronecker_bijective_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    Function.Bijective (kronecker k K Y i) := by
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (rfl : -i = -i)
  have := projective_restriction_homology K (neg_sub i 1)
  have h1 : Function.Bijective (Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).inv) :=
    ⟨fun a b h ↦ (cancel_epi _).1 h, fun f ↦ ⟨(regradeHomologyIso K rfl).hom ≫ f, by simp⟩⟩
  exact h1.comp
    ((TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_of_add_one_eq
      (sub_add_cancel i 1)).comp (linearHomComplexSingle₀HomologyEquiv k K Y i).bijective)

variable (k K Y) in
/-- When `K.iCycles (1 - i)` and `K.iCycles (-i)` split and `K.homology (1 - i)` is projective,
the cochain Kronecker map as a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def kroneckerEquivOfProjectiveHomology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (kronecker k K Y i) (kronecker_bijective_of_projective_homology i)

@[simp]
lemma kroneckerEquivOfProjectiveHomology_apply (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    kroneckerEquivOfProjectiveHomology k K Y i x = kronecker k K Y i x :=
  (rfl)

/-- If `K.iCycles (1 - i)` and `K.iCycles (-i)` split, `K.homology (1 - i)` is projective, and
`K.homology (-i)` vanishes, then `Hⁱ(Hom(K, Y[0]))` vanishes. -/
theorem isZero_homology_linearHomComplex_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] (hi : IsZero (K.homology (-i))) :
    IsZero ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) := by
  have : Subsingleton (K.homology (-i) ⟶ Y) := ⟨hi.eq_of_src⟩
  have := (kronecker_bijective_of_projective_homology (k := k) (K := K) (Y := Y) i).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end Ring

section CommRing

variable {k : Type w} [CommRing k] [Linear k C] [HasExt.{w'} C]
  {K : _root_.CochainComplex C ℤ} {Y : C}

variable (k K Y) in
/-- **The `Ext` term of the cochain universal coefficient sequence**: the `k`-linear map
`Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))`, defined when `K.cycles (1 - i)` is projective and
`K.iCycles (1 - i)` is a split monomorphism. -/
def extToHomology (i : ℤ) [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Ext.{w'} (K.homology (1 - i)) Y 1 →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  (linearHomComplexSingle₀HomologyEquiv k K Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.extToHomology.{w'} k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i (i - 1) ∘ₗ
    (TauCeti.extLinearEquivOfIso k (regradeHomologyIso K (neg_sub i 1)).symm
      (Iso.refl Y) 1).toLinearMap

/-- **Injectivity in the cochain universal coefficient sequence**: the map
`Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem extToHomology_injective (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Function.Injective (extToHomology.{w'} k K Y i) := by
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  exact (linearHomComplexSingle₀HomologyEquiv k K Y i).symm.injective.comp
    ((TauCeti.ChainComplex.extToHomology_injective (sub_add_cancel i 1)).comp
      (TauCeti.extLinearEquivOfIso k (regradeHomologyIso K (neg_sub i 1)).symm
        (Iso.refl Y) 1).injective)

/-- **Exactness in the middle of the cochain universal coefficient sequence**: the kernel of
`TauCeti.CochainComplex.kronecker` in degree `i` is the image of
`TauCeti.CochainComplex.extToHomology`. -/
theorem exact_extToHomology_kronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Function.Exact (extToHomology.{w'} k K Y i) (kronecker k K Y i) := by
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  have hex := TauCeti.ChainComplex.exact_extToHomology_kronecker.{w'} (k := k)
    (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y) (sub_add_cancel i 1)
  have hinj : Function.Injective (Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).inv) :=
    fun a b h ↦ (cancel_epi _).1 h
  intro x
  rw [kronecker, LinearMap.comp_apply, LinearMap.comp_apply,
    (map_eq_zero_iff _ hinj), LinearEquiv.coe_coe, hex]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨TauCeti.extLinearEquivOfIso k (regradeHomologyIso K (neg_sub i 1)) (Iso.refl Y) 1 e, ?_⟩
    apply (linearHomComplexSingle₀HomologyEquiv k K Y i).injective
    simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, extLinearEquivOfIso_apply, Iso.refl_hom, Iso.symm_inv,
      Ext.comp_mk₀_id, ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.mk₀_id_comp, he]
  · rintro ⟨e, rfl⟩
    refine ⟨TauCeti.extLinearEquivOfIso k (regradeHomologyIso K (neg_sub i 1)).symm
      (Iso.refl Y) 1 e, ?_⟩
    simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

/-- **Naturality of `TauCeti.CochainComplex.extToHomology` in `K`**: pulling an extension back
along `homologyMap φ (1 - i)` and including it in cohomology agrees with including first and
pulling back along `φ`. -/
lemma extToHomology_naturality {K' : _root_.CochainComplex C ℤ} (φ : K' ⟶ K) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Projective (K'.cycles (1 - i))] [IsSplitMono (K'.iCycles (1 - i))]
    (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    extToHomology.{w'} k K' Y i ((Ext.mk₀ (homologyMap φ (1 - i))).comp e (zero_add 1)) =
      homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i
        (extToHomology.{w'} k K Y i e) := by
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  have := projective_restriction_cycles K' (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K' (neg_sub i 1)
  apply (linearHomComplexSingle₀HomologyEquiv k K' Y i).injective
  rw [linearHomComplexSingle₀HomologyEquiv_precomp]
  simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← TauCeti.ChainComplex.extToHomology_naturality]
  congr 1
  simp only [extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1), Ext.mk₀_comp_mk₀,
    regradeHomologyIso_hom_naturality]

/-- **Coefficient naturality of `TauCeti.CochainComplex.extToHomology` in `Y`**. -/
lemma extToHomology_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    extToHomology.{w'} k K Z i (e.comp (Ext.mk₀ g) (add_zero 1)) =
      homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i
        (extToHomology.{w'} k K Y i e) := by
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  apply (linearHomComplexSingle₀HomologyEquiv k K Z i).injective
  rw [linearHomComplexSingle₀HomologyEquiv_postcomp]
  simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← TauCeti.ChainComplex.extToHomology_coefficient_naturality]
  congr 1
  simp only [extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)]

variable (k K Y) in
/-- **The split decomposition of the cochain universal coefficient sequence**:
`Hⁱ(Hom(K, Y[0])) ≃ₗ[k] Ext¹(H¹⁻ⁱ(K), Y) × (H⁻ⁱ(K) ⟶ Y)`, built from
`TauCeti.CochainComplex.extToHomology`, `TauCeti.CochainComplex.kronecker`, and
`TauCeti.CochainComplex.kroneckerSection`. It depends on the chosen retraction of
`K.iCycles (-i)`, and commutes with coefficient morphisms `Y ⟶ Z`. -/
def universalCoefficientEquiv (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      Ext.{w'} (K.homology (1 - i)) Y 1 × (K.homology (-i) ⟶ Y) :=
  ((exact_extToHomology_kronecker.{w'} (k := k) (K := K) (Y := Y) i).splitSurjectiveEquiv
    (extToHomology_injective i)
    ⟨kroneckerSection k K Y i, LinearMap.ext (kronecker_kroneckerSection i)⟩).1

@[simp]
lemma universalCoefficientEquiv_symm_inl (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    (universalCoefficientEquiv.{w'} k K Y i).symm (e, 0) = extToHomology.{w'} k K Y i e :=
  (LinearMap.congr_fun
    ((exact_extToHomology_kronecker.{w'} (k := k) (K := K) (Y := Y) i).splitSurjectiveEquiv
      (extToHomology_injective i) _).property.left e).symm

@[simp]
lemma universalCoefficientEquiv_symm_inr (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y) :
    (universalCoefficientEquiv.{w'} k K Y i).symm (0, g) = kroneckerSection k K Y i g :=
  LinearMap.congr_fun (congrArg Subtype.val
    (((exact_extToHomology_kronecker.{w'} (k := k) (K := K) (Y := Y) i).splitSurjectiveEquiv
      (extToHomology_injective i)).left_inv
      ⟨kroneckerSection k K Y i, LinearMap.ext (kronecker_kroneckerSection i)⟩)) g

lemma universalCoefficientEquiv_symm_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : Ext.{w'} (K.homology (1 - i)) Y 1 × (K.homology (-i) ⟶ Y)) :
    (universalCoefficientEquiv.{w'} k K Y i).symm x =
      extToHomology.{w'} k K Y i x.1 + kroneckerSection k K Y i x.2 := by
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, universalCoefficientEquiv_symm_inl, universalCoefficientEquiv_symm_inr]

@[simp]
lemma universalCoefficientEquiv_apply_snd (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    (universalCoefficientEquiv.{w'} k K Y i x).2 = kronecker k K Y i x :=
  (LinearMap.congr_fun
    ((exact_extToHomology_kronecker.{w'} (k := k) (K := K) (Y := Y) i).splitSurjectiveEquiv
      (extToHomology_injective i) _).property.right x).symm

/-- For a fixed retraction of `K.iCycles (-i)`, the splitting
`TauCeti.CochainComplex.universalCoefficientEquiv` commutes with postcomposition by any coefficient
morphism `g : Y ⟶ Z`. -/
lemma universalCoefficientEquiv_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    universalCoefficientEquiv.{w'} k K Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      ((universalCoefficientEquiv.{w'} k K Y i x).1.comp (Ext.mk₀ g) (add_zero 1),
        (universalCoefficientEquiv.{w'} k K Y i x).2 ≫ g) := by
  apply (universalCoefficientEquiv.{w'} k K Z i).symm.injective
  rw [LinearEquiv.symm_apply_apply, universalCoefficientEquiv_symm_apply,
    extToHomology_coefficient_naturality, ← kroneckerSection_coefficient_naturality,
    ← map_add, ← universalCoefficientEquiv_symm_apply i, LinearEquiv.symm_apply_apply]

end CommRing

end UniversalCoefficient

section BimoduleCoefficients

section Ring

variable (k : Type u) [Ring k] (S : Type*) [Ring S]
  (M : Type u) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]
  (K : _root_.CochainComplex (ModuleCat.{u} k) ℤ)

/-- **The `(k, S)`-bimodule Hom cochain complex** in `ModuleCat S`: in degree `i` it is the
`S`-module `K.X (-i) →ₗ[k] M`, with differential `f ↦ (-1) ^ (i + 1) • (f ∘ₗ K.d (-j) (-i))`. -/
def bimoduleHomComplex : _root_.CochainComplex (ModuleCat.{u} S) ℤ where
  X i := ModuleCat.of S ((K.X (-i)) →ₗ[k] M)
  d i j := ModuleCat.ofHom
    { toFun f := ((i + 1).negOnePow : ℤ) • (f.comp (K.d (-j) (-i)).hom)
      map_add' f g := by rw [LinearMap.add_comp, smul_add]
      map_smul' s f := by
        ext x
        simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply]
        exact smul_comm _ _ _ }
  shape i j hij := by
    ext f x
    have hd : K.d (-j) (-i) = 0 := K.shape _ _ (by simp [ComplexShape.up_Rel] at hij ⊢; omega)
    simp [hd]
  d_comp_d' i j l _ _ := by
    ext f x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.smul_apply, HomologicalComplex.d_comp_d_apply, map_zero, smul_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The degree-`i` carrier of `bimoduleHomComplex` is the `S`-module `K.X (-i) →ₗ[k] M`. -/
def bimoduleHomComplexXIso (i : ℤ) :
    (bimoduleHomComplex k S M K).X i ≅ ModuleCat.of S (K.X (-i) →ₗ[k] M) :=
  Iso.refl _

/-- Evaluation of the differential of `bimoduleHomComplex` under `bimoduleHomComplexXIso`. -/
@[simp]
lemma bimoduleHomComplex_d_apply (i : ℤ) (f : K.X (-i) →ₗ[k] M) :
    (bimoduleHomComplexXIso k S M K (i + 1)).hom.hom
      (((bimoduleHomComplex k S M K).d i (i + 1)).hom
        ((bimoduleHomComplexXIso k S M K i).inv.hom f)) =
      ((i + 1).negOnePow : ℤ) • f.comp (K.d (-(i + 1)) (-i)).hom := by
  rfl

end Ring

section CommRing

variable (k : Type u) [CommRing k] (S : Type*) [Ring S]
  (M : Type u) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- Scalar multiplication by `s : S` on `M` as a `k`-linear endomorphism of `ModuleCat.of k M`. -/
private def coeffScalarHom (s : S) : ModuleCat.of k M ⟶ ModuleCat.of k M :=
  have := SMulCommClass.symm k S M
  ModuleCat.ofHom (DistribSMul.toLinearMap k M s)

@[simp]
private lemma coeffScalarHom_apply (s : S) (m : M) : (coeffScalarHom k S M s).hom m = s • m :=
  (rfl)

variable (K : _root_.CochainComplex (ModuleCat.{u} k) ℤ)

/-- Scalar multiplication by `s : S` on `M` as a cochain endomorphism of
`linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M))`, defined via
`TauCeti.linearHomComplexPostcomp`. -/
def linearHomComplexSingleScalarHom (s : S) :
    linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M)) ⟶
      linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M)) :=
  TauCeti.linearHomComplexPostcomp k K
    ((singleFunctor (ModuleCat.{u} k) 0).map (coeffScalarHom k S M s))

/-- Under `Cochain.toSingleEquiv (neg_add_cancel i)`, `linearHomComplexSingleScalarHom` acts
pointwise as `s • f` on `K.X (-i) →ₗ[k] M`. -/
@[simp]
lemma toSingleEquiv_linearHomComplexSingleScalarHom_f_apply (s : S) (i : ℤ)
    (z : Cochain K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M)) i) :
    ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i)
        (dsimp% only [linearHomComplex_X]
          ((linearHomComplexSingleScalarHom k S M K s).f i).hom z)) =
      s • ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i) z) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  change ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i)
    (((TauCeti.linearHomComplexPostcomp k K
      ((singleFunctor _ 0).map (coeffScalarHom k S M s))).f i).hom
        (Cochain.toSingleMk f (neg_add_cancel i)))) = _
  erw [TauCeti.linearHomComplexPostcomp_f_apply]
  rw [← Cochain.toSingleMk_postcomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk]
  rfl

/-- **The `S`-action on the cohomology of `linearHomComplex`** into `M` placed in degree `0`,
induced by `TauCeti.linearHomComplexPostcomp` applied to scalar multiplication on `M`. -/
def linearHomComplexSingleHomologyAction (i : ℤ) :
    S →+* Module.End k
      ((linearHomComplex k K
        ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M))).homology i) where
  toFun s := (homologyMap (linearHomComplexSingleScalarHom k S M K s) i).hom
  map_one' := by
    have h1 : coeffScalarHom k S M 1 = 𝟙 _ := by ext m; exact one_smul S m
    ext x
    simp [linearHomComplexSingleScalarHom, h1]
  map_mul' r s := by
    -- In `Module.End`, `(f * g) x = f (g x)`, matching `s ≫ r` in `ModuleCat`.
    have hmul : coeffScalarHom k S M (r * s) =
        coeffScalarHom k S M s ≫ coeffScalarHom k S M r := by
      ext m
      exact mul_smul r s m
    ext x
    simp [linearHomComplexSingleScalarHom, hmul, TauCeti.linearHomComplexPostcomp_comp,
      homologyMap_comp]
  map_zero' := by
    have h0 : linearHomComplexSingleScalarHom k S M K 0 = 0 := by
      have hc : coeffScalarHom k S M 0 = 0 := by ext m; exact zero_smul S m
      ext j z
      obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-j) (neg_add_cancel j)
      change (((TauCeti.linearHomComplexPostcomp k K
        ((singleFunctor _ 0).map (coeffScalarHom k S M 0))).f j).hom _) = 0
      erw [TauCeti.linearHomComplexPostcomp_f_apply]
      rw [← Cochain.toSingleMk_postcomp, hc, comp_zero, Cochain.toSingleMk_zero]
    ext x
    simp [h0]
  map_add' r s := by
    have hadd : linearHomComplexSingleScalarHom k S M K (r + s) =
        linearHomComplexSingleScalarHom k S M K r + linearHomComplexSingleScalarHom k S M K s := by
      have hc : coeffScalarHom k S M (r + s) =
          coeffScalarHom k S M r + coeffScalarHom k S M s := by
        ext m
        exact add_smul r s m
      ext j z
      obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-j) (neg_add_cancel j)
      simp only [linearHomComplexSingleScalarHom, HomologicalComplex.add_f_apply,
        ModuleCat.hom_add, LinearMap.add_apply]
      erw [TauCeti.linearHomComplexPostcomp_f_apply, TauCeti.linearHomComplexPostcomp_f_apply,
        TauCeti.linearHomComplexPostcomp_f_apply]
      rw [← Cochain.toSingleMk_postcomp, ← Cochain.toSingleMk_postcomp,
        ← Cochain.toSingleMk_postcomp, hc, Preadditive.comp_add, Cochain.toSingleMk_add]
    ext x
    simp [hadd, homologyMap_add]

@[simp]
lemma linearHomComplexSingleHomologyAction_apply (i : ℤ) (s : S)
    (x : (linearHomComplex k K
      ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M))).homology i) :
    linearHomComplexSingleHomologyAction k S M K i s x =
      homologyMap (linearHomComplexSingleScalarHom k S M K s) i x := by
  simp [linearHomComplexSingleHomologyAction]

/-- Forgetting scalar actions identifies `linearHomComplex k K ((singleFunctor _ 0).obj M)` with
`bimoduleHomComplex k S M K` as cochain complexes of abelian groups. -/
def forget₂BimoduleHomComplexIso :
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M))) ≅
      ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (bimoduleHomComplex k S M K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ AddEquiv.toAddCommGrpIso
      ((Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)).toAddEquiv.trans
        ModuleCat.homAddEquiv))
    fun i j hij ↦ by
      obtain rfl : j = i + 1 := hij.symm
      ext z
      apply LinearMap.ext
      intro x
      have h := congrArg (fun φ ↦ ModuleCat.Hom.hom φ x)
        (toSingleLinearEquiv_linearHomComplex_d_apply k K (ModuleCat.of k M) i z).symm
      rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
        Cochain.toSingleLinearEquiv_apply, Cochain.toSingleLinearEquiv_apply] at h
      exact h

@[simp]
lemma forget₂BimoduleHomComplexIso_hom_f_apply (i : ℤ)
    (z : Cochain K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M)) i) :
    (dsimp% only [Functor.mapHomologicalComplex_obj_X, linearHomComplex_X, ModuleCat.forget₂_obj]
      (bimoduleHomComplexXIso k S M K i).hom.hom
        (((forget₂BimoduleHomComplexIso k S M K).hom.f i) z)) =
      ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i) z) := by
  rfl

/-- `TauCeti.CochainComplex.kronecker` commutes with the `S`-scalar actions on cohomology and on
`K.homology (-i) →ₗ[k] M`. -/
lemma kronecker_scalar (i : ℤ) (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    (kronecker k K (ModuleCat.of k M) i
        (linearHomComplexSingleHomologyAction k S M K i s x)).hom =
      s • (kronecker k K (ModuleCat.of k M) i x).hom := by
  rw [linearHomComplexSingleHomologyAction_apply, linearHomComplexSingleScalarHom,
    kronecker_coefficient_naturality]
  rfl

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`, `TauCeti.CochainComplex.kroneckerSection`
commutes with the `S`-scalar action. -/
lemma kroneckerSection_scalar (i : ℤ) [IsSplitMono (K.iCycles (-i))] (s : S)
    (f : K.homology (-i) →ₗ[k] M) :
    kroneckerSection k K (ModuleCat.of k M) i (ModuleCat.ofHom (s • f)) =
      linearHomComplexSingleHomologyAction k S M K i s
        (kroneckerSection k K (ModuleCat.of k M) i (ModuleCat.ofHom f)) :=
  (kroneckerSection_coefficient_naturality (coeffScalarHom k S M s) i (ModuleCat.ofHom f)).symm

/-- **The `S`-action on `Extⁿ(A, M)`** induced by functoriality of `Ext` in the target module. -/
def extScalarAction (A : ModuleCat.{u} k) (n : ℕ) :
    S →+* Module.End k (Ext.{u} A (ModuleCat.of k M) n) where
  toFun s := Ext.postcompOfLinear (Ext.mk₀ (coeffScalarHom k S M s)) k A (add_zero n)
  map_one' := by
    have h1 : coeffScalarHom k S M 1 = 𝟙 _ := by ext m; exact one_smul S m
    ext e
    simp [h1]
  map_mul' r s := by
    have hmul : coeffScalarHom k S M (r * s) =
        coeffScalarHom k S M s ≫ coeffScalarHom k S M r := by
      ext m
      exact mul_smul r s m
    ext e
    change e.comp (Ext.mk₀ (coeffScalarHom k S M (r * s))) (add_zero n) =
      (e.comp (Ext.mk₀ (coeffScalarHom k S M s)) (add_zero n)).comp
        (Ext.mk₀ (coeffScalarHom k S M r)) (add_zero n)
    rw [hmul, ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc _ _ _ (add_zero n) (zero_add 0) (add_zero n)]
  map_zero' := by
    have h0 : coeffScalarHom k S M 0 = 0 := by ext m; exact zero_smul S m
    ext e
    simp [h0]
  map_add' r s := by
    have hadd : coeffScalarHom k S M (r + s) =
        coeffScalarHom k S M r + coeffScalarHom k S M s := by
      ext m
      exact add_smul r s m
    ext e
    simp [hadd, Ext.mk₀_add]

@[simp]
lemma extScalarAction_apply (A : ModuleCat.{u} k) (n : ℕ) (s : S)
    (e : Ext.{u} A (ModuleCat.of k M) n) :
    have := SMulCommClass.symm k S M
    extScalarAction k S M A n s e =
      e.comp (Ext.mk₀ (ModuleCat.ofHom (DistribSMul.toLinearMap k M s))) (add_zero n) := by
  simp [extScalarAction, coeffScalarHom]

/-- `TauCeti.CochainComplex.extToHomology` commutes with the `S`-scalar actions on `Ext¹` and on
the cohomology of `linearHomComplex`. -/
lemma extToHomology_scalar (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] (s : S)
    (e : Ext.{u} (K.homology (1 - i)) (ModuleCat.of k M) 1) :
    extToHomology.{u} k K (ModuleCat.of k M) i (extScalarAction k S M (K.homology (1 - i)) 1 s e) =
      linearHomComplexSingleHomologyAction k S M K i s
        (extToHomology.{u} k K (ModuleCat.of k M) i e) :=
  extToHomology_coefficient_naturality (coeffScalarHom k S M s) i e

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`, the universal coefficient splitting
`TauCeti.CochainComplex.universalCoefficientEquiv` commutes with the `S`-scalar actions on both
factors. -/
lemma universalCoefficientEquiv_scalar (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    universalCoefficientEquiv.{u} k K (ModuleCat.of k M) i
        (linearHomComplexSingleHomologyAction k S M K i s x) =
      (extScalarAction k S M (K.homology (1 - i)) 1 s
          (universalCoefficientEquiv.{u} k K (ModuleCat.of k M) i x).1,
        ModuleCat.ofHom (s • (universalCoefficientEquiv.{u} k K (ModuleCat.of k M) i x).2.hom)) :=
  universalCoefficientEquiv_coefficient_naturality (coeffScalarHom k S M s) i x

end CommRing

section CommRingScalar

variable (k : Type u) [CommRing k] (S : Type*) [CommRing S]
  (M : Type u) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]
  (K : _root_.CochainComplex (ModuleCat.{u} k) ℤ)

/-- Over a commutative ring `S`, `forget₂BimoduleHomComplexIso` intertwines
`linearHomComplexSingleScalarHom k S M K s` with scalar multiplication `s • 𝟙 _` on
`bimoduleHomComplex k S M K`. -/
@[reassoc]
lemma map_linearHomComplexSingleScalarHom_comp_forget₂BimoduleHomComplexIso (s : S) :
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (linearHomComplexSingleScalarHom k S M K s) ≫
      (forget₂BimoduleHomComplexIso k S M K).hom =
    (forget₂BimoduleHomComplexIso k S M K).hom ≫
      ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (s • 𝟙 (bimoduleHomComplex k S M K)) := by
  ext i z
  exact toSingleEquiv_linearHomComplexSingleScalarHom_f_apply k S M K s i z

end CommRingScalar

end BimoduleCoefficients

section PrincipalIdealDomain

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

/-- Over a principal ideal domain, `Ext^{n + 1}(A, Y)` is a torsion `R`-module whenever `A` is
finitely generated: the torsion-free quotient `A ⧸ torsion R A` is finite free, so restricting to
`torsion R A` is injective on `Ext^{n + 1}` and `torsion R A` is killed by a single nonzero
scalar. -/
private theorem isTorsion_ext_succ_of_finite (A Y : ModuleCat.{u} R) [Module.Finite R A] (n : ℕ) :
    Module.IsTorsion R (Ext.{u} A Y (n + 1)) := by
  let T := Submodule.torsion R A
  let Q := A ⧸ T
  have : Module.Free R Q := Module.free_of_finite_type_torsion_free'
  have : Projective (ModuleCat.of R Q) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis R Q)
  let S : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (ModuleCat.ofHom T.subtype) (ModuleCat.ofHom T.mkQ) (by ext; simp)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.moduleCat_exact_iff _).2 fun x hx ↦
        ⟨⟨x, (Submodule.Quotient.mk_eq_zero T).1 hx⟩, rfl⟩
      mono_f := (ModuleCat.mono_iff_injective _).2 T.injective_subtype
      epi_g := (ModuleCat.epi_iff_surjective _).2 T.mkQ_surjective }
  obtain ⟨r, hr_ann, hr_mem⟩ :=
    Submodule.annihilator_top_inter_nonZeroDivisors (Submodule.torsion_isTorsion (R := R) (M := A))
  have hrT : r • (𝟙 (ModuleCat.of R T) : ModuleCat.of R T ⟶ ModuleCat.of R T) = 0 := by
    ext x
    exact congrArg Subtype.val (Submodule.mem_annihilator.1 hr_ann x Submodule.mem_top)
  have hrSf : r • S.f = 0 := by
    rw [← Category.id_comp S.f, ← Linear.smul_comp, hrT, zero_comp]
  intro e
  refine ⟨⟨r, hr_mem⟩, ?_⟩
  have hex := TauCeti.exact_precompOfLinear R hS Y (n + 1)
  have hzero : Ext.precompOfLinear (Ext.mk₀ S.f) R Y (zero_add (n + 1)) (r • e) = 0 := by
    change (Ext.mk₀ S.f).comp (r • e) (zero_add (n + 1)) = 0
    rw [Ext.comp_smul, ← Ext.smul_comp, ← Ext.mk₀_smul, hrSf, Ext.mk₀_zero, Ext.zero_comp]
  obtain ⟨q, hq⟩ := (hex (r • e)).1 hzero
  rw [Ext.eq_zero_of_projective q, map_zero] at hq
  exact hq.symm

/-- Over a principal ideal domain, a finitely generated module and its `R`-dual have the same
`finrank`. -/
private theorem finrank_dual_eq_of_finite (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    Module.finrank R (Module.Dual R M) = Module.finrank R M := by
  let T := Submodule.torsion R M
  let Q := M ⧸ T
  have : Module.Free R Q := Module.free_of_finite_type_torsion_free'
  have hker : ∀ φ : Module.Dual R M, T ≤ LinearMap.ker φ := fun φ x ⟨r, hr⟩ ↦ by
    rw [LinearMap.mem_ker]
    have h0 : (r : R) • φ x = 0 := by
      rw [← map_smul, ← Submonoid.smul_def, hr, map_zero]
    exact (smul_eq_zero.1 h0).resolve_left (nonZeroDivisors.coe_ne_zero r)
  let eDual : Module.Dual R M ≃ₗ[R] Module.Dual R Q :=
    { toFun φ := T.liftQ φ (hker φ)
      invFun ψ := ψ.comp T.mkQ
      left_inv φ := LinearMap.ext fun _ ↦ rfl
      right_inv ψ := LinearMap.ext fun q ↦ Submodule.Quotient.induction_on T q fun _ ↦ rfl
      map_add' φ₁ φ₂ := LinearMap.ext fun q ↦ Submodule.Quotient.induction_on T q fun _ ↦ rfl
      map_smul' r φ := LinearMap.ext fun q ↦ Submodule.Quotient.induction_on T q fun _ ↦ rfl }
  exact eDual.finrank_eq.trans
    ((Module.Free.chooseBasis R Q).toDualEquiv.symm.finrank_eq.trans
      (finrank_quotient_eq_of_le_torsion le_rfl))

variable (K : _root_.CochainComplex (ModuleCat.{u} R) ℤ)

/-- Over a principal ideal domain, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)`
splits, and `H¹⁻ⁱ(K)` is finitely generated, the image of `extToHomology` in `Hⁱ(Hom(K, R[0]))` is
its torsion submodule. -/
theorem range_extToHomology_eq_torsion (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    LinearMap.range (extToHomology.{u} R K (ModuleCat.of R R) i) =
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) := by
  have htor := isTorsion_ext_succ_of_finite (K.homology (1 - i)) (ModuleCat.of R R) 0
  have hex := exact_extToHomology_kronecker.{u} (k := R) (K := K) (Y := ModuleCat.of R R) i
  refine le_antisymm ?_ ?_
  · rintro _ ⟨e, rfl⟩
    obtain ⟨r, hr⟩ := @htor e
    exact ⟨r, by rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, hr, map_zero]⟩
  · intro x ⟨r, hr⟩
    refine (hex x).1 ?_
    ext y
    have h0 : (r : R) • (kronecker R K (ModuleCat.of R R) i x).hom y = 0 := by
      rw [← LinearMap.smul_apply, ← ModuleCat.hom_smul, ← map_smul, ← Submonoid.smul_def, hr,
        map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact (smul_eq_zero.1 h0).resolve_left (nonZeroDivisors.coe_ne_zero r)

/-- **Canonical torsion identification for the dual cochain complex over a PID**: `extToHomology`
restricts to a canonical `R`-linear equivalence
`Ext¹(H¹⁻ⁱ(K), R) ≃ₗ[R] torsion R (Hⁱ(Hom(K, R[0])))`. -/
def extEquivTorsion (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    Ext.{u} (K.homology (1 - i)) (ModuleCat.of R R) 1 ≃ₗ[R]
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) :=
  (LinearEquiv.ofInjective (extToHomology.{u} R K (ModuleCat.of R R) i)
    (extToHomology_injective i)).trans
    (LinearEquiv.ofEq _ _ (range_extToHomology_eq_torsion K i))

@[simp]
lemma coe_extEquivTorsion_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))]
    (e : Ext.{u} (K.homology (1 - i)) (ModuleCat.of R R) 1) :
    (extEquivTorsion K i e :
      (linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).homology i) =
      extToHomology.{u} R K (ModuleCat.of R R) i e := by
  simp [extEquivTorsion]

private lemma ker_homLinearEquiv_comp_kronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    LinearMap.ker ((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
        kronecker R K (ModuleCat.of R R) i) =
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) := by
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
    (exact_extToHomology_kronecker.{u} (k := R) (K := K)
      (Y := ModuleCat.of R R) i).linearMap_ker_eq,
    range_extToHomology_eq_torsion]

/-- **Canonical torsion-free quotient identification for the dual cochain complex over a PID**:
the Kronecker map descends to a canonical `R`-linear equivalence
`Hⁱ(Hom(K, R[0])) ⧸ torsion ≃ₗ[R] Module.Dual R (H⁻ⁱ(K))`. -/
def modTorsionEquivDual (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] [Module.Finite R (K.homology (1 - i))] :
    ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).homology i ⧸
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i)) ≃ₗ[R]
      Module.Dual R (K.homology (-i)) :=
  (Submodule.quotEquivOfEq _ _ (ker_homLinearEquiv_comp_kronecker K i).symm).trans
    (((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
        kronecker R K (ModuleCat.of R R) i).quotKerEquivOfSurjective
      ((ModuleCat.homLinearEquiv (R := R) (S := R)).surjective.comp
        (kronecker_surjective_of_isSplitMono i)))

@[simp]
lemma modTorsionEquivDual_mk (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] [Module.Finite R (K.homology (1 - i))]
    (x : (linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))).homology i) :
    modTorsionEquivDual K i (Submodule.Quotient.mk x) =
      (kronecker R K (ModuleCat.of R R) i x).hom := by
  simp [modTorsionEquivDual]
  rfl

/-- Over a principal ideal domain, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` and
`K.iCycles (-i)` split, and `H¹⁻ⁱ(K)` and `H⁻ⁱ(K)` are finitely generated, `Hⁱ(Hom(K, R[0]))` and
`H⁻ⁱ(K)` have the same `finrank`. -/
theorem finrank_homology_linearHomComplex_single₀ (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    [Module.Finite R (K.homology (1 - i))] [Module.Finite R (K.homology (-i))] :
    Module.finrank R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) =
      Module.finrank R (K.homology (-i)) :=
  (finrank_quotient_eq_of_le_torsion le_rfl).symm.trans
    ((modTorsionEquivDual K i).finrank_eq.trans (finrank_dual_eq_of_finite (K.homology (-i))))

end PrincipalIdealDomain

end TauCeti.CochainComplex
