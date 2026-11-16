/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import TauCeti.Algebra.Homology.LinearHomComplex.Basic
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
import TauCeti.Algebra.Homology.Embedding.Restriction.Surjective
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.LinearAlgebra.Exact

/-!
# The universal coefficient theorem for `linearHomComplex` into a degree-zero object

For a `ℤ`-indexed cochain complex `K` in a `k`-linear abelian category `C` and an object `Y : C`,
`CochainComplex.linearHomComplex k K ((singleFunctor C 0).obj Y)` has degree-`i` cochains
identified with `K.X (-i) ⟶ Y` via `Cochain.toSingleLinearEquiv (neg_add_cancel i)`, with
differential `f ↦ (-1)^(i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`
(`TauCeti.toSingleLinearEquiv_linearHomComplex_d_apply`).

Reindexing `K` along `n ↦ -n` (`ComplexShape.embeddingDownIntUpInt`) gives a chain complex `K'`
whose unsigned dual `K'.linearYonedaObj k Y` is naturally isomorphic to `linearHomComplex k K Y[0]`
after scaling degree `i` by `(-1)^(i(i + 1) / 2)` (`TauCeti.linearHomComplexSingle₀Iso`).
Scaling the induced cohomology isomorphism by `(-1)^(i(i + 1) / 2)` again cancels the sign on
cocycles while preserving naturality in `K` and `Y` (`TauCeti.linearHomComplexSingle₀HomologyIso`).

When `k` is commutative (`[CommRing k]`) and `C` has `Ext` (`[HasExt C]`), transporting the
chain-complex universal coefficient sequence (`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`)
yields, for `i + j = 1` (i.e. `j = 1 - i`), the split short exact sequence

`0 ⟶ Ext¹(Hʲ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`

when `Zʲ(K)` is projective and `Z⁻ⁱ(K) ⟶ K⁻ⁱ`, `Zʲ(K) ⟶ Kʲ` split. Both maps are natural in `K`
and `Y`; the splitting (`TauCeti.cochainKroneckerSection`) is natural in `Y` (non-naturality in `K`
is proved in `TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.NonNaturality`).

## Main definitions and results

* `TauCeti.toSingleLinearEquiv_linearHomComplex_d_apply`,
  `TauCeti.toSingleLinearEquiv_linearHomComplexPrecomp_f_apply`, and
  `TauCeti.toSingleLinearEquiv_linearHomComplexPostcomp_f_apply`: differential and functoriality
  formulas in degree `i`.
* `TauCeti.linearHomComplexSingle₀Iso` and `TauCeti.linearHomComplexSingle₀HomologyIso`: signed
  complex comparison and unsigned cohomology comparison with `linearYonedaObj`.
* `TauCeti.cochainKronecker`, `TauCeti.cochainKroneckerEquiv`,
  `TauCeti.cochainKroneckerEquivOfProjectiveHomology`, `TauCeti.cochainKroneckerSection`:
  Kronecker evaluation, its isomorphisms, and its splitting section.
* `TauCeti.cochainExtToHomology` and `TauCeti.cochainUniversalCoefficientEquiv`: the `Ext¹`
  inclusion, extension evaluation, exactness, naturality, and direct-product decomposition.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 3.6.5.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex Opposite
  Abelian

universe w v u

namespace TauCeti

section Differential

variable {C : Type u} [Category.{v} C] [Preadditive C] {k : Type*} [Ring k] [Linear k C]

/-- **The differential of `linearHomComplex` into a degree-zero object.** Under the degreewise
identification `Cochain.toSingleLinearEquiv (neg_add_cancel _)`, the differential from degree `i` to
degree `i + 1` sends `f : K.X (-i) ⟶ Y` to `(-1)^(i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`. -/
theorem toSingleLinearEquiv_linearHomComplex_d_apply [HasZeroObject C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (z : (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel (i + 1))
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom z) =
      (i + 1).negOnePow •
        (K.d (-(i + 1)) (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
  have hz := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  rw [linearHomComplex_d_hom_apply, ← hz,
    Cochain.δ_toSingleMk _ (neg_add_cancel i) (i + 1) (-(i + 1)) (neg_add_cancel (i + 1))]
  simp [Cochain.toSingleLinearEquiv]

/-- Under `Cochain.toSingleLinearEquiv`, precomposition in `linearHomComplex` into a degree-zero
object acts by precomposing with `φ.f (-i)`. -/
lemma toSingleLinearEquiv_linearHomComplexPrecomp_f_apply [HasZeroObject C]
    {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (Y : C) (i : ℤ)
    (z : (linearHomComplex k K₂ ((singleFunctor C 0).obj Y)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)).f i).hom z) =
      φ.f (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z := by
  have hz := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  rw [linearHomComplexPrecomp_f_apply, ← hz, ← Cochain.toSingleMk_precomp]
  simp [Cochain.toSingleLinearEquiv]

/-- Under `Cochain.toSingleLinearEquiv`, postcomposition in `linearHomComplex` into a degree-zero
object acts by postcomposing with `g`. -/
lemma toSingleLinearEquiv_linearHomComplexPostcomp_f_apply [HasZeroObject C]
    (K : CochainComplex C ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ)
    (z : (linearHomComplex k K ((singleFunctor C 0).obj Y₁)).X i) :
    Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplexPostcomp k K ((singleFunctor C 0).map g)).f i).hom z) =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z ≫ g := by
  have hz := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  rw [linearHomComplexPostcomp_f_apply, ← hz, ← Cochain.toSingleMk_postcomp]
  simp [Cochain.toSingleLinearEquiv]

end Differential

section Comparison

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reindexing a `ℤ`-indexed cochain complex `K` along `n ↦ -n` as a chain complex. -/
private abbrev negChain (K : CochainComplex C ℤ) : ChainComplex C ℤ :=
  K.restriction ComplexShape.embeddingDownIntUpInt

private lemma surjective_embeddingDownIntUpInt_f :
    Function.Surjective ComplexShape.embeddingDownIntUpInt.f :=
  neg_involutive.surjective

private lemma restrictionXIso_hom_comp (K : CochainComplex C ℤ) (i : ℤ) {Z : C}
    (g : K.X (-i) ⟶ Z) :
    (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫ g = g :=
  Category.id_comp g

variable (k : Type*) [Ring k] [Linear k C]

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

section Kronecker

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type*} [Ring k] [Linear k C]
  {K : CochainComplex C ℤ} {Y : C}

variable (k K Y) in
/-- **The Kronecker map for `linearHomComplex` into a degree-zero object**: the `k`-linear map
`Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` evaluating cohomology classes of cochains on homology
classes of `K` in degree `-i`. -/
def cochainKronecker (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i →ₗ[k] (K.homology (-i) ⟶ Y) :=
  (Linear.homCongr k (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
      (Iso.refl Y)).toLinearMap.comp <|
    (ChainComplex.kronecker k (negChain K) Y i).comp
      (linearHomComplexSingle₀HomologyIso k K Y i).hom.hom

/-- **The Kronecker map on cocycle classes**: evaluating the cohomology class of a cocycle `φ` on
the homology class of a cycle in degree `-i` applies the underlying morphism of `φ` to the cycle,
with no sign. -/
@[reassoc (attr := simp)]
lemma homologyπ_cochainKronecker (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    K.homologyπ (-i) ≫ cochainKronecker k K Y i
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ) =
      K.iCycles (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
  set X : _root_.ChainComplex C ℤ := negChain K
  set g : K.X (-i) ⟶ Y := Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
    (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)
  set f : X.X i ⟶ Y := (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
    (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫ g
  have hf : X.d ((ComplexShape.up ℤ).next i) i ≫ f = 0 := by
    have h0 : ((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) = 0 :=
      ConcreteCategory.congr_hom
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles_d i (i + 1)) φ
    have hd := toSingleLinearEquiv_linearHomComplex_d_apply (k := k) K Y i
      (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)
    rw [h0, map_zero] at hd
    have hdg : K.d (-(i + 1)) (-i) ≫ g = 0 := by
      simpa [g, smul_smul] using congrArg ((i + 1).negOnePow • ·) hd.symm
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i + 1) by simp)]
    dsimp only [X, negChain, f]
    rw [K.restriction_d_eq ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f (i + 1)) (ComplexShape.embeddingDownIntUpInt_f i),
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hdg, comp_zero]
  let ψ := ChainComplex.cocycleOfComp k Y f hf (𝟙 Y)
  have hψ : (X.linearYonedaObj k Y).iCycles i ψ = g := by
    rw [ChainComplex.iCycles_cocycleOfComp, Category.comp_id]
    exact restrictionXIso_hom_comp K i g
  rw [cochainKronecker, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
    linearHomComplexSingle₀HomologyIso_hom_homologyπ K Y i φ ψ hψ,
    HomologicalComplex.homologyπ_restrictionHomologyIsoOfSurjective_inv_assoc,
    ChainComplex.kronecker_homologyπ, ChainComplex.iCycles_cocycleOfComp, Category.comp_id,
    HomologicalComplex.restrictionCyclesIsoOfSurjective_inv_iCycles_assoc, Iso.inv_hom_id_assoc]

/-- **Naturality of `cochainKronecker` in the complex**: pulling back along `φ : K₁ ⟶ K₂` and
evaluating on homology is pushing homology forward along `φ` and evaluating. -/
theorem cochainKronecker_naturality {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (i : ℤ)
    (x : (linearHomComplex k K₂ ((singleFunctor C 0).obj Y)).homology i) :
    cochainKronecker k K₁ Y i
        ((homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom x) =
      homologyMap φ (-i) ≫ cochainKronecker k K₂ Y i x := by
  simp only [cochainKronecker, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← ModuleCat.comp_apply,
    homologyMap_precomp_linearHomComplexSingle₀HomologyIso_hom k φ Y i, ModuleCat.comp_apply,
    ChainComplex.kronecker_naturality,
    ← cancel_epi (K₁.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)).hom,
    Iso.hom_inv_id_assoc, ← Category.assoc,
    ← HomologicalComplex.homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom
      ComplexShape.embeddingDownIntUpInt surjective_embeddingDownIntUpInt_f φ i (-i)
      (ComplexShape.embeddingDownIntUpInt_f i),
    Category.assoc, Iso.hom_inv_id_assoc]

/-- **Naturality of `cochainKronecker` in the coefficient object**: postcomposing with `g : Y₁ ⟶ Y₂`
commutes with `cochainKronecker`. -/
theorem cochainKronecker_coefficient_naturality {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y₁)).homology i) :
    cochainKronecker k K Y₂ i
        ((homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom x) =
      cochainKronecker k K Y₁ i x ≫ g := by
  simp only [cochainKronecker, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← ModuleCat.comp_apply,
    homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom k K g i, ModuleCat.comp_apply,
    ChainComplex.kronecker_coefficient_naturality, Category.assoc]

/-- **The universal coefficient theorem for injective coefficients**: when `Y` is injective,
`cochainKronecker` is bijective in every degree. -/
theorem cochainKronecker_bijective [Injective Y] (i : ℤ) :
    Function.Bijective (cochainKronecker k K Y i) := by
  rw [cochainKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (Linear.homCongr k (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
      (Iso.refl Y)).bijective.comp <|
    (ChainComplex.kronecker_bijective (k := k) (X := negChain K) (Y := Y) i).comp
      (linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv.bijective

variable (k K Y) in
/-- **The Kronecker equivalence for injective coefficients**: for an injective object `Y`,
`cochainKronecker` is a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def cochainKroneckerEquiv [Injective Y] (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (cochainKronecker k K Y i) (cochainKronecker_bijective i)

@[simp]
lemma cochainKroneckerEquiv_apply [Injective Y] (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    cochainKroneckerEquiv k K Y i x = cochainKronecker k K Y i x :=
  (rfl)

/-- **The universal coefficient theorem with projective cohomology in degree `1 - i`**: when
`i + j = 1`, the cycle inclusions in degrees `j` and `-i` split, and `Hʲ(K)` is projective,
`cochainKronecker` in degree `i` is bijective over any ring `k`. -/
theorem cochainKronecker_bijective_of_projective_homology {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] [Projective (K.homology j)] :
    Function.Bijective (cochainKronecker k K Y i) := by
  have hji : ComplexShape.embeddingDownIntUpInt.f (i - 1) = j := by
    rw [ComplexShape.embeddingDownIntUpInt_f]; omega
  have := K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)
  have := K.projective_restriction_homology_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  rw [cochainKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (Linear.homCongr k (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
      (Iso.refl Y)).bijective.comp <|
    (ChainComplex.kronecker_bijective_of_projective_homology_of_add_one_eq
      (k := k) (X := negChain K) (Y := Y) (show i - 1 + 1 = i by omega)).comp
        (linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv.bijective

variable (k K Y) in
/-- **The Kronecker equivalence with projective cohomology in degree `1 - i`**: for `i + j = 1`,
when `K.iCycles j` and `K.iCycles (-i)` split and `K.homology j` is projective, `cochainKronecker`
is a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def cochainKroneckerEquivOfProjectiveHomology {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] [Projective (K.homology j)] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (cochainKronecker k K Y i)
    (cochainKronecker_bijective_of_projective_homology hij)

@[simp]
lemma cochainKroneckerEquivOfProjectiveHomology_apply {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] [Projective (K.homology j)]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    cochainKroneckerEquivOfProjectiveHomology k K Y hij x = cochainKronecker k K Y i x :=
  (rfl)

/-- **Vanishing of dual cohomology**: for `i + j = 1`, when the cycle inclusions `K.iCycles j` and
`K.iCycles (-i)` split, `Hʲ(K)` is projective, and `H⁻ⁱ(K)` vanishes, degree-`i` cohomology of
`linearHomComplex k K ((singleFunctor C 0).obj Y)` vanishes. -/
theorem isZero_homology_linearHomComplex_of_projective_homology {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] [Projective (K.homology j)]
    (hi : IsZero (K.homology (-i))) :
    IsZero ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) := by
  have : Subsingleton (K.homology (-i) ⟶ Y) := ⟨hi.eq_of_src⟩
  have := (cochainKronecker_bijective_of_projective_homology (k := k) (K := K) (Y := Y)
    hij).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private lemma negChain_d_comp_retraction_iCycles_comp_homologyπ (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    (negChain K).d ((ComplexShape.up ℤ).next i) i ≫
        (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) = 0 := by
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
    K.restriction_d_eq ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f (i + 1)) (ComplexShape.embeddingDownIntUpInt_f i),
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← K.toCycles_i, Category.assoc,
    IsSplitMono.id_assoc, toCycles_comp_homologyπ, comp_zero]

variable (k K Y) in
/-- **Chosen splitting of `cochainKronecker`**: given a retraction of `K.iCycles (-i)`, the
`k`-linear right inverse of `cochainKronecker` sending `g : H⁻ⁱ(K) ⟶ Y` to the cohomology class of
the cocycle `K⁻ⁱ ⟶ Z⁻ⁱ(K) ⟶ H⁻ⁱ(K) ⟶ Y`. -/
def cochainKroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    (K.homology (-i) ⟶ Y) →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom.comp <|
    ChainComplex.homologyClassOfComp k Y (X := negChain K)
      ((K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        retraction (K.iCycles (-i)) ≫ K.homologyπ (-i))
      (negChain_d_comp_retraction_iCycles_comp_homologyπ K i)

/-- `cochainKroneckerSection k K Y i g` is the cohomology class of any cocycle with underlying
morphism `retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) ≫ g`. -/
lemma cochainKroneckerSection_apply (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hφ : Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) =
      retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) ≫ g) :
    cochainKroneckerSection k K Y i g =
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ := by
  let ψ := ChainComplex.cocycleOfComp k Y (X := negChain K)
    ((K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
      retraction (K.iCycles (-i)) ≫ K.homologyπ (-i))
    (negChain_d_comp_retraction_iCycles_comp_homologyπ K i) g
  have hψ : ((negChain K).linearYonedaObj k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    rw [ChainComplex.iCycles_cocycleOfComp, Category.assoc, Category.assoc, hφ]
    exact restrictionXIso_hom_comp K i _
  rw [cochainKroneckerSection, LinearMap.comp_apply,
    ChainComplex.homologyClassOfComp_eq _ _ g ψ (ChainComplex.iCycles_cocycleOfComp _ _ g)]
  exact linearHomComplexSingle₀HomologyIso_inv_homologyπ K Y i φ ψ hψ

/-- `cochainKroneckerSection` is a right inverse of `cochainKronecker`. -/
@[simp]
lemma cochainKronecker_cochainKroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y) :
    cochainKronecker k K Y i (cochainKroneckerSection k K Y i g) = g := by
  simp only [cochainKronecker, cochainKroneckerSection, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply, ← cancel_epi (K.homologyπ (-i)),
    HomologicalComplex.homologyπ_restrictionHomologyIsoOfSurjective_inv_assoc,
    ChainComplex.homologyπ_kronecker_homologyClassOfComp,
    HomologicalComplex.restrictionCyclesIsoOfSurjective_inv_iCycles_assoc,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, IsSplitMono.id_assoc]

/-- **Surjectivity of `cochainKronecker`** when `K.iCycles (-i)` is a split monomorphism. -/
theorem cochainKronecker_surjective_of_isSplitMono (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    Function.Surjective (cochainKronecker k K Y i) :=
  fun g ↦ ⟨cochainKroneckerSection k K Y i g, cochainKronecker_cochainKroneckerSection i g⟩

/-- **Coefficient naturality of `cochainKroneckerSection`**: `cochainKroneckerSection` commutes with
postcomposition by any morphism `h : Y₁ ⟶ Y₂`. -/
theorem cochainKroneckerSection_coefficient_naturality {Y₁ Y₂ : C} (h : Y₁ ⟶ Y₂) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y₁) :
    (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map h)) i).hom
        (cochainKroneckerSection k K Y₁ i g) =
      cochainKroneckerSection k K Y₂ i (g ≫ h) := by
  apply (linearHomComplexSingle₀HomologyIso k K Y₂ i).toLinearEquiv.injective
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, ← ModuleCat.comp_apply,
    homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom k K h i, ModuleCat.comp_apply]
  simp only [cochainKroneckerSection, LinearMap.comp_apply,
    ← ModuleCat.comp_apply (linearHomComplexSingle₀HomologyIso k K _ i).inv,
    Iso.inv_hom_id, ModuleCat.id_apply]
  exact ChainComplex.homologyClassOfComp_coefficient_naturality _ _ g h

end Kronecker

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {k : Type*} [CommRing k] [Linear k C] {K : CochainComplex C ℤ} {Y : C}

variable (k K Y) in
/-- **The `Ext` inclusion in the universal coefficient sequence for `linearHomComplex`**: for
`i + j = 1` (that is, `j = 1 - i`), when `K.cycles j` is projective and `K.iCycles j` splits, the
`k`-linear map `Ext¹(Hʲ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` sending the extension class of
`β : Bʲ(K) ⟶ Y` to the cohomology class of the cocycle `K⁻ⁱ ⟶ Bʲ(K) ⟶ Y`
(`TauCeti.cochainExtToHomology_extClass_comp_mk₀`). -/
def cochainExtToHomology {i j : ℤ} (hij : i + j = 1) [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    Ext.{w} (K.homology j) Y 1 →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  have hji : ComplexShape.embeddingDownIntUpInt.f (i - 1) = j := by
    rw [ComplexShape.embeddingDownIntUpInt_f]; omega
  have := K.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom.comp <|
    (ChainComplex.extToHomology.{w} k (negChain K) Y i (i - 1)).comp
      (extLinearEquivOfIso k
        (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
          surjective_embeddingDownIntUpInt_f (i - 1) j hji).symm (Iso.refl Y) 1).toLinearMap

/-- **The characterization of `cochainExtToHomology`**: for `i + j = 1`, the class in
`Ext¹(Hʲ(K), Y)` of a morphism `β : Bʲ(K) ⟶ Y` from the degree-`j` boundaries goes to the
cohomology class of any cocycle `φ` with underlying morphism `K.toBoundaries (-i) j ≫ β`. -/
lemma cochainExtToHomology_extClass_comp_mk₀ {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] (β : kernel (K.homologyπ j) ⟶ Y)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hφ : Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) =
      K.toBoundaries (-i) j ≫ β) :
    cochainExtToHomology.{w} k K Y hij
        ((kernelSequence_shortExact (K.homologyπ j)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ := by
  have hji : ComplexShape.embeddingDownIntUpInt.f (i - 1) = j := by
    rw [ComplexShape.embeddingDownIntUpInt_f]; omega
  have := K.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  let eZ := K.restrictionCyclesIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  let eH := K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have hcomm : (negChain K).homologyπ (i - 1) ≫ eH.hom = eZ.hom ≫ K.homologyπ j :=
    K.homologyπ_restrictionHomologyIsoOfSurjective_hom ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f (i - 1) j hji
  let b : kernel ((negChain K).homologyπ (i - 1)) ⟶ kernel (K.homologyπ j) :=
    kernel.map ((negChain K).homologyπ (i - 1)) (K.homologyπ j) eZ.hom eH.hom hcomm
  let s : ShortComplex.mk (kernel.ι ((negChain K).homologyπ (i - 1)))
        ((negChain K).homologyπ (i - 1)) (kernel.condition _) ⟶
      ShortComplex.mk (kernel.ι (K.homologyπ j)) (K.homologyπ j) (kernel.condition _) :=
    { τ₁ := b
      τ₂ := eZ.hom
      τ₃ := eH.hom
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := hcomm.symm }
  have hn := ShortComplex.ShortExact.extClass_naturality
    (kernelSequence_shortExact ((negChain K).homologyπ (i - 1)))
    (kernelSequence_shortExact (K.homologyπ j)) s
  dsimp only [s, ShortComplex.kernelSequence] at hn
  have hB : (negChain K).toBoundaries i (i - 1) ≫ b =
      (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫ K.toBoundaries (-i) j := by
    rw [← cancel_mono (kernel.ι (K.homologyπ j)), Category.assoc, Category.assoc, kernel.lift_ι,
      HomologicalComplex.toBoundaries_ι_assoc, HomologicalComplex.toBoundaries_ι,
      ← cancel_mono (K.iCycles j), Category.assoc, Category.assoc,
      HomologicalComplex.restrictionCyclesIsoOfSurjective_hom_iCycles,
      HomologicalComplex.toCycles_i_assoc, HomologicalComplex.toCycles_i,
      K.restriction_d_eq ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i) hji,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let ψ := ChainComplex.cocycleOfComp k Y (X := negChain K)
    ((negChain K).toBoundaries i (i - 1)) ((negChain K).d_toBoundaries _ i (i - 1)) (b ≫ β)
  have hψ : ((negChain K).linearYonedaObj k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    rw [ChainComplex.iCycles_cocycleOfComp, ← Category.assoc, hB, Category.assoc, hφ]
    exact restrictionXIso_hom_comp K i _
  have harg : (extLinearEquivOfIso k eH.symm (Iso.refl Y) 1)
        ((kernelSequence_shortExact (K.homologyπ j)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      (kernelSequence_shortExact ((negChain K).homologyπ (i - 1))).extClass.comp
        (Ext.mk₀ (b ≫ β)) (add_zero 1) := by
    dsimp only [ShortComplex.kernelSequence]
    rw [extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
      ← Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1), ← hn,
      Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 0) (add_zero 1), Ext.mk₀_comp_mk₀]
  exact (congrArg (fun e ↦ (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom
      (ChainComplex.extToHomology k (negChain K) Y i (i - 1) e)) harg).trans
    ((congrArg (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom
      (ChainComplex.extToHomology_extClass_comp_mk₀ i (i - 1) (b ≫ β) ψ
        (ChainComplex.iCycles_cocycleOfComp _ _ _))).trans
      (linearHomComplexSingle₀HomologyIso_inv_homologyπ K Y i φ ψ hψ))

/-- **Injectivity of `cochainExtToHomology`**: in bidegree `i + j = 1`, the map
`Ext¹(Hʲ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem cochainExtToHomology_injective {i j : ℤ} (hij : i + j = 1) [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    Function.Injective (cochainExtToHomology.{w} k K Y hij) := by
  have hji : ComplexShape.embeddingDownIntUpInt.f (i - 1) = j := by
    rw [ComplexShape.embeddingDownIntUpInt_f]; omega
  have := K.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  exact (linearHomComplexSingle₀HomologyIso k K Y i).symm.toLinearEquiv.injective.comp <|
    (ChainComplex.extToHomology_injective (k := k) (X := negChain K) (Y := Y)
      (show i - 1 + 1 = i by omega)).comp
        (extLinearEquivOfIso k
          (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
            surjective_embeddingDownIntUpInt_f (i - 1) j hji).symm (Iso.refl Y) 1).injective

/-- **Middle exactness of the universal coefficient sequence for `linearHomComplex`**: for
`i + j = 1`, the image of `cochainExtToHomology` is the kernel of `cochainKronecker`. -/
theorem exact_cochainExtToHomology_cochainKronecker {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    Function.Exact (cochainExtToHomology.{w} k K Y hij) (cochainKronecker k K Y i) := by
  have hji : ComplexShape.embeddingDownIntUpInt.f (i - 1) = j := by
    rw [ComplexShape.embeddingDownIntUpInt_f]; omega
  have := K.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have h1 : cochainExtToHomology.{w} k K Y hij =
      ((linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv.symm.toLinearMap.comp
        (ChainComplex.extToHomology.{w} k (negChain K) Y i (i - 1))).comp
        (extLinearEquivOfIso k
          (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
            surjective_embeddingDownIntUpInt_f (i - 1) j hji).symm (Iso.refl Y) 1).toLinearMap := by
    ext e; simp [cochainExtToHomology]
  have h2 : cochainKronecker k K Y i =
      (Linear.homCongr k (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
        (Iso.refl Y)).toLinearMap.comp
        ((ChainComplex.kronecker k (negChain K) Y i).comp
          (linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv.toLinearMap) := rfl
  rw [h1, h2, LinearEquiv.postcomp_exact_iff_exact, LinearEquiv.precomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact]
  exact ChainComplex.exact_extToHomology_kronecker.{w} (k := k) (X := negChain K) (Y := Y)
    (show i - 1 + 1 = i by omega)

variable (k K Y) in
/-- **Split direct-product decomposition of the universal coefficient sequence** for
`linearHomComplex`: when `i + j = 1`, `K.cycles j` is projective, and `K.iCycles j` and
`K.iCycles (-i)` split, cohomology in degree `i` decomposes `k`-linearly as
`Ext¹(Hʲ(K), Y) × (H⁻ⁱ(K) ⟶ Y)`. -/
def cochainUniversalCoefficientEquiv {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      Ext.{w} (K.homology j) Y 1 × (K.homology (-i) ⟶ Y) :=
  ((exact_cochainExtToHomology_cochainKronecker.{w} (k := k) (K := K) (Y := Y)
    hij).splitSurjectiveEquiv (cochainExtToHomology_injective hij)
      ⟨cochainKroneckerSection k K Y i,
        LinearMap.ext (cochainKronecker_cochainKroneckerSection i)⟩).1

@[simp]
lemma cochainUniversalCoefficientEquiv_symm_apply {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (e : Ext.{w} (K.homology j) Y 1) (g : K.homology (-i) ⟶ Y) :
    (cochainUniversalCoefficientEquiv.{w} k K Y hij).symm (e, g) =
      cochainExtToHomology k K Y hij e + cochainKroneckerSection k K Y i g :=
  Function.Exact.splitSurjectiveEquiv_symm_apply _ _ _ e g

@[simp]
lemma cochainUniversalCoefficientEquiv_apply_snd {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    (cochainUniversalCoefficientEquiv.{w} k K Y hij x).2 = cochainKronecker k K Y i x :=
  Function.Exact.splitSurjectiveEquiv_apply_snd _ _ _ x

/-- **Naturality of `cochainExtToHomology` in the complex**: pulling an extension back along
`homologyMap φ j` and including it into cohomology agrees with including first and pulling back
along `linearHomComplexPrecomp k φ _`. -/
theorem cochainExtToHomology_naturality {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) {i j : ℤ}
    (hij : i + j = 1) [Projective (K₁.cycles j)] [IsSplitMono (K₁.iCycles j)]
    [Projective (K₂.cycles j)] [IsSplitMono (K₂.iCycles j)] (e : Ext.{w} (K₂.homology j) Y 1) :
    cochainExtToHomology k K₁ Y hij ((Ext.mk₀ (homologyMap φ j)).comp e (zero_add 1)) =
      (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom
        (cochainExtToHomology k K₂ Y hij e) := by
  have hji : ComplexShape.embeddingDownIntUpInt.f (i - 1) = j := by
    rw [ComplexShape.embeddingDownIntUpInt_f]; omega
  have := K₁.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K₁.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K₂.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K₂.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  apply (linearHomComplexSingle₀HomologyIso k K₁ Y i).toLinearEquiv.injective
  have hext : (extLinearEquivOfIso k
        (K₁.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
          surjective_embeddingDownIntUpInt_f (i - 1) j hji).symm (Iso.refl Y) 1)
      ((Ext.mk₀ (homologyMap φ j)).comp e (zero_add 1)) =
      (Ext.mk₀ (homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt)
        (i - 1))).comp
          ((extLinearEquivOfIso k
            (K₂.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
              surjective_embeddingDownIntUpInt_f (i - 1) j hji).symm (Iso.refl Y) 1) e)
            (zero_add 1) := by
    simp only [extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀,
      ← HomologicalComplex.homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, ← ModuleCat.comp_apply,
    homologyMap_precomp_linearHomComplexSingle₀HomologyIso_hom k φ Y i, ModuleCat.comp_apply]
  simp only [cochainExtToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← ModuleCat.comp_apply (linearHomComplexSingle₀HomologyIso k _ Y i).inv,
    Iso.inv_hom_id, ModuleCat.id_apply, hext]
  exact ChainComplex.extToHomology_naturality
    (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i (i - 1) _

/-- **Naturality of `cochainExtToHomology` in the coefficient object**: pushing an extension forward
along `g : Y₁ ⟶ Y₂` and including it into cohomology agrees with including first and applying
`linearHomComplexPostcomp`. -/
theorem cochainExtToHomology_coefficient_naturality {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) {i j : ℤ}
    (hij : i + j = 1) [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)]
    (e : Ext.{w} (K.homology j) Y₁ 1) :
    cochainExtToHomology k K Y₂ hij (e.comp (Ext.mk₀ g) (add_zero 1)) =
      (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom
        (cochainExtToHomology k K Y₁ hij e) := by
  have hji : ComplexShape.embeddingDownIntUpInt.f (i - 1) = j := by
    rw [ComplexShape.embeddingDownIntUpInt_f]; omega
  have := K.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  have := K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j hji
  apply (linearHomComplexSingle₀HomologyIso k K Y₂ i).toLinearEquiv.injective
  have hext : (extLinearEquivOfIso k
        (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
          surjective_embeddingDownIntUpInt_f (i - 1) j hji).symm (Iso.refl Y₂) 1)
      (e.comp (Ext.mk₀ g) (add_zero 1)) =
      ((extLinearEquivOfIso k
        (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
          surjective_embeddingDownIntUpInt_f (i - 1) j hji).symm (Iso.refl Y₁) 1) e).comp
        (Ext.mk₀ g) (add_zero 1) := by
    simp only [extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    exact (Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)).symm
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, ← ModuleCat.comp_apply,
    homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom k K g i, ModuleCat.comp_apply]
  simp only [cochainExtToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← ModuleCat.comp_apply (linearHomComplexSingle₀HomologyIso k K _ i).inv,
    Iso.inv_hom_id, ModuleCat.id_apply, hext]
  exact ChainComplex.extToHomology_coefficient_naturality g i (i - 1) _

end Ext

end TauCeti
