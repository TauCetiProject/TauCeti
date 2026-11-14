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
public import TauCeti.Algebra.Homology.LinearHomComplex.Homotopy
public import TauCeti.Algebra.Homology.PrincipalIdealRing
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality

/-!
# The universal coefficient theorem for `linearHomComplex` into a degree-zero object

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear abelian category `C`, and let `Y : C`.
Mathlib's `CochainComplex.linearHomComplex k K ((singleFunctor C 0).obj Y)` is the cochain complex
of `k`-modules of cochains from `K` into `Y` placed in degree `0`. In degree `i`,
`Cochain.toSingleLinearEquiv (neg_add_cancel i)` identifies its cochains with morphisms
`K.X (-i) ⟶ Y`, and its differential sends `f : K.X (-i) ⟶ Y` to
`(-1)^(i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`
(`TauCeti.toSingleLinearEquiv_linearHomComplex_d_apply`).

Reindexing `K` along `n ↦ -n` (`ComplexShape.embeddingDownIntUpInt`) turns `K` into a chain complex
`K'` with `K'.X i = K.X (-i)` and unsigned dual `K'.linearYonedaObj k Y`. Because the quadratic sign
`ε(i) = (-1)^(i(i + 1) / 2)` satisfies `ε(i + 1) = (-1)^(i + 1) ε(i)` for every integer `i`, scaling
`Cochain.toSingleLinearEquiv (neg_add_cancel i)` by `ε(i)` in degree `i` gives a natural isomorphism
of cochain complexes
`linearHomComplex k K ((singleFunctor C 0).obj Y) ≅ K'.linearYonedaObj k Y`
(`TauCeti.linearHomComplexSingle₀Iso`). Multiplying the induced cohomology isomorphism in degree `i`
by `ε(i)` a second time cancels the sign on cocycles while remaining natural in both `K` and `Y`,
since `ε(i)` depends only on `i` (`TauCeti.linearHomComplexSingle₀HomologyIso`).

Transporting the chain-complex universal coefficient sequence
(`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`) across this unsigned cohomology comparison
and the reindexing isomorphisms `Hᵢ(K') ≅ H⁻ⁱ(K)` and `Hᵢ₋₁(K') ≅ Hʲ(K)` (for `i + j = 1`, that is
`j = 1 - i`) yields the split short exact sequence

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`

whenever the cycles `Z¹⁻ⁱ(K)` are projective and the inclusions `Z⁻ⁱ(K) ⟶ K⁻ⁱ` and
`Z¹⁻ⁱ(K) ⟶ K¹⁻ⁱ` split, as holds for any complex of projective modules over a principal ideal
domain (`TauCeti.Algebra.Homology.PrincipalIdealRing`). Both maps of the sequence are natural in
`K` and in `Y`. The splitting (`TauCeti.cochainKroneckerSection`) is natural in the coefficient
object `Y`, whereas no simultaneous splitting natural in `K` exists even for bounded finite free
`ℤ`-cochain complexes with `Y = ℤ` (`TauCeti.not_exists_natural_section_cochainKronecker`).

## Main definitions and results

* `TauCeti.toSingleLinearEquiv_linearHomComplex_d_apply`: under
  `Cochain.toSingleLinearEquiv (neg_add_cancel _)`, the differential of
  `linearHomComplex k K ((singleFunctor C 0).obj Y)` in degree `i` is
  `f ↦ (-1)^(i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`.
* `TauCeti.linearHomComplexSingle₀Iso` and `TauCeti.linearHomComplexSingle₀HomologyIso`: the signed
  cochain-complex comparison with `(K.restriction embeddingDownIntUpInt).linearYonedaObj k Y` and
  the resulting unsigned cohomology comparison, natural in `K` and `Y`.
* `TauCeti.cochainKronecker`: the `k`-linear Kronecker evaluation
  `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, natural in `K` and `Y`, which is an equivalence when `Y`
  is injective (`TauCeti.cochainKroneckerEquiv`) or when `Hʲ(K)` (`i + j = 1`) is projective and the
  relevant cycle inclusions split (`TauCeti.cochainKroneckerEquivOfProjectiveHomology`).
* `TauCeti.cochainKroneckerSection`: the `k`-linear right inverse of `cochainKronecker` built from
  a retraction of `K.iCycles (-i)`, natural in `Y`.
* `TauCeti.cochainExtToHomology`: the `k`-linear inclusion
  `Ext¹(Hʲ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))`, injective and exact with `cochainKronecker` when
  `i + j = 1`, natural in `K` and `Y`.
* `TauCeti.cochainUniversalCoefficientEquiv`: the split decomposition
  `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] Ext¹(Hʲ(K), Y) × (H⁻ⁱ(K) ⟶ Y)` for `i + j = 1`.
* `TauCeti.not_exists_natural_section_cochainKronecker`: no family of sections of
  `cochainKronecker` at `Y = ℤ` in degree `0` is natural across morphisms of bounded finite free
  `ℤ`-cochain complexes.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2 and Example 3.3.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 3.6.5.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex CochainComplex.HomComplex Opposite
  Abelian

universe w v u

namespace TauCeti

section Sign

/-- The quadratic sign `(-1)^(i(i + 1) / 2)` intertwining the Koszul differential of
`linearHomComplex` into a degree-zero object with the unsigned differential of `linearYonedaObj` on
the negated chain complex. -/
def cochainDualSign (i : ℤ) : ℤˣ :=
  ((i * (i + 1)) / 2).negOnePow

/-- Shifting the index of `cochainDualSign` by `1` multiplies it by `(-1)^(i + 1)`, for every
integer `i` (positive, zero, or negative). -/
lemma cochainDualSign_add_one (i : ℤ) :
    cochainDualSign (i + 1) = (i + 1).negOnePow * cochainDualSign i := by
  have h : (i + 1) * (i + 1 + 1) = i * (i + 1) + (i + 1) * 2 := by ring
  rw [cochainDualSign, cochainDualSign, h, Int.add_mul_ediv_right _ _ (by decide : (2 : ℤ) ≠ 0),
    Int.negOnePow_add, mul_comm]

@[simp]
lemma cochainDualSign_zero : cochainDualSign 0 = 1 := by
  simp [cochainDualSign]

lemma cochainDualSign_mul_self (i : ℤ) : cochainDualSign i * cochainDualSign i = 1 :=
  Int.units_mul_self _

@[simp]
private lemma cochainDualSign_smul_smul {M : Type*} [AddCommGroup M] (i : ℤ) (x : M) :
    cochainDualSign i • (cochainDualSign i • x) = x := by
  rw [smul_smul, cochainDualSign_mul_self, one_smul]

private lemma cochainDualSign_smul_comp {D : Type*} [Category* D] [Preadditive D]
    {X Y Z : D} (i : ℤ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (cochainDualSign i • f) ≫ g = cochainDualSign i • (f ≫ g) := by
  rw [Units.smul_def, Units.smul_def, Preadditive.zsmul_comp]

private lemma comp_cochainDualSign_smul {D : Type*} [Category* D] [Preadditive D]
    {X Y Z : D} (i : ℤ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ (cochainDualSign i • g) = cochainDualSign i • (f ≫ g) := by
  rw [Units.smul_def, Units.smul_def, Preadditive.comp_zsmul]

end Sign

section Differential

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {k : Type*} [Ring k] [Linear k C]

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
  -- Express `z` as `Cochain.toSingleMk` of its underlying morphism so `Cochain.δ_toSingleMk`
  -- applies directly.
  have hz : Cochain.toSingleMk (Cochain.toSingleEquiv (neg_add_cancel i) z) (neg_add_cancel i) =
      z := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  rw [linearHomComplex_d_hom_apply, ← hz,
    Cochain.δ_toSingleMk _ (neg_add_cancel i) (i + 1) (-(i + 1)) (neg_add_cancel (i + 1))]
  simp [Cochain.toSingleLinearEquiv]

end Differential

section Comparison

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reindexing a `ℤ`-indexed cochain complex `K` along `n ↦ -n` as a chain complex. -/
private abbrev negChain (K : CochainComplex C ℤ) : ChainComplex C ℤ :=
  K.restriction ComplexShape.embeddingDownIntUpInt

variable (k : Type*) [Ring k] [Linear k C]

/-- **Comparison of `linearHomComplex` into a degree-zero object with `linearYonedaObj`.**
Scaling `Cochain.toSingleLinearEquiv (neg_add_cancel i)` by `cochainDualSign i` in degree `i`
gives an isomorphism of cochain complexes from `linearHomComplex k K ((singleFunctor C 0).obj Y)` to
`(K.restriction ComplexShape.embeddingDownIntUpInt).linearYonedaObj k Y`. -/
def linearHomComplexSingle₀Iso (K : CochainComplex C ℤ) (Y : C) :
    linearHomComplex k K ((singleFunctor C 0).obj Y) ≅
      _root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦
      { hom := ModuleCat.ofHom
          (X := (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i)
          (Y := ((negChain K).linearYonedaObj k Y).X i)
          (cochainDualSign i •
            (Cochain.toSingleLinearEquiv (R := k) (K := K) (X := Y)
              (neg_add_cancel i)).toLinearMap)
        inv := ModuleCat.ofHom
          (X := ((negChain K).linearYonedaObj k Y).X i)
          (Y := (linearHomComplex k K ((singleFunctor C 0).obj Y)).X i)
          (cochainDualSign i •
            (Cochain.toSingleLinearEquiv (R := k) (K := K) (X := Y)
              (neg_add_cancel i)).symm.toLinearMap)
        hom_inv_id := by
          ext z
          let e := Cochain.toSingleLinearEquiv (R := k) (K := K) (X := Y) (neg_add_cancel i)
          let z' : Cochain K ((singleFunctor C 0).obj Y) i := z
          have h : (cochainDualSign i • e.symm.toLinearMap)
              ((cochainDualSign i • e.toLinearMap) z') = z' := by
            rw [Units.smul_def, LinearMap.smul_apply, Units.smul_def, LinearMap.smul_apply,
              map_zsmul, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
              e.symm_apply_apply, ← Units.smul_def, ← Units.smul_def, cochainDualSign_smul_smul]
          exact h
        inv_hom_id := by
          ext f
          let e := Cochain.toSingleLinearEquiv (R := k) (K := K) (X := Y) (neg_add_cancel i)
          let f' : K.X (-i) ⟶ Y := f
          have h : (cochainDualSign i • e.toLinearMap)
              ((cochainDualSign i • e.symm.toLinearMap) f') = f' := by
            rw [Units.smul_def, LinearMap.smul_apply, Units.smul_def, LinearMap.smul_apply,
              map_zsmul, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
              e.apply_symm_apply, ← Units.smul_def, ← Units.smul_def, cochainDualSign_smul_smul]
          exact h })
    (fun i j hij ↦ by
      obtain rfl : i + 1 = j := by simpa [ComplexShape.up_Rel] using hij
      ext z
      have hcomm :
          K.d (-(i + 1)) (-i) ≫
              (cochainDualSign i • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) =
            cochainDualSign (i + 1) •
              Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel (i + 1))
                (((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom z) := by
        rw [toSingleLinearEquiv_linearHomComplex_d_apply (k := k) K Y i z,
          cochainDualSign_add_one i, mul_comm (i + 1).negOnePow, smul_smul, mul_assoc,
          Int.units_mul_self, mul_one, comp_cochainDualSign_smul]
      exact hcomm)

@[simp]
lemma linearHomComplexSingle₀Iso_hom_f_apply {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (z : ModuleCat.of k (Cochain K ((singleFunctor C 0).obj Y) i)) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexSingle₀Iso k K Y).hom.f i) z) =
      cochainDualSign i • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z :=
  (rfl)

@[simp]
lemma linearHomComplexSingle₀Iso_inv_f_apply {k} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (f : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).X i) :
    (dsimp% only [linearHomComplex_X]
      ModuleCat.Hom.hom ((linearHomComplexSingle₀Iso k K Y).inv.f i) f) =
      (cochainDualSign i • Cochain.toSingleMk f (neg_add_cancel i) :
        ModuleCat.of k (Cochain K ((singleFunctor C 0).obj Y) i)) :=
  (rfl)

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
  have hz : Cochain.toSingleMk (Cochain.toSingleEquiv (neg_add_cancel i) z) (neg_add_cancel i) =
      z := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, linearHomComplex_X, linearHomComplexSingle₀Iso_hom_f_apply]
  have hrhs := ChainComplex.linearYonedaFunctor_map_f_hom_apply k Y
    (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op i
    (cochainDualSign i • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z)
  have hpre :
      cochainDualSign i • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
          (((linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)).f i).hom z) =
        φ.f (-i) ≫
          (cochainDualSign i • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) := by
    rw [linearHomComplexPrecomp_f_apply, ← hz, ← Cochain.toSingleMk_precomp,
      comp_cochainDualSign_smul]
    simp [Cochain.toSingleLinearEquiv]
  exact hpre.trans hrhs.symm

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
  have hz : Cochain.toSingleMk (Cochain.toSingleEquiv (neg_add_cancel i) z) (neg_add_cancel i) =
      z := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel i) z
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply, linearHomComplex_X, linearHomComplexSingle₀Iso_hom_f_apply]
  have hrhs := _root_.ChainComplex.linearYonedaObjMap_f_hom_apply k (negChain K) g i
    (cochainDualSign i • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z)
  have hpost :
      cochainDualSign i • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
          (((linearHomComplexPostcomp k K ((singleFunctor C 0).map g)).f i).hom z) =
        (cochainDualSign i • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z) ≫ g := by
    rw [linearHomComplexPostcomp_f_apply, ← hz, ← Cochain.toSingleMk_postcomp,
      cochainDualSign_smul_comp]
    simp [Cochain.toSingleLinearEquiv]
  exact hpost.trans hrhs.symm

/-- **Unsigned cohomology comparison** between `linearHomComplex k K ((singleFunctor C 0).obj Y)`
and `_root_.ChainComplex.linearYonedaObj (K.restriction ComplexShape.embeddingDownIntUpInt) k Y` in
degree `i`. Multiplying the map on cohomology induced by `linearHomComplexSingle₀Iso` by
`cochainDualSign i` cancels the degree-`i` sign on cocycles while keeping naturality in both `K` and
`Y`. -/
def linearHomComplexSingle₀HomologyIso (K : CochainComplex C ℤ) (Y : C) (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≅
      (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).homology i where
  hom := cochainDualSign i • homologyMap (linearHomComplexSingle₀Iso k K Y).hom i
  inv := cochainDualSign i • homologyMap (linearHomComplexSingle₀Iso k K Y).inv i
  hom_inv_id := by
    rw [cochainDualSign_smul_comp, comp_cochainDualSign_smul, cochainDualSign_smul_smul,
      ← homologyMap_comp, Iso.hom_inv_id, homologyMap_id]
  inv_hom_id := by
    rw [cochainDualSign_smul_comp, comp_cochainDualSign_smul, cochainDualSign_smul_smul,
      ← homologyMap_comp, Iso.inv_hom_id, homologyMap_id]

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
  have h₁ : (linearHomComplexSingle₀HomologyIso k K₁ Y i).hom =
      cochainDualSign i • homologyMap (linearHomComplexSingle₀Iso k K₁ Y).hom i := rfl
  have h₂ : (linearHomComplexSingle₀HomologyIso k K₂ Y i).hom =
      cochainDualSign i • homologyMap (linearHomComplexSingle₀Iso k K₂ Y).hom i := rfl
  have hcomp := HomologicalComplex.homologyMap_comp
    (K := linearHomComplex k K₂ ((singleFunctor C 0).obj Y))
    (L := (negChain K₂).linearYonedaObj k Y)
    (M := (negChain K₁).linearYonedaObj k Y)
    (linearHomComplexSingle₀Iso k K₂ Y).hom
    ((ChainComplex.linearYonedaFunctor k Y).map
      (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op) i
  rw [h₁, h₂, comp_cochainDualSign_smul, cochainDualSign_smul_comp, ← homologyMap_comp, ← hcomp,
    linearHomComplexPrecomp_linearHomComplexSingle₀Iso_hom]
  rfl

@[reassoc]
theorem homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom
    (K : CochainComplex C ℤ) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ) :
    homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i ≫
        (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom =
      (linearHomComplexSingle₀HomologyIso k K Y₁ i).hom ≫
        homologyMap
          (_root_.ChainComplex.linearYonedaObjMap k
            (K.restriction ComplexShape.embeddingDownIntUpInt) g) i := by
  have h₁ : (linearHomComplexSingle₀HomologyIso k K Y₁ i).hom =
      cochainDualSign i • homologyMap (linearHomComplexSingle₀Iso k K Y₁).hom i := rfl
  have h₂ : (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom =
      cochainDualSign i • homologyMap (linearHomComplexSingle₀Iso k K Y₂).hom i := rfl
  rw [h₁, h₂, comp_cochainDualSign_smul, cochainDualSign_smul_comp, ← homologyMap_comp,
    ← homologyMap_comp, linearHomComplexPostcomp_linearHomComplexSingle₀Iso_hom]

/-- On cocycles, `linearHomComplexSingle₀HomologyIso` removes the sign `cochainDualSign i` and sends
the class of a cocycle `φ` directly to the class of `Cochain.toSingleLinearEquiv` applied to its
underlying cochain. -/
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
  have hcyc : cyclesMap (linearHomComplexSingle₀Iso k K Y).hom i φ = cochainDualSign i • ψ := by
    apply HomologicalComplex.moduleCat_iCycles_injective
    have hi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (linearHomComplexSingle₀Iso k K Y).hom i) φ
    rw [ModuleCat.comp_apply, ModuleCat.comp_apply, linearHomComplexSingle₀Iso_hom_f_apply] at hi
    have hsmul : (cochainDualSign i : ℤ) • Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) =
        (cochainDualSign i : ℤ) • (((negChain K).linearYonedaObj k Y).iCycles i).hom ψ :=
      congrArg ((cochainDualSign i : ℤ) • ·) hψ.symm
    exact hi.trans (hsmul.trans
      (map_zsmul (((negChain K).linearYonedaObj k Y).iCycles i).hom (cochainDualSign i : ℤ) ψ).symm)
  -- Unfold `linearHomComplexSingle₀HomologyIso` to scalar multiplication on `homologyMap` in
  -- `ModuleCat k`.
  change cochainDualSign i •
      (homologyMap (linearHomComplexSingle₀Iso k K Y).hom i).hom
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ) = _
  rw [hnat, hcyc, Units.smul_def, Units.smul_def, ← map_zsmul, ← Units.smul_def, ← Units.smul_def,
    cochainDualSign_smul_smul]

end Comparison

section RestrictionHelpers

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reindexing isomorphism `(K.restriction embeddingDownIntUpInt).cycles m ≅ K.cycles n` when
`-m = n`. -/
private def negChainCyclesIso (K : CochainComplex C ℤ) {m n : ℤ} (hmn : -m = n) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).cycles m ≅ K.cycles n :=
  K.restrictionCyclesIso ComplexShape.embeddingDownIntUpInt m (m - 1) (by simp)
    (j' := n) (k' := n + 1) (by simp [hmn]) (by simp; omega) (by simp)

/-- Reindexing isomorphism `(K.restriction embeddingDownIntUpInt).homology m ≅ K.homology n` when
`-m = n`. -/
private def negChainHomologyIso (K : CochainComplex C ℤ) {m n : ℤ} (hmn : -m = n) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homology m ≅ K.homology n :=
  K.restrictionHomologyIso ComplexShape.embeddingDownIntUpInt (m + 1) m (m - 1) (by simp) (by simp)
    (i' := n - 1) (j' := n) (k' := n + 1) (by simp; omega) (by simp [hmn]) (by simp; omega)
    (by simp) (by simp)

@[reassoc]
private lemma negChainHomologyIso_hom_naturality {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂)
    {m n : ℤ} (hmn : -m = n) :
    homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) m ≫
        (negChainHomologyIso K₂ hmn).hom =
      (negChainHomologyIso K₁ hmn).hom ≫ homologyMap φ n := by
  rw [← cancel_mono (K₂.homologyι n)]
  simp only [negChainHomologyIso, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality, homologyι_naturality_assoc, restrictionHomologyIso_hom_homologyι_assoc]
  congr 1
  rw [← cancel_epi ((K₁.restriction ComplexShape.embeddingDownIntUpInt).pOpcycles m),
    p_opcyclesMap_assoc,
    restrictionMap_f' φ _ (by simpa using hmn)]
  simp

private lemma projective_negChain_cycles (K : CochainComplex C ℤ) {m n : ℤ} (hmn : -m = n)
    [Projective (K.cycles n)] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles m) :=
  Projective.of_iso (negChainCyclesIso K hmn).symm inferInstance

private lemma projective_negChain_homology (K : CochainComplex C ℤ) {m n : ℤ} (hmn : -m = n)
    [Projective (K.homology n)] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).homology m) :=
  Projective.of_iso (negChainHomologyIso K hmn).symm inferInstance

private lemma isSplitMono_negChain_iCycles (K : CochainComplex C ℤ) {m n : ℤ} (hmn : -m = n)
    [IsSplitMono (K.iCycles n)] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles m) := by
  have hfac : (K.restriction ComplexShape.embeddingDownIntUpInt).iCycles m =
      (negChainCyclesIso K hmn).hom ≫ K.iCycles n ≫
        (K.restrictionXIso ComplexShape.embeddingDownIntUpInt (by simpa using hmn)).inv := by
    rw [← cancel_mono
      (K.restrictionXIso ComplexShape.embeddingDownIntUpInt (by simpa using hmn)).hom]
    simp [negChainCyclesIso]
  rw [hfac]
  infer_instance

private lemma bijective_leftComp_iso_inv {k : Type*} [Ring k] [Linear k C] {X₁ X₂ Y : C}
    (e : X₁ ≅ X₂) : Function.Bijective (Linear.leftComp k Y e.inv) := by
  refine ⟨fun a b h ↦ ?_, fun g ↦ ⟨e.hom ≫ g, ?_⟩⟩
  · simpa [Linear.leftComp_apply] using congrArg (e.hom ≫ ·) h
  · simp [Linear.leftComp_apply]

end RestrictionHelpers

section Kronecker

variable {C : Type u} [Category.{v} C] [Abelian C] (k : Type*) [Ring k] [Linear k C]
  (K : CochainComplex C ℤ) (Y : C)

/-- **The Kronecker map for `linearHomComplex` into a degree-zero object**: the `k`-linear map
`Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` evaluating cohomology classes of cochains on homology
classes of `K` in degree `-i`. -/
def cochainKronecker (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i →ₗ[k] (K.homology (-i) ⟶ Y) :=
  (Linear.leftComp k Y (negChainHomologyIso K (rfl : -i = -i)).inv).comp <|
    (ChainComplex.kronecker k (K.restriction ComplexShape.embeddingDownIntUpInt) Y i).comp
      (linearHomComplexSingle₀HomologyIso k K Y i).hom.hom

/-- **The Kronecker map on cocycle classes**: evaluating the cohomology class of a cocycle `φ` on
the homology class of a cycle in degree `-i` applies the underlying morphism of `φ` to the cycle,
with no sign. -/
@[reassoc (attr := simp)]
lemma homologyπ_cochainKronecker {k} [Ring k] [Linear k C] {K : CochainComplex C ℤ} {Y : C}
    (i : ℤ) (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    K.homologyπ (-i) ≫
        cochainKronecker k K Y i
          (((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ) =
      K.iCycles (-i) ≫ Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
  set X : _root_.ChainComplex C ℤ := negChain K
  set f : X.X i ⟶ Y := Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
    (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)
  have hf : X.d ((ComplexShape.up ℤ).next i) i ≫ f = 0 := by
    have h0 : ((linearHomComplex k K ((singleFunctor C 0).obj Y)).d i (i + 1)).hom
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) = 0 :=
      ConcreteCategory.congr_hom
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles_d i (i + 1)) φ
    have hd := toSingleLinearEquiv_linearHomComplex_d_apply (k := k) K Y i
      (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ)
    rw [h0, map_zero] at hd
    have hf₀ : K.d (-(i + 1)) (-i) ≫
        Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
          (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) = 0 := by
      simpa [smul_smul] using congrArg ((i + 1).negOnePow • ·) hd.symm
    rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i + 1) by simp)]
    exact hf₀
  let ψ := ChainComplex.cocycleOfComp k Y f hf (𝟙 Y)
  have hψ : (X.linearYonedaObj k Y).iCycles i ψ = f :=
    (ChainComplex.iCycles_cocycleOfComp f hf (𝟙 Y)).trans (Category.comp_id f)
  rw [cochainKronecker, LinearMap.comp_apply, LinearMap.comp_apply, Linear.leftComp_apply,
    linearHomComplexSingle₀HomologyIso_hom_homologyπ K Y i φ ψ hψ]
  rw [negChainHomologyIso, homologyπ_restrictionHomologyIso_inv_assoc,
    ChainComplex.kronecker_homologyπ, hψ, restrictionCyclesIso_inv_iCycles_assoc]
  exact congrArg (K.iCycles (-i) ≫ ·) (Category.id_comp f)

/-- **Naturality of `cochainKronecker` in the complex**: pulling back along `φ : K₁ ⟶ K₂` and
evaluating on homology is pushing homology forward along `φ` and evaluating. -/
theorem cochainKronecker_naturality {k} [Ring k] [Linear k C] {K₁ K₂ : CochainComplex C ℤ}
    {Y : C} (φ : K₁ ⟶ K₂) (i : ℤ)
    (x : (linearHomComplex k K₂ ((singleFunctor C 0).obj Y)).homology i) :
    cochainKronecker k K₁ Y i
        ((homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom x) =
      homologyMap φ (-i) ≫ cochainKronecker k K₂ Y i x := by
  simp only [cochainKronecker, LinearMap.comp_apply, Linear.leftComp_apply]
  rw [← ModuleCat.comp_apply,
    homologyMap_precomp_linearHomComplexSingle₀HomologyIso_hom k φ Y i, ModuleCat.comp_apply,
    ChainComplex.kronecker_naturality]
  rw [← cancel_epi (negChainHomologyIso K₁ (rfl : -i = -i)).hom, Iso.hom_inv_id_assoc,
    ← Category.assoc, ← negChainHomologyIso_hom_naturality φ (rfl : -i = -i),
    Category.assoc, Iso.hom_inv_id_assoc]

/-- **Naturality of `cochainKronecker` in the coefficient object**: postcomposing with `g : Y₁ ⟶ Y₂`
commutes with `cochainKronecker`. -/
theorem cochainKronecker_coefficient_naturality {k} [Ring k] [Linear k C]
    {K : CochainComplex C ℤ} {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y₁)).homology i) :
    cochainKronecker k K Y₂ i
        ((homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom x) =
      cochainKronecker k K Y₁ i x ≫ g := by
  simp only [cochainKronecker, LinearMap.comp_apply, Linear.leftComp_apply]
  rw [← ModuleCat.comp_apply,
    homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom k K g i, ModuleCat.comp_apply,
    ChainComplex.kronecker_coefficient_naturality, Category.assoc]

/-- **The universal coefficient theorem for injective coefficients**: when `Y` is injective,
`cochainKronecker` is bijective in every degree. -/
theorem cochainKronecker_bijective {k} [Ring k] [Linear k C] {K : CochainComplex C ℤ}
    {Y : C} [Injective Y] (i : ℤ) :
    Function.Bijective (cochainKronecker k K Y i) := by
  rw [cochainKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (bijective_leftComp_iso_inv (k := k) (Y := Y)
    (negChainHomologyIso K (rfl : -i = -i))).comp <|
      (ChainComplex.kronecker_bijective (k := k)
        (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y) i).comp
          (linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv.bijective

/-- **The Kronecker equivalence for injective coefficients**: for an injective object `Y`,
`cochainKronecker` is a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def cochainKroneckerEquiv [Injective Y] (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (cochainKronecker k K Y i) (cochainKronecker_bijective i)

@[simp]
lemma cochainKroneckerEquiv_apply {k} [Ring k] [Linear k C] {K : CochainComplex C ℤ} {Y : C}
    [Injective Y] (i : ℤ) (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    cochainKroneckerEquiv k K Y i x = cochainKronecker k K Y i x :=
  (rfl)

/-- **The universal coefficient theorem with projective cohomology in degree `1 - i`**: when
`i + j = 1`, the cycle inclusions in degrees `j` and `-i` split, and `Hʲ(K)` is projective,
`cochainKronecker` in degree `i` is bijective over any ring `k`. -/
theorem cochainKronecker_bijective_of_projective_homology {k} [Ring k] [Linear k C]
    {K : CochainComplex C ℤ} {Y : C} {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] [Projective (K.homology j)] :
    Function.Bijective (cochainKronecker k K Y i) := by
  have hji : -(i - 1) = j := by omega
  have := isSplitMono_negChain_iCycles K hji
  have := isSplitMono_negChain_iCycles K (rfl : -i = -i)
  have := projective_negChain_homology K hji
  rw [cochainKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (bijective_leftComp_iso_inv (k := k) (Y := Y)
    (negChainHomologyIso K (rfl : -i = -i))).comp <|
      (ChainComplex.kronecker_bijective_of_projective_homology_of_add_one_eq
        (k := k) (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y)
        (show i - 1 + 1 = i by omega)).comp
          (linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv.bijective

/-- **The Kronecker equivalence with projective cohomology in degree `1 - i`**: for `i + j = 1`,
when `K.iCycles j` and `K.iCycles (-i)` split and `K.homology j` is projective, `cochainKronecker`
is a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def cochainKroneckerEquivOfProjectiveHomology {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] [Projective (K.homology j)] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (cochainKronecker k K Y i)
    (cochainKronecker_bijective_of_projective_homology hij)

@[simp]
lemma cochainKroneckerEquivOfProjectiveHomology_apply {k} [Ring k] [Linear k C]
    {K : CochainComplex C ℤ} {Y : C} {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] [Projective (K.homology j)]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    cochainKroneckerEquivOfProjectiveHomology k K Y hij x = cochainKronecker k K Y i x :=
  (rfl)

/-- **Vanishing of dual cohomology** when `H¹⁻ⁱ(K)` is projective and `H⁻ⁱ(K)` vanishes. -/
theorem isZero_homology_linearHomComplex_of_projective_homology {k} [Ring k] [Linear k C]
    {K : CochainComplex C ℤ} {Y : C} {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))] [Projective (K.homology j)]
    (hi : IsZero (K.homology (-i))) :
    IsZero ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) := by
  have : Subsingleton (K.homology (-i) ⟶ Y) := ⟨hi.eq_of_src⟩
  have := (cochainKronecker_bijective_of_projective_homology (k := k) (K := K) (Y := Y)
    hij).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- **Chosen splitting of `cochainKronecker`**: given a retraction of `K.iCycles (-i)`, the
`k`-linear right inverse of `cochainKronecker` sending `g : H⁻ⁱ(K) ⟶ Y` to the cohomology class of
the cocycle `K⁻ⁱ ⟶ Z⁻ⁱ(K) ⟶ H⁻ⁱ(K) ⟶ Y`. -/
def cochainKroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    (K.homology (-i) ⟶ Y) →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  have : IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i) :=
    isSplitMono_negChain_iCycles K (rfl : -i = -i)
  (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom.comp <|
    (ChainComplex.kroneckerSection k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i).comp
        (Linear.leftComp k Y (negChainHomologyIso K (rfl : -i = -i)).hom)

/-- `cochainKroneckerSection` is a right inverse of `cochainKronecker`. -/
@[simp]
lemma cochainKronecker_cochainKroneckerSection {k} [Ring k] [Linear k C]
    {K : CochainComplex C ℤ} {Y : C} (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y) :
    cochainKronecker k K Y i (cochainKroneckerSection k K Y i g) = g := by
  have : IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i) :=
    isSplitMono_negChain_iCycles K (rfl : -i = -i)
  simp only [cochainKronecker, cochainKroneckerSection, LinearMap.comp_apply,
    Linear.leftComp_apply]
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    ChainComplex.kronecker_kroneckerSection, Iso.inv_hom_id_assoc]

/-- **Surjectivity of `cochainKronecker`** when `K.iCycles (-i)` is a split monomorphism. -/
theorem cochainKronecker_surjective_of_isSplitMono {k} [Ring k] [Linear k C]
    {K : CochainComplex C ℤ} {Y : C} (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    Function.Surjective (cochainKronecker k K Y i) :=
  fun g ↦ ⟨cochainKroneckerSection k K Y i g, cochainKronecker_cochainKroneckerSection i g⟩

/-- **Coefficient naturality of `cochainKroneckerSection`**: `cochainKroneckerSection` commutes with
postcomposition by any morphism `h : Y₁ ⟶ Y₂`. -/
theorem cochainKroneckerSection_coefficient_naturality {k} [Ring k] [Linear k C]
    {K : CochainComplex C ℤ} {Y₁ Y₂ : C} (h : Y₁ ⟶ Y₂) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y₁) :
    (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map h)) i).hom
        (cochainKroneckerSection k K Y₁ i g) =
      cochainKroneckerSection k K Y₂ i (g ≫ h) := by
  have : IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i) :=
    isSplitMono_negChain_iCycles K (rfl : -i = -i)
  apply (linearHomComplexSingle₀HomologyIso k K Y₂ i).toLinearEquiv.injective
  -- Rewrite `toLinearEquiv` composition into a categorical composite in `ModuleCat` so the
  -- naturality square of `linearHomComplexSingle₀HomologyIso` applies.
  change ((homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map h)) i ≫
      (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom).hom)
        (cochainKroneckerSection k K Y₁ i g) =
    (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom.hom
      (cochainKroneckerSection k K Y₂ i (g ≫ h))
  rw [homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom k K h i]
  simp only [cochainKroneckerSection, ModuleCat.comp_apply, LinearMap.comp_apply,
    Linear.leftComp_apply, ← ModuleCat.comp_apply
      (linearHomComplexSingle₀HomologyIso k K Y₁ i).inv
      (linearHomComplexSingle₀HomologyIso k K Y₁ i).hom,
    ← ModuleCat.comp_apply
      (linearHomComplexSingle₀HomologyIso k K Y₂ i).inv
      (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom,
    Iso.inv_hom_id, ModuleCat.id_apply]
  set X : _root_.ChainComplex C ℤ := negChain K
  set r := retraction (X.iCycles i) ≫ X.homologyπ i
  have hr := ChainComplex.d_comp_retraction_iCycles_comp_homologyπ
    (X := X) ((ComplexShape.up ℤ).next i) i
  set a := (negChainHomologyIso K (rfl : -i = -i)).hom ≫ g
  have h₁ : ChainComplex.kroneckerSection k X Y₁ i a =
      (X.linearYonedaObj k Y₁).homologyπ i (ChainComplex.cocycleOfComp k Y₁ r hr a) :=
    ChainComplex.kroneckerSection_apply i a _
      ((ChainComplex.iCycles_cocycleOfComp r hr a).trans (Category.assoc ..))
  rw [h₁, ← Category.assoc (negChainHomologyIso K (rfl : -i = -i)).hom g h]
  -- Unfold `.hom` application on `ModuleCat` morphisms to function application.
  change homologyMap (X.linearYonedaObjMap k h) i
      ((X.linearYonedaObj k Y₁).homologyπ i (ChainComplex.cocycleOfComp k Y₁ r hr a)) =
    ChainComplex.kroneckerSection k X Y₂ i (a ≫ h)
  rw [X.homologyMap_linearYonedaObjMap_homologyπ_apply k h i]
  symm
  apply ChainComplex.kroneckerSection_apply
  rw [X.iCycles_cyclesMap_linearYonedaObjMap_apply k h i,
    ChainComplex.iCycles_cocycleOfComp, Category.assoc, Category.assoc]

end Kronecker

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] (k : Type*) [CommRing k] [Linear k C]
  [HasExt.{w} C] (K : CochainComplex C ℤ) (Y : C)

/-- **The `Ext` inclusion in the universal coefficient sequence for `linearHomComplex`**: for
`i + j = 1` (that is, `j = 1 - i`), the `k`-linear map
`Ext¹(Hʲ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` sending an extension of `Hʲ(K)` by `Y` to its coboundary
class in degree-`i` cohomology. -/
def cochainExtToHomology {i j : ℤ} (hij : i + j = 1) [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    Ext.{w} (K.homology j) Y 1 →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  have hji : -(i - 1) = j := by omega
  have : Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
    projective_negChain_cycles K hji
  have : IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
    isSplitMono_negChain_iCycles K hji
  (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom.comp <|
    (ChainComplex.extToHomology.{w} k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i (i - 1)).comp
        (extLinearEquivOfIso k (negChainHomologyIso K hji).symm (Iso.refl Y) 1).toLinearMap

/-- **Injectivity of `cochainExtToHomology`**: in bidegree `i + j = 1`, the map
`Ext¹(Hʲ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem cochainExtToHomology_injective {k} [CommRing k] [Linear k C] {K : CochainComplex C ℤ}
    {Y : C} {i j : ℤ} (hij : i + j = 1) [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    Function.Injective (cochainExtToHomology.{w} k K Y hij) := by
  have hji : -(i - 1) = j := by omega
  have : Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
    projective_negChain_cycles K hji
  have : IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
    isSplitMono_negChain_iCycles K hji
  exact (linearHomComplexSingle₀HomologyIso k K Y i).symm.toLinearEquiv.injective.comp <|
    (ChainComplex.extToHomology_injective (k := k)
      (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y)
      (show i - 1 + 1 = i by omega)).comp
        (extLinearEquivOfIso k (negChainHomologyIso K hji).symm (Iso.refl Y) 1).injective

/-- **Middle exactness of the universal coefficient sequence for `linearHomComplex`**: for
`i + j = 1`, the image of `cochainExtToHomology` is the kernel of `cochainKronecker`. -/
theorem exact_cochainExtToHomology_cochainKronecker {k} [CommRing k] [Linear k C]
    {K : CochainComplex C ℤ} {Y : C} {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    Function.Exact (cochainExtToHomology.{w} k K Y hij) (cochainKronecker k K Y i) := by
  have hji : -(i - 1) = j := by omega
  have : Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
    projective_negChain_cycles K hji
  have : IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
    isSplitMono_negChain_iCycles K hji
  have hex := ChainComplex.exact_extToHomology_kronecker.{w} (k := k)
    (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y)
    (show i - 1 + 1 = i by omega)
  have hinj := (bijective_leftComp_iso_inv (k := k) (Y := Y)
    (negChainHomologyIso K (rfl : -i = -i))).1
  intro x
  -- Transport exactness across the outer bijections and the middle cohomology isomorphism.
  let eH := (linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv
  have hkr : cochainKronecker k K Y i x = 0 ↔
      ChainComplex.kronecker k (K.restriction ComplexShape.embeddingDownIntUpInt) Y i
        (eH x) = 0 := by
    -- Expose the outer `Linear.leftComp` factor of `cochainKronecker` so `hinj` removes it.
    change Linear.leftComp k Y (negChainHomologyIso K (rfl : -i = -i)).inv _ = 0 ↔ _
    exact hinj.eq_iff' (map_zero _)
  rw [hkr, hex (eH x)]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨extLinearEquivOfIso k (negChainHomologyIso K hji).symm (Iso.refl Y) 1 |>.symm e, ?_⟩
    apply eH.injective
    simpa [cochainExtToHomology, eH, ← ModuleCat.comp_apply] using he
  · rintro ⟨e, rfl⟩
    refine ⟨extLinearEquivOfIso k (negChainHomologyIso K hji).symm (Iso.refl Y) 1 e, ?_⟩
    simp [cochainExtToHomology, eH]

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
lemma cochainUniversalCoefficientEquiv_symm_apply {k} [CommRing k] [Linear k C]
    {K : CochainComplex C ℤ} {Y : C} {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (e : Ext.{w} (K.homology j) Y 1) (g : K.homology (-i) ⟶ Y) :
    (cochainUniversalCoefficientEquiv.{w} k K Y hij).symm (e, g) =
      cochainExtToHomology k K Y hij e + cochainKroneckerSection k K Y i g := by
  let S := (exact_cochainExtToHomology_cochainKronecker.{w} (k := k) (K := K) (Y := Y)
    hij).splitSurjectiveEquiv (cochainExtToHomology_injective hij)
  let sec : { s // (cochainKronecker k K Y i).comp s = LinearMap.id } :=
    ⟨cochainKroneckerSection k K Y i, LinearMap.ext (cochainKronecker_cochainKroneckerSection i)⟩
  have he : (cochainUniversalCoefficientEquiv.{w} k K Y hij).symm (e, 0) =
      cochainExtToHomology k K Y hij e :=
    (LinearMap.congr_fun (S sec).property.left e).symm
  have hg : (cochainUniversalCoefficientEquiv.{w} k K Y hij).symm (0, g) =
      cochainKroneckerSection k K Y i g :=
    LinearMap.congr_fun (congrArg Subtype.val (S.left_inv sec)) g
  calc
    (cochainUniversalCoefficientEquiv.{w} k K Y hij).symm (e, g) =
        (cochainUniversalCoefficientEquiv.{w} k K Y hij).symm (e, 0) +
          (cochainUniversalCoefficientEquiv.{w} k K Y hij).symm (0, g) := by
      rw [← map_add]; simp
    _ = _ := by rw [he, hg]

@[simp]
lemma cochainUniversalCoefficientEquiv_apply_snd {k} [CommRing k] [Linear k C]
    {K : CochainComplex C ℤ} {Y : C} {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    (cochainUniversalCoefficientEquiv.{w} k K Y hij x).2 = cochainKronecker k K Y i x :=
  (LinearMap.congr_fun
    ((exact_cochainExtToHomology_cochainKronecker.{w} (k := k) (K := K) (Y := Y)
      hij).splitSurjectiveEquiv (cochainExtToHomology_injective hij) _).property.right x).symm

/-- **Naturality of `cochainExtToHomology` in the complex**: pulling an extension back along
`homologyMap φ j` and including it into cohomology agrees with including first and pulling back
along `linearHomComplexPrecomp k φ _`. -/
theorem cochainExtToHomology_naturality {k} [CommRing k] [Linear k C]
    {K₁ K₂ : CochainComplex C ℤ} {Y : C} (φ : K₁ ⟶ K₂) {i j : ℤ} (hij : i + j = 1)
    [Projective (K₁.cycles j)] [IsSplitMono (K₁.iCycles j)]
    [Projective (K₂.cycles j)] [IsSplitMono (K₂.iCycles j)]
    (e : Ext.{w} (K₂.homology j) Y 1) :
    cochainExtToHomology k K₁ Y hij ((Ext.mk₀ (homologyMap φ j)).comp e (zero_add 1)) =
      (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom
        (cochainExtToHomology k K₂ Y hij e) := by
  have hji : -(i - 1) = j := by omega
  have : Projective ((K₁.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
    projective_negChain_cycles K₁ hji
  have : IsSplitMono ((K₁.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
    isSplitMono_negChain_iCycles K₁ hji
  have : Projective ((K₂.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
    projective_negChain_cycles K₂ hji
  have : IsSplitMono ((K₂.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
    isSplitMono_negChain_iCycles K₂ hji
  apply (linearHomComplexSingle₀HomologyIso k K₁ Y i).toLinearEquiv.injective
  have hext : (extLinearEquivOfIso k (negChainHomologyIso K₁ hji).symm (Iso.refl Y) 1)
      ((Ext.mk₀ (homologyMap φ j)).comp e (zero_add 1)) =
      (Ext.mk₀ (homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt)
        (i - 1))).comp
          ((extLinearEquivOfIso k (negChainHomologyIso K₂ hji).symm (Iso.refl Y) 1) e)
            (zero_add 1) := by
    simp only [extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, negChainHomologyIso_hom_naturality φ hji]
  -- Rewrite `toLinearEquiv` application on the right into a categorical composite so
  -- `homologyMap_precomp_linearHomComplexSingle₀HomologyIso_hom` applies.
  change (linearHomComplexSingle₀HomologyIso k K₁ Y i).hom.hom
      (cochainExtToHomology k K₁ Y hij ((Ext.mk₀ (homologyMap φ j)).comp e (zero_add 1))) =
    ((homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i ≫
      (linearHomComplexSingle₀HomologyIso k K₁ Y i).hom).hom)
        (cochainExtToHomology k K₂ Y hij e)
  rw [homologyMap_precomp_linearHomComplexSingle₀HomologyIso_hom k φ Y i]
  simp only [cochainExtToHomology, ModuleCat.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ← ModuleCat.comp_apply
      (linearHomComplexSingle₀HomologyIso k K₁ Y i).inv
      (linearHomComplexSingle₀HomologyIso k K₁ Y i).hom,
    ← ModuleCat.comp_apply
      (linearHomComplexSingle₀HomologyIso k K₂ Y i).inv
      (linearHomComplexSingle₀HomologyIso k K₂ Y i).hom,
    Iso.inv_hom_id, ModuleCat.id_apply, hext]
  exact ChainComplex.extToHomology_naturality
    (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i (i - 1) _

/-- **Naturality of `cochainExtToHomology` in the coefficient object**: pushing an extension forward
along `g : Y₁ ⟶ Y₂` and including it into cohomology agrees with including first and applying
`linearHomComplexPostcomp`. -/
theorem cochainExtToHomology_coefficient_naturality {k} [CommRing k] [Linear k C]
    {K : CochainComplex C ℤ} {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] (e : Ext.{w} (K.homology j) Y₁ 1) :
    cochainExtToHomology k K Y₂ hij (e.comp (Ext.mk₀ g) (add_zero 1)) =
      (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom
        (cochainExtToHomology k K Y₁ hij e) := by
  have hji : -(i - 1) = j := by omega
  have : Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
    projective_negChain_cycles K hji
  have : IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
    isSplitMono_negChain_iCycles K hji
  apply (linearHomComplexSingle₀HomologyIso k K Y₂ i).toLinearEquiv.injective
  have hext : (extLinearEquivOfIso k (negChainHomologyIso K hji).symm (Iso.refl Y₂) 1)
      (e.comp (Ext.mk₀ g) (add_zero 1)) =
      ((extLinearEquivOfIso k (negChainHomologyIso K hji).symm (Iso.refl Y₁) 1) e).comp
        (Ext.mk₀ g) (add_zero 1) := by
    simp only [extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    exact (Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)).symm
  -- Rewrite the right-hand side as a categorical composite in `ModuleCat` so
  -- `homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom` applies.
  change (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom.hom
      (cochainExtToHomology k K Y₂ hij (e.comp (Ext.mk₀ g) (add_zero 1))) =
    ((homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i ≫
      (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom).hom)
        (cochainExtToHomology k K Y₁ hij e)
  rw [homologyMap_postcomp_linearHomComplexSingle₀HomologyIso_hom k K g i]
  simp only [cochainExtToHomology, ModuleCat.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ← ModuleCat.comp_apply
      (linearHomComplexSingle₀HomologyIso k K Y₁ i).inv
      (linearHomComplexSingle₀HomologyIso k K Y₁ i).hom,
    ← ModuleCat.comp_apply
      (linearHomComplexSingle₀HomologyIso k K Y₂ i).inv
      (linearHomComplexSingle₀HomologyIso k K Y₂ i).hom,
    Iso.inv_hom_id, ModuleCat.id_apply, hext]
  exact ChainComplex.extToHomology_coefficient_naturality g i (i - 1) _

end Ext

section NonNaturality

private abbrev mulTwoObj (i : ℤ) : ModuleCat.{0} ℤ :=
  if i = 0 then ModuleCat.of ℤ ℤ
  else if i = 1 then ModuleCat.of ℤ ℤ
  else ModuleCat.of ℤ PUnit

/-- The two-term bounded finite free `ℤ`-cochain complex `0 ⟶ ℤ xrightarrow{×2} ℤ ⟶ 0` in degrees
`0` and `1` witnessing that the universal coefficient splitting cannot be chosen naturally. -/
private def mulTwoCochainComplex : CochainComplex (ModuleCat.{0} ℤ) ℤ where
  X := mulTwoObj
  d i j :=
    if hi : i = 0 then
      if hj : j = 1 then
        eqToHom (by subst hi; rfl) ≫ ModuleCat.ofHom (2 • LinearMap.id) ≫
          eqToHom (by subst hj; rfl)
      else 0
    else 0
  shape i j hij := by
    simp only [ComplexShape.up_Rel] at hij
    split_ifs with hi hj
    · omega
    · rfl
    · rfl
  d_comp_d' i j k hij hjk := by
    simp only [ComplexShape.up_Rel] at hij hjk
    by_cases hi : i = 0
    · subst hi
      obtain rfl : j = 1 := by omega
      obtain rfl : k = 2 := by omega
      simp
    · rw [dite_eq_right hi, zero_comp]

private instance (i : ℤ) : Module.Free ℤ (mulTwoCochainComplex.X i) := by
  by_cases hi0 : i = 0
  · subst hi0; exact inferInstanceAs (Module.Free ℤ ℤ)
  · by_cases hi1 : i = 1
    · subst hi1; exact inferInstanceAs (Module.Free ℤ ℤ)
    · have hX : mulTwoCochainComplex.X i = ModuleCat.of ℤ PUnit := by
        simp [mulTwoCochainComplex, mulTwoObj, hi0, hi1]
      rw [hX]
      exact inferInstanceAs (Module.Free ℤ PUnit)

private instance (i : ℤ) : Module.Finite ℤ (mulTwoCochainComplex.X i) := by
  by_cases hi0 : i = 0
  · subst hi0; exact inferInstanceAs (Module.Finite ℤ ℤ)
  · by_cases hi1 : i = 1
    · subst hi1; exact inferInstanceAs (Module.Finite ℤ ℤ)
    · have hX : mulTwoCochainComplex.X i = ModuleCat.of ℤ PUnit := by
        simp [mulTwoCochainComplex, mulTwoObj, hi0, hi1]
      rw [hX]
      exact inferInstanceAs (Module.Finite ℤ PUnit)

private instance : mulTwoCochainComplex.IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  -- For `i < 0`, `mulTwoObj i` reduces to the zero `ℤ`-module `PUnit`.
  change IsZero (mulTwoObj i)
  unfold mulTwoObj
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact ModuleCat.isZero_of_subsingleton _

private instance : mulTwoCochainComplex.IsStrictlyLE 1 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  -- For `i > 1`, `mulTwoObj i` reduces to the zero `ℤ`-module `PUnit`.
  change IsZero (mulTwoObj i)
  unfold mulTwoObj
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  exact ModuleCat.isZero_of_subsingleton _

private lemma isZero_homology_zero_mulTwoCochainComplex :
    IsZero (mulTwoCochainComplex.homology 0) := by
  have hmono : Mono (mulTwoCochainComplex.d 0 1) := by
    rw [ModuleCat.mono_iff_injective]
    intro a b hab
    let a' : ℤ := a
    let b' : ℤ := b
    have hab' : ((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) a' =
        ((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) b' := hab
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hab'
    exact (by omega : a' = b')
  have hex : mulTwoCochainComplex.ExactAt 0 := by
    rw [HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    exact ((mulTwoCochainComplex.sc' (-1) 0 1).exact_iff_mono rfl).2 hmono
  exact hex.isZero_homology

/-- **No simultaneous natural splitting of the cochain universal coefficient sequence exists.**
Even among strictly bounded finite free `ℤ`-cochain complexes with dualizing target `ℤ`, there is
no family of additive sections `s K : (H⁰(K) ⟶ ℤ) →+ H⁰(Hom(K, ℤ[0]))` of `cochainKronecker` in
degree `0` that commutes with chain maps. -/
theorem not_exists_natural_section_cochainKronecker :
    ¬ ∃ s : ∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
        [∀ i, Module.Free ℤ (K.X i)] [∀ i, Module.Finite ℤ (K.X i)]
        [K.IsStrictlyGE 0] [K.IsStrictlyLE 1],
        (K.homology 0 ⟶ ModuleCat.of ℤ ℤ) →+
          (linearHomComplex ℤ K ((singleFunctor (ModuleCat.{0} ℤ) 0).obj
            (ModuleCat.of ℤ ℤ))).homology 0,
      (∀ (K : CochainComplex (ModuleCat.{0} ℤ) ℤ)
          [∀ i, Module.Free ℤ (K.X i)] [∀ i, Module.Finite ℤ (K.X i)]
          [K.IsStrictlyGE 0] [K.IsStrictlyLE 1] (g : K.homology 0 ⟶ ModuleCat.of ℤ ℤ),
        cochainKronecker ℤ K (ModuleCat.of ℤ ℤ) 0 (s K g) = g) ∧
      (∀ (K₁ K₂ : CochainComplex (ModuleCat.{0} ℤ) ℤ)
          [∀ i, Module.Free ℤ (K₁.X i)] [∀ i, Module.Finite ℤ (K₁.X i)]
          [K₁.IsStrictlyGE 0] [K₁.IsStrictlyLE 1]
          [∀ i, Module.Free ℤ (K₂.X i)] [∀ i, Module.Finite ℤ (K₂.X i)]
          [K₂.IsStrictlyGE 0] [K₂.IsStrictlyLE 1]
          (φ : K₁ ⟶ K₂) (g : K₂.homology 0 ⟶ ModuleCat.of ℤ ℤ),
        (homologyMap (linearHomComplexPrecomp ℤ φ
          ((singleFunctor (ModuleCat.{0} ℤ) 0).obj (ModuleCat.of ℤ ℤ))) 0).hom (s K₂ g) =
            s K₁ (homologyMap φ 0 ≫ g)) := by
  rintro ⟨s, hs_sec, hs_nat⟩
  let Z := ModuleCat.of ℤ ℤ
  let K₂ : CochainComplex (ModuleCat.{0} ℤ) ℤ := (singleFunctor (ModuleCat.{0} ℤ) 0).obj Z
  have (i : ℤ) : Module.Free ℤ (K₂.X i) := by
    by_cases hi : i = 0
    · subst hi
      exact Module.Free.of_equiv (singleObjXSelf (ComplexShape.up ℤ) 0 Z).symm.toLinearEquiv
    · have hz := isZero_single_obj_X (ComplexShape.up ℤ) 0 Z i hi
      have : Subsingleton (K₂.X i) := ModuleCat.isZero_iff_subsingleton.1 hz
      infer_instance
  have (i : ℤ) : Module.Finite ℤ (K₂.X i) := by
    by_cases hi : i = 0
    · subst hi
      exact Module.Finite.equiv (singleObjXSelf (ComplexShape.up ℤ) 0 Z).symm.toLinearEquiv
    · have hz := isZero_single_obj_X (ComplexShape.up ℤ) 0 Z i hi
      have : Subsingleton (K₂.X i) := ModuleCat.isZero_iff_subsingleton.1 hz
      infer_instance
  have : K₂.IsStrictlyLE 1 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact isZero_single_obj_X (ComplexShape.up ℤ) 0 Z i (by omega)
  -- Map `mulTwoCochainComplex ⟶ K₂` as the identity in degree `0` and `0` elsewhere.
  let φ₀ : mulTwoCochainComplex.X 0 ⟶ Z := 𝟙 Z
  let φ : mulTwoCochainComplex ⟶ K₂ :=
    HomologicalComplex.mkHomToSingle φ₀ (fun i hi ↦
      (mulTwoCochainComplex.isZero_of_isStrictlyGE 0 i
        (by simp only [ComplexShape.up_Rel] at hi; omega)).eq_of_src _ _)
  have hφ0 : φ.f 0 = φ₀ ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 Z).inv :=
    HomologicalComplex.mkHomToSingle_f _ _
  let g₀ : K₂.homology 0 ⟶ Z := (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 Z).hom
  let L₂ := linearHomComplex ℤ K₂ K₂
  let L₁ := linearHomComplex ℤ mulTwoCochainComplex K₂
  -- Lift `s K₂ g₀` to a degree-`0` cocycle `cyc₂` and compute its underlying morphism via
  -- `homologyπ_cochainKronecker`.
  obtain ⟨cyc₂, hcyc₂⟩ := L₂.moduleCat_homologyπ_surjective 0 (s K₂ g₀)
  have hf₂ : Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0) ((L₂.iCycles 0).hom cyc₂) =
      (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom := by
    have hkr := homologyπ_cochainKronecker (k := ℤ) (K := K₂) (Y := Z) 0 cyc₂
    rw [hcyc₂, hs_sec K₂ g₀] at hkr
    have hkr' := congrArg ((singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 Z).inv ≫ ·) hkr
    -- Unfold `K₂`, `g₀`, and `-0 = 0` so the single-complex `@[simp]` lemmas match directly.
    change (singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 Z).inv ≫
        ((HomologicalComplex.single (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).obj Z).homologyπ 0 ≫
          (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 Z).hom =
      (singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 Z).inv ≫
        ((HomologicalComplex.single (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) 0).obj Z).iCycles 0 ≫
          Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0) ((L₂.iCycles 0).hom cyc₂) at hkr'
    rw [homologyπ_singleObjHomologySelfIso_hom, Iso.inv_hom_id,
      singleObjCyclesSelfIso_inv_iCycles_assoc] at hkr'
    simpa using congrArg ((singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom ≫ ·) hkr'.symm
  -- On `mulTwoCochainComplex`, `H⁰ = 0`, so pulling `s K₂ g₀` back along `φ` gives `0` in `H⁰(L₁)`.
  have hφg : homologyMap φ 0 ≫ g₀ = 0 :=
    isZero_homology_zero_mulTwoCochainComplex.eq_of_src _ _
  have hpull := hs_nat mulTwoCochainComplex K₂ φ g₀
  rw [← hcyc₂, hφg, map_zero, HomologicalComplex.moduleCat_homologyMap_homologyπ] at hpull
  -- Hence the pulled-back cocycle is a coboundary of some `y : L₁.X (-1)`.
  obtain ⟨y, hy⟩ :=
    (L₁.moduleCat_homologyπ_eq_zero_iff (m := -1) (by simp) _).1 hpull
  have hdy : (L₁.d (-1) 0).hom y =
      ((linearHomComplexPrecomp ℤ φ K₂).f 0).hom ((L₂.iCycles 0).hom cyc₂) := by
    have := congrArg (L₁.iCycles 0).hom hy
    simpa only [HomologicalComplex.moduleCat_iCycles_toCycles_apply,
      HomologicalComplex.moduleCat_iCycles_cyclesMap_apply] using this
  -- Translate `hdy` through `Cochain.toSingleLinearEquiv` in degree `0`: `2 • g = 𝟙 ℤ`.
  let g : mulTwoCochainComplex.X 1 ⟶ Z :=
    Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel (-1)) y
  have hg : mulTwoCochainComplex.d 0 1 ≫ g = 𝟙 Z := by
    have hd := toSingleLinearEquiv_linearHomComplex_d_apply (k := ℤ) mulTwoCochainComplex Z (-1) y
    have hpre : Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0)
        (((linearHomComplexPrecomp ℤ φ K₂).f 0).hom ((L₂.iCycles 0).hom cyc₂)) = 𝟙 Z := by
      have hz₂ := Cochain.toSingleMk_toSingleEquiv (neg_add_cancel 0) ((L₂.iCycles 0).hom cyc₂)
      rw [linearHomComplexPrecomp_f_apply, ← hz₂, ← Cochain.toSingleMk_precomp]
      have hf₂' : Cochain.toSingleEquiv (neg_add_cancel 0) ((L₂.iCycles 0).hom cyc₂) =
          (singleObjXSelf (ComplexShape.up ℤ) 0 Z).hom := hf₂
      -- Unfold `Cochain.toSingleLinearEquiv` and `-0 = 0` so `toSingleEquiv_toSingleMk` applies.
      change Cochain.toSingleEquiv (add_zero (0 : ℤ))
          (Cochain.toSingleMk (φ.f 0 ≫ Cochain.toSingleEquiv (neg_add_cancel 0)
            ((L₂.iCycles 0).hom cyc₂)) (add_zero (0 : ℤ))) = 𝟙 Z
      rw [Cochain.toSingleEquiv_toSingleMk, hf₂', hφ0, Category.assoc, Iso.inv_hom_id,
        Category.comp_id]
    -- Fold `L₁` and `g` and simplify `-1 + 1 = 0` in `hd` so `hdy` and `hpre` rewrite directly.
    change Cochain.toSingleLinearEquiv (R := ℤ) (neg_add_cancel 0) ((L₁.d (-1) 0).hom y) =
      (-1 + 1).negOnePow • (mulTwoCochainComplex.d 0 1 ≫ g) at hd
    rw [hdy, hpre] at hd
    simpa using hd.symm
  let g' : ℤ →ₗ[ℤ] ℤ := g.hom
  have h1 : g' (((2 : ℤ) • LinearMap.id : ℤ →ₗ[ℤ] ℤ) 1) = (1 : ℤ) :=
    ConcreteCategory.congr_hom hg (1 : ℤ)
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, mul_one] at h1
  have h2 : g' 2 = 2 * g' 1 := by
    simpa using g'.map_smul (2 : ℤ) (1 : ℤ)
  omega

end NonNaturality

end TauCeti
