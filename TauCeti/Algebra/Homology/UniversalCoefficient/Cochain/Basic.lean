/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import TauCeti.Algebra.Homology.LinearHomComplex.Single
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality

/-!
# The universal coefficient sequence for cochain complexes

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear abelian category `C`, and let `Y : C`.
In `TauCeti.Algebra.Homology.LinearHomComplex.Single`, regrading `K` into the chain complex
`X = K.restriction ComplexShape.embeddingDownIntUpInt` with `Xᵢ = K⁻ⁱ` identifies
`CochainComplex.linearHomComplex k K ((singleFunctor C 0).obj Y)` with
`ChainComplex.linearYonedaObj X k Y` via `CochainComplex.linearHomComplexSingle₀Iso`, inducing a
sign-free `k`-linear cohomology equivalence `CochainComplex.linearHomComplexSingle₀HomologyEquiv`
natural in both `K` and `Y`.

Transporting `TauCeti.ChainComplex` along this equivalence and
`HomologicalComplex.restrictionHomologyIso` gives the cochain Kronecker map
`CochainComplex.kronecker : Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` and its section
`CochainComplex.kroneckerSection` over any ring `k`. When `Y` is injective or when
`K.iCycles (1 - i)` and `K.iCycles (-i)` split and `H¹⁻ⁱ(K)` is projective, the Kronecker map is a
`k`-linear equivalence (`CochainComplex.kroneckerEquiv`,
`CochainComplex.kroneckerEquivOfProjectiveHomology`).

When `k` is commutative and `C` has `Ext`, this further gives the universal coefficient sequence for
cochain complexes:

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`

when `K.cycles (1 - i)` is projective and `K.iCycles (1 - i)` and `K.iCycles (-i)` are split
monomorphisms (`CochainComplex.extToHomology`, `CochainComplex.kronecker`,
`CochainComplex.kroneckerSection`, `CochainComplex.universalCoefficientEquiv`). Both maps in the
sequence are natural in `K` and `Y`, and the chosen splitting commutes with morphisms in `Y`.
Module-category bimodule equivariance and principal-ideal-domain specializations are developed in
`TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Module`.

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
open CochainComplex.HomComplex

namespace CochainComplex

universe w' w v u

section RegradeHelpers

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma embeddingDownIntUpInt_f_eq {j j' : ℤ} (hj' : -j = j') :
    ComplexShape.embeddingDownIntUpInt.f j = j' := by
  simpa using hj'

private def regradeCyclesIso (K : CochainComplex C ℤ) {j j' : ℤ} (hj' : -j = j') :
    (K.restriction ComplexShape.embeddingDownIntUpInt).cycles j ≅ K.cycles j' :=
  K.restrictionCyclesIso ComplexShape.embeddingDownIntUpInt j (j - 1) (by simp)
    (k' := j' + 1)
    (hj' := embeddingDownIntUpInt_f_eq hj')
    (hk' := embeddingDownIntUpInt_f_eq (by omega))
    (by simp)

private def regradeHomologyIso (K : CochainComplex C ℤ) {j j' : ℤ} (hj' : -j = j') :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homology j ≅ K.homology j' :=
  K.restrictionHomologyIso ComplexShape.embeddingDownIntUpInt (j + 1) j (j - 1) (by simp) (by simp)
    (i' := j' - 1) (k' := j' + 1)
    (hi' := embeddingDownIntUpInt_f_eq (by omega))
    (hj' := embeddingDownIntUpInt_f_eq hj')
    (hk' := embeddingDownIntUpInt_f_eq (by omega))
    (by simp) (by simp)

@[reassoc]
private lemma homologyπ_regradeHomologyIso_hom (K : CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ j ≫
        (regradeHomologyIso K hj').hom =
      (regradeCyclesIso K hj').hom ≫ K.homologyπ j' :=
  K.homologyπ_restrictionHomologyIso_hom _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
private lemma homologyπ_regradeHomologyIso_inv (K : CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') :
    K.homologyπ j' ≫ (regradeHomologyIso K hj').inv =
      (regradeCyclesIso K hj').inv ≫
        (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ j :=
  K.homologyπ_restrictionHomologyIso_inv _ _ _ _ _ _ _ _ _ _ _

@[reassoc]
private lemma regradeHomologyIso_hom_naturality {K' K : CochainComplex C ℤ} (φ : K' ⟶ K)
    {j j' : ℤ} (hj' : -j = j') :
    homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) j ≫
        (regradeHomologyIso K hj').hom =
      (regradeHomologyIso K' hj').hom ≫ homologyMap φ j' := by
  have hj'' := embeddingDownIntUpInt_f_eq hj'
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

private lemma projective_restriction_cycles (K : CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') [Projective (K.cycles j')] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles j) :=
  Projective.of_iso (regradeCyclesIso K hj').symm inferInstance

private lemma projective_restriction_homology (K : CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') [Projective (K.homology j')] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).homology j) :=
  Projective.of_iso (regradeHomologyIso K hj').symm inferInstance

private lemma isSplitMono_restriction_iCycles (K : CochainComplex C ℤ) {j j' : ℤ}
    (hj' : -j = j') [IsSplitMono (K.iCycles j')] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles j) :=
  ⟨⟨{ retraction := (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (embeddingDownIntUpInt_f_eq hj')).hom ≫
        retraction (K.iCycles j') ≫ (regradeCyclesIso K hj').inv
      id := by
        let e := ComplexShape.embeddingDownIntUpInt
        have hj'' := embeddingDownIntUpInt_f_eq hj'
        have hk'' := embeddingDownIntUpInt_f_eq (j := j - 1) (j' := j' + 1) (by omega)
        rw [← restrictionCyclesIso_hom_iCycles_assoc K e j (j - 1) (by simp) hj'' hk'' (by simp),
          IsSplitMono.id_assoc]
        exact (regradeCyclesIso K hj').hom_inv_id }⟩⟩

end RegradeHelpers

section UniversalCoefficient

variable {C : Type u} [Category.{v} C] [Abelian C]

section Ring

variable {K : CochainComplex C ℤ} {k : Type w} [Ring k] [Linear k C] {Y : C}

variable (K k Y) in
/-- **The Kronecker map for cochain complexes**
`Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`: evaluates a degree-`i` cohomology class of
`linearHomComplex k K ((singleFunctor C 0).obj Y)` on homology classes of `K` in degree `-i`. -/
def kronecker (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i →ₗ[k] (K.homology (-i) ⟶ Y) :=
  Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).inv ∘ₗ
    TauCeti.ChainComplex.kronecker k (K.restriction ComplexShape.embeddingDownIntUpInt) Y i ∘ₗ
    (K.linearHomComplexSingle₀HomologyEquiv k Y i).toLinearMap

/-- **The Kronecker map on cocycle classes**: evaluating the class of a cocycle `φ` on the class
of a cycle of `K` in degree `-i` applies `Cochain.toSingleEquiv (neg_add_cancel i)` to `φ`. -/
@[reassoc (attr := simp)]
lemma kronecker_homologyπ (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    K.homologyπ (-i) ≫
        K.kronecker k Y i ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      K.iCycles (-i) ≫ Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
  let X : ChainComplex C ℤ := K.restriction ComplexShape.embeddingDownIntUpInt
  have hd' : K.d (-(i + 1)) (-i) ≫ Cochain.toSingleEquiv (neg_add_cancel i)
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) = 0 := by
    have h0 := (linearHomComplex k K ((singleFunctor C 0).obj Y)).moduleCat_d_iCycles_apply i
      (i + 1) φ
    have h1 := K.toSingleLinearEquiv_linearHomComplex_d_apply k Y i
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
  -- `X.X i` is `K.X (-i)` up to unfolding `restriction`, so `eqToHom` is reflexive.
  erw [eqToHom_refl, Category.id_comp]
  exact hψ

/-- **Naturality of the cochain Kronecker map** in the source cochain complex `K`. -/
lemma kronecker_naturality {K' : CochainComplex C ℤ} (φ : K' ⟶ K) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K'.kronecker k Y i
        (homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i x) =
      homologyMap φ (-i) ≫ K.kronecker k Y i x := by
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
    K.kronecker k Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      K.kronecker k Y i x ≫ g := by
  simp only [kronecker, LinearMap.comp_apply, LinearEquiv.coe_coe, Linear.leftComp_apply,
    linearHomComplexSingle₀HomologyEquiv_postcomp,
    TauCeti.ChainComplex.kronecker_coefficient_naturality, Category.assoc]

/-- For an injective object `Y`, the cochain Kronecker map is bijective. -/
theorem kronecker_bijective [Injective Y] (i : ℤ) :
    Function.Bijective (K.kronecker k Y i) := by
  have h1 : Function.Bijective (Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).inv) :=
    ⟨fun a b h ↦ (cancel_epi _).1 h, fun f ↦ ⟨(regradeHomologyIso K rfl).hom ≫ f, by simp⟩⟩
  exact h1.comp ((TauCeti.ChainComplex.kronecker_bijective i).comp
    (K.linearHomComplexSingle₀HomologyEquiv k Y i).bijective)

variable (K k Y) in
/-- For an injective object `Y`, the cochain Kronecker map as a `k`-linear equivalence
`Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def kroneckerEquiv [Injective Y] (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (K.kronecker k Y i) (kronecker_bijective i)

@[simp]
lemma kroneckerEquiv_apply [Injective Y] (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K.kroneckerEquiv k Y i x = K.kronecker k Y i x :=
  (rfl)

variable (K k Y) in
/-- **The splitting of the cochain universal coefficient sequence**: given a retraction of
`K.iCycles (-i)`, the `k`-linear right inverse `(H⁻ⁱ(K) ⟶ Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` of
`CochainComplex.kronecker` sending `g` to the cocycle class induced by the retraction on cycles. -/
def kroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    (K.homology (-i) ⟶ Y) →ₗ[k] (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  have := isSplitMono_restriction_iCycles K (rfl : -i = -i)
  (K.linearHomComplexSingle₀HomologyEquiv k Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.kroneckerSection k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i ∘ₗ
    Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).hom

/-- `CochainComplex.kroneckerSection` is a right inverse of `kronecker`. -/
@[simp]
lemma kronecker_kroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y) :
    K.kronecker k Y i (K.kroneckerSection k Y i g) = g := by
  have := isSplitMono_restriction_iCycles K (rfl : -i = -i)
  simp only [kronecker, kroneckerSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, TauCeti.ChainComplex.kronecker_kroneckerSection,
    Linear.leftComp_apply, Iso.inv_hom_id_assoc]

/-- `CochainComplex.kroneckerSection` commutes with postcomposition by a coefficient morphism
`g : Y ⟶ Z`, for the same chosen retraction of `K.iCycles (-i)`. -/
lemma kroneckerSection_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (f : K.homology (-i) ⟶ Y) :
    homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i
        (K.kroneckerSection k Y i f) =
      K.kroneckerSection k Z i (f ≫ g) := by
  have := isSplitMono_restriction_iCycles K (rfl : -i = -i)
  apply (K.linearHomComplexSingle₀HomologyEquiv k Z i).injective
  rw [linearHomComplexSingle₀HomologyEquiv_postcomp]
  simp only [kroneckerSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, TauCeti.ChainComplex.kroneckerSection_coefficient_naturality,
    Linear.leftComp_apply, Category.assoc]

/-- When `K.iCycles (-i)` is a split monomorphism, `CochainComplex.kronecker` is surjective. -/
theorem kronecker_surjective_of_isSplitMono (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    Function.Surjective (K.kronecker k Y i) :=
  fun g ↦ ⟨K.kroneckerSection k Y i g, kronecker_kroneckerSection i g⟩

/-- **The cochain universal coefficient theorem with projective `(1 - i)`-th cohomology**: when
`K.iCycles (1 - i)` and `K.iCycles (-i)` split and `K.homology (1 - i)` is projective, the
Kronecker map `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` is bijective over any ring `k`. -/
theorem kronecker_bijective_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    Function.Bijective (K.kronecker k Y i) := by
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (rfl : -i = -i)
  have := projective_restriction_homology K (neg_sub i 1)
  have h1 : Function.Bijective (Linear.leftComp k Y (regradeHomologyIso K (rfl : -i = -i)).inv) :=
    ⟨fun a b h ↦ (cancel_epi _).1 h, fun f ↦ ⟨(regradeHomologyIso K rfl).hom ≫ f, by simp⟩⟩
  exact h1.comp
    ((TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_of_add_one_eq
      (sub_add_cancel i 1)).comp (K.linearHomComplexSingle₀HomologyEquiv k Y i).bijective)

variable (K k Y) in
/-- When `K.iCycles (1 - i)` and `K.iCycles (-i)` split and `K.homology (1 - i)` is projective,
the cochain Kronecker map as a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def kroneckerEquivOfProjectiveHomology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (K.kronecker k Y i) (kronecker_bijective_of_projective_homology i)

@[simp]
lemma kroneckerEquivOfProjectiveHomology_apply (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K.kroneckerEquivOfProjectiveHomology k Y i x = K.kronecker k Y i x :=
  (rfl)

/-- If `K.iCycles (1 - i)` and `K.iCycles (-i)` split, `K.homology (1 - i)` is projective, and
`K.homology (-i)` vanishes, then `Hⁱ(Hom(K, Y[0]))` vanishes. -/
theorem isZero_homology_linearHomComplex_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] (hi : IsZero (K.homology (-i))) :
    IsZero ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) := by
  have : Subsingleton (K.homology (-i) ⟶ Y) := ⟨hi.eq_of_src⟩
  have := (kronecker_bijective_of_projective_homology (K := K) (k := k) (Y := Y) i).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end Ring

section CommRing

variable {K : CochainComplex C ℤ} {k : Type w} [CommRing k] [Linear k C] [HasExt.{w'} C] {Y : C}

variable (K k Y) in
/-- **The `Ext` term of the cochain universal coefficient sequence**: the `k`-linear map
`Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))`, defined when `K.cycles (1 - i)` is projective and
`K.iCycles (1 - i)` is a split monomorphism. -/
def extToHomology (i : ℤ) [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Ext.{w'} (K.homology (1 - i)) Y 1 →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  (K.linearHomComplexSingle₀HomologyEquiv k Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.extToHomology.{w'} k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i (i - 1) ∘ₗ
    (TauCeti.extLinearEquivOfIso k (regradeHomologyIso K (neg_sub i 1)).symm
      (Iso.refl Y) 1).toLinearMap

/-- **Injectivity in the cochain universal coefficient sequence**: the map
`Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem extToHomology_injective (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Function.Injective (extToHomology.{w'} K k Y i) := by
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  exact (K.linearHomComplexSingle₀HomologyEquiv k Y i).symm.injective.comp
    ((TauCeti.ChainComplex.extToHomology_injective (sub_add_cancel i 1)).comp
      (TauCeti.extLinearEquivOfIso k (regradeHomologyIso K (neg_sub i 1)).symm
        (Iso.refl Y) 1).injective)

/-- **Exactness in the middle of the cochain universal coefficient sequence**: the kernel of
`CochainComplex.kronecker` in degree `i` is the image of `CochainComplex.extToHomology`. -/
theorem exact_extToHomology_kronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Function.Exact (extToHomology.{w'} K k Y i) (K.kronecker k Y i) := by
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
    apply (K.linearHomComplexSingle₀HomologyEquiv k Y i).injective
    simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, TauCeti.extLinearEquivOfIso_apply, Iso.refl_hom, Iso.symm_inv,
      Ext.comp_mk₀_id, ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.mk₀_id_comp, he]
  · rintro ⟨e, rfl⟩
    refine ⟨TauCeti.extLinearEquivOfIso k (regradeHomologyIso K (neg_sub i 1)).symm
      (Iso.refl Y) 1 e, ?_⟩
    simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

/-- **Naturality of `CochainComplex.extToHomology` in `K`**: pulling an extension back along
`homologyMap φ (1 - i)` and including it in cohomology agrees with including first and pulling back
along `φ`. -/
lemma extToHomology_naturality {K' : CochainComplex C ℤ} (φ : K' ⟶ K) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Projective (K'.cycles (1 - i))] [IsSplitMono (K'.iCycles (1 - i))]
    (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    extToHomology.{w'} K' k Y i ((Ext.mk₀ (homologyMap φ (1 - i))).comp e (zero_add 1)) =
      homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i
        (extToHomology.{w'} K k Y i e) := by
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  have := projective_restriction_cycles K' (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K' (neg_sub i 1)
  apply (K'.linearHomComplexSingle₀HomologyEquiv k Y i).injective
  rw [linearHomComplexSingle₀HomologyEquiv_precomp]
  simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← TauCeti.ChainComplex.extToHomology_naturality]
  congr 1
  simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1), Ext.mk₀_comp_mk₀,
    regradeHomologyIso_hom_naturality]

/-- **Coefficient naturality of `CochainComplex.extToHomology` in `Y`**. -/
lemma extToHomology_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    extToHomology.{w'} K k Z i (e.comp (Ext.mk₀ g) (add_zero 1)) =
      homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i
        (extToHomology.{w'} K k Y i e) := by
  have := projective_restriction_cycles K (neg_sub i 1)
  have := isSplitMono_restriction_iCycles K (neg_sub i 1)
  apply (K.linearHomComplexSingle₀HomologyEquiv k Z i).injective
  rw [linearHomComplexSingle₀HomologyEquiv_postcomp]
  simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← TauCeti.ChainComplex.extToHomology_coefficient_naturality]
  congr 1
  simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)]

variable (K k Y) in
/-- **The split decomposition of the cochain universal coefficient sequence**:
`Hⁱ(Hom(K, Y[0])) ≃ₗ[k] Ext¹(H¹⁻ⁱ(K), Y) × (H⁻ⁱ(K) ⟶ Y)`, built from
`CochainComplex.extToHomology`, `CochainComplex.kronecker`, and `CochainComplex.kroneckerSection`.
It depends on the chosen retraction of `K.iCycles (-i)`, and commutes with coefficient morphisms
`Y ⟶ Z`. -/
def universalCoefficientEquiv (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      Ext.{w'} (K.homology (1 - i)) Y 1 × (K.homology (-i) ⟶ Y) :=
  ((exact_extToHomology_kronecker.{w'} (K := K) (k := k) (Y := Y) i).splitSurjectiveEquiv
    (extToHomology_injective i)
    ⟨K.kroneckerSection k Y i, LinearMap.ext (kronecker_kroneckerSection i)⟩).1

@[simp]
lemma universalCoefficientEquiv_symm_inl (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    (universalCoefficientEquiv.{w'} K k Y i).symm (e, 0) = extToHomology.{w'} K k Y i e :=
  (LinearMap.congr_fun
    ((exact_extToHomology_kronecker.{w'} (K := K) (k := k) (Y := Y) i).splitSurjectiveEquiv
      (extToHomology_injective i) _).property.left e).symm

@[simp]
lemma universalCoefficientEquiv_symm_inr (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y) :
    (universalCoefficientEquiv.{w'} K k Y i).symm (0, g) = K.kroneckerSection k Y i g :=
  LinearMap.congr_fun (congrArg Subtype.val
    (((exact_extToHomology_kronecker.{w'} (K := K) (k := k) (Y := Y) i).splitSurjectiveEquiv
      (extToHomology_injective i)).left_inv
      ⟨K.kroneckerSection k Y i, LinearMap.ext (kronecker_kroneckerSection i)⟩)) g

lemma universalCoefficientEquiv_symm_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : Ext.{w'} (K.homology (1 - i)) Y 1 × (K.homology (-i) ⟶ Y)) :
    (universalCoefficientEquiv.{w'} K k Y i).symm x =
      extToHomology.{w'} K k Y i x.1 + K.kroneckerSection k Y i x.2 := by
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, universalCoefficientEquiv_symm_inl, universalCoefficientEquiv_symm_inr]

@[simp]
lemma universalCoefficientEquiv_apply_snd (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    (universalCoefficientEquiv.{w'} K k Y i x).2 = K.kronecker k Y i x :=
  (LinearMap.congr_fun
    ((exact_extToHomology_kronecker.{w'} (K := K) (k := k) (Y := Y) i).splitSurjectiveEquiv
      (extToHomology_injective i) _).property.right x).symm

/-- For a fixed retraction of `K.iCycles (-i)`, the splitting
`CochainComplex.universalCoefficientEquiv` commutes with postcomposition by any coefficient morphism
`g : Y ⟶ Z`. -/
lemma universalCoefficientEquiv_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    universalCoefficientEquiv.{w'} K k Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      ((universalCoefficientEquiv.{w'} K k Y i x).1.comp (Ext.mk₀ g) (add_zero 1),
        (universalCoefficientEquiv.{w'} K k Y i x).2 ≫ g) := by
  apply (universalCoefficientEquiv.{w'} K k Z i).symm.injective
  rw [LinearEquiv.symm_apply_apply, universalCoefficientEquiv_symm_apply,
    extToHomology_coefficient_naturality, ← kroneckerSection_coefficient_naturality,
    ← map_add, ← universalCoefficientEquiv_symm_apply i, LinearEquiv.symm_apply_apply]

end CommRing

end UniversalCoefficient

end CochainComplex
