/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import TauCeti.Algebra.Homology.LinearHomComplex.Single
public import TauCeti.Algebra.Homology.LinearHomComplex.Single.Comparison
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
import TauCeti.Algebra.Homology.LinearHomComplex.Single.Basic
import TauCeti.LinearAlgebra.Exact

/-!
# Splitting and naturality of the universal coefficient sequence for dual cochain complexes

`TauCeti.Algebra.Homology.LinearHomComplex.Single` establishes the Kronecker map
`CochainComplex.linearHomComplexSingleKronecker` and the `Ext¹` inclusion
`CochainComplex.linearHomComplexSingleExtToHomology` in the universal coefficient sequence

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`

for a `ℤ`-indexed cochain complex `K` in a `k`-linear abelian category `C` and an object `Y : C`.
This file supplements that sequence with:

* naturality of both maps (`CochainComplex.linearHomComplexSingleKronecker_naturality`,
  `CochainComplex.linearHomComplexSingleKronecker_coefficient_naturality`,
  `CochainComplex.linearHomComplexSingleExtToHomology_naturality`, and
  `CochainComplex.linearHomComplexSingleExtToHomology_coefficient_naturality`),
* the Kronecker isomorphism and cohomology vanishing when `H¹⁻ⁱ(K)` is projective and the cycle
  inclusions split
  (`CochainComplex.linearHomComplexSingleKronecker_bijective_of_projective_homology`,
  `CochainComplex.linearHomComplexSingleKroneckerEquivOfProjectiveHomology`,
  `CochainComplex.isZero_homology_linearHomComplex_of_projective_homology`), and
* the splitting section (`CochainComplex.linearHomComplexSingleKroneckerSection`, natural in `Y`)
  and direct-product decomposition
  (`CochainComplex.linearHomComplexSingleUniversalCoefficientEquiv`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 3.6.5.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex CochainComplex.HomComplex Opposite Abelian TauCeti

universe w v u

namespace CochainComplex

section Helpers

variable {C : Type u} [Category.{v} C] [Abelian C]

private lemma projective_restrictionDownIntUpInt_cycles_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [Projective (K.cycles (1 - i))] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
  K.projective_restrictionDownIntUpInt_cycles (i - 1) (1 - i) (by omega)

private lemma isSplitMono_restrictionDownIntUpInt_iCycles_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
  K.isSplitMono_restrictionDownIntUpInt_iCycles (i - 1) (1 - i) (by omega)

private lemma isSplitMono_restrictionDownIntUpInt_iCycles_self (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i) :=
  K.isSplitMono_restrictionDownIntUpInt_iCycles i (-i) (add_neg_cancel i)

private lemma projective_restrictionDownIntUpInt_homology_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [Projective (K.homology (1 - i))] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).homology (i - 1)) :=
  Projective.of_iso (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm
    inferInstance

private lemma homologyMap_restrictionMap_restrictionDownIntUpIntHomologyIso_hom
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) (i j : ℤ) (h : i + j = 0) :
    homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i ≫
        (L.restrictionDownIntUpIntHomologyIso i j h).hom =
      (K.restrictionDownIntUpIntHomologyIso i j h).hom ≫ homologyMap φ j := by
  obtain rfl : j = -i := by omega
  have hcycles :
      cyclesMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i ≫
          (L.restrictionDownIntUpIntCyclesIso i (-i) h).hom =
        (K.restrictionDownIntUpIntCyclesIso i (-i) h).hom ≫ cyclesMap φ (-i) := by
    rw [← cancel_mono (L.iCycles (-i))]
    simp [restrictionXIso]
  rw [← cancel_epi ((K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ i)]
  simp only [homologyπ_naturality_assoc, homologyπ_restrictionDownIntUpIntHomologyIso_hom,
    homologyπ_restrictionDownIntUpIntHomologyIso_hom_assoc, homologyπ_naturality]
  rw [reassoc_of% hcycles]

private lemma linearHomComplexSingleKronecker_eq {k : Type*} [Ring k] [Linear k C]
    (K : CochainComplex C ℤ) (Y : C) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKronecker k K Y i x =
      (K.restrictionDownIntUpIntHomologyIso i (-i) (add_neg_cancel i)).inv ≫
        TauCeti.ChainComplex.kronecker k (K.restriction ComplexShape.embeddingDownIntUpInt) Y i
          ((linearHomComplexSingleHomologyIso k K Y i).hom.hom x) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ i x
  set X : _root_.ChainComplex C ℤ := K.restriction ComplexShape.embeddingDownIntUpInt
  set g : K.X (-i) ⟶ Y := Cochain.toSingleEquiv (neg_add_cancel i)
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
    dsimp only [X, f]
    rw [K.restriction_d_eq ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f (i + 1)) (ComplexShape.embeddingDownIntUpInt_f i),
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hdg, comp_zero]
  let ψ := TauCeti.ChainComplex.cocycleOfComp k Y f hf (𝟙 Y)
  have hψ : (X.linearYonedaObj k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    rw [TauCeti.ChainComplex.iCycles_cocycleOfComp, Category.comp_id]
    exact Category.id_comp _
  have hIso :
      (linearHomComplexSingleHomologyIso k K Y i).hom.hom
          ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
        (X.linearYonedaObj k Y).homologyπ i ψ :=
    linearHomComplexSingleHomologyIso_hom_homologyπ K Y i φ ψ hψ
  dsimp only [X] at hIso ⊢
  rw [← cancel_epi (K.homologyπ (-i)), homologyπ_linearHomComplexSingleKronecker,
    homologyπ_restrictionDownIntUpIntHomologyIso_inv_assoc, hIso,
    TauCeti.ChainComplex.kronecker_homologyπ, TauCeti.ChainComplex.iCycles_cocycleOfComp,
    Category.comp_id, restrictionDownIntUpIntCyclesIso_inv_iCycles_assoc, Iso.inv_hom_id_assoc]

private lemma restrictionDownIntUpInt_d_comp_retraction_iCycles_comp_homologyπ
    (K : CochainComplex C ℤ) (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    (K.restriction ComplexShape.embeddingDownIntUpInt).d ((ComplexShape.up ℤ).next i) i ≫
        (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) = 0 := by
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i + 1) by simp),
    K.restriction_d_eq ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f (i + 1)) (ComplexShape.embeddingDownIntUpInt_f i),
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    HomologicalComplex.d_comp_retraction_iCycles_comp_homologyπ, comp_zero]

end Helpers

section Kronecker

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type*} [Ring k] [Linear k C]
  {K : CochainComplex C ℤ} {Y : C}

attribute [local instance] projective_restrictionDownIntUpInt_cycles_sub_one
  isSplitMono_restrictionDownIntUpInt_iCycles_sub_one
  isSplitMono_restrictionDownIntUpInt_iCycles_self
  projective_restrictionDownIntUpInt_homology_sub_one

/-- **Naturality of `linearHomComplexSingleKronecker` in the complex**: pulling back along
`φ : K₁ ⟶ K₂` and evaluating on cohomology is pushing cohomology forward along `φ` and
evaluating. -/
theorem linearHomComplexSingleKronecker_naturality {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂)
    (i : ℤ) (x : (linearHomComplex k K₂ ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKronecker k K₁ Y i
        ((homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom x) =
      homologyMap φ (-i) ≫ linearHomComplexSingleKronecker k K₂ Y i x := by
  rw [linearHomComplexSingleKronecker_eq, linearHomComplexSingleKronecker_eq,
    ← ModuleCat.comp_apply, homologyMap_precomp_linearHomComplexSingleHomologyIso_hom k φ Y i,
    ModuleCat.comp_apply, TauCeti.ChainComplex.kronecker_naturality,
    ← cancel_epi (K₁.restrictionDownIntUpIntHomologyIso i (-i) (add_neg_cancel i)).hom,
    Iso.hom_inv_id_assoc, ← Category.assoc,
    ← homologyMap_restrictionMap_restrictionDownIntUpIntHomologyIso_hom φ i (-i)
      (add_neg_cancel i),
    Category.assoc, Iso.hom_inv_id_assoc]

/-- **Naturality of `linearHomComplexSingleKronecker` in the coefficient object**: postcomposing
with `g : Y₁ ⟶ Y₂` commutes with `linearHomComplexSingleKronecker`. -/
theorem linearHomComplexSingleKronecker_coefficient_naturality {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y₁)).homology i) :
    linearHomComplexSingleKronecker k K Y₂ i
        ((homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom x) =
      linearHomComplexSingleKronecker k K Y₁ i x ≫ g := by
  rw [linearHomComplexSingleKronecker_eq, linearHomComplexSingleKronecker_eq,
    ← ModuleCat.comp_apply, homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom k K g i,
    ModuleCat.comp_apply, TauCeti.ChainComplex.kronecker_coefficient_naturality, Category.assoc]

/-- **The universal coefficient theorem with projective cohomology in degree `1 - i`**: when the
cycle inclusions in degrees `1 - i` and `-i` split, and `H¹⁻ⁱ(K)` is projective,
`linearHomComplexSingleKronecker` in degree `i` is bijective over any ring `k`. -/
theorem linearHomComplexSingleKronecker_bijective_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    Function.Bijective (linearHomComplexSingleKronecker k K Y i) := by
  have hkr : linearHomComplexSingleKronecker k K Y i =
      (Linear.homCongr k (K.restrictionDownIntUpIntHomologyIso i (-i) (add_neg_cancel i))
        (Iso.refl Y)).toLinearMap.comp
        ((TauCeti.ChainComplex.kronecker k (K.restriction ComplexShape.embeddingDownIntUpInt) Y
          i).comp (linearHomComplexSingleHomologyIso k K Y i).hom.hom) := by
    ext x
    simp [linearHomComplexSingleKronecker_eq, Linear.homCongr_apply]
  rw [hkr, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp <|
    (TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_of_add_one_eq
      (k := k) (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y)
      (sub_add_cancel i 1)).comp
      (linearHomComplexSingleHomologyIso k K Y i).toLinearEquiv.bijective

variable (k K Y) in
/-- **The Kronecker equivalence with projective cohomology in degree `1 - i`**: when
`K.iCycles (1 - i)` and `K.iCycles (-i)` split and `K.homology (1 - i)` is projective,
`linearHomComplexSingleKronecker` is a `k`-linear equivalence
`Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def linearHomComplexSingleKroneckerEquivOfProjectiveHomology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (linearHomComplexSingleKronecker k K Y i)
    (linearHomComplexSingleKronecker_bijective_of_projective_homology i)

@[simp]
lemma linearHomComplexSingleKroneckerEquivOfProjectiveHomology_apply (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKroneckerEquivOfProjectiveHomology k K Y i x =
      linearHomComplexSingleKronecker k K Y i x :=
  (rfl)

/-- **Vanishing of dual cohomology**: when the cycle inclusions `K.iCycles (1 - i)` and
`K.iCycles (-i)` split, `H¹⁻ⁱ(K)` is projective, and `H⁻ⁱ(K)` vanishes, degree-`i` cohomology of
`linearHomComplex k K ((singleFunctor C 0).obj Y)` vanishes. -/
theorem isZero_homology_linearHomComplex_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] (hi : IsZero (K.homology (-i))) :
    IsZero ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) := by
  have hi' : IsZero ((K.restriction ComplexShape.embeddingDownIntUpInt).homology i) :=
    hi.of_iso (K.restrictionDownIntUpIntHomologyIso i (-i) (add_neg_cancel i))
  exact (TauCeti.ChainComplex.isZero_homology_linearYonedaObj_of_projective_homology_of_add_one_eq
    (k := k) (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y)
    (sub_add_cancel i 1) hi').of_iso
    (linearHomComplexSingleHomologyIso k K Y i)

variable (k K Y) in
/-- **Chosen splitting of `linearHomComplexSingleKronecker`**: given a retraction of
`K.iCycles (-i)`, the `k`-linear right inverse of `linearHomComplexSingleKronecker` sending
`g : H⁻ⁱ(K) ⟶ Y` to the cohomology class of the cocycle `K⁻ⁱ ⟶ Z⁻ⁱ(K) ⟶ H⁻ⁱ(K) ⟶ Y`. -/
def linearHomComplexSingleKroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    (K.homology (-i) ⟶ Y) →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  (linearHomComplexSingleHomologyIso k K Y i).inv.hom.comp <|
    TauCeti.ChainComplex.homologyClassOfComp k Y
      (X := K.restriction ComplexShape.embeddingDownIntUpInt)
      ((K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        retraction (K.iCycles (-i)) ≫ K.homologyπ (-i))
      (restrictionDownIntUpInt_d_comp_retraction_iCycles_comp_homologyπ K i)

/-- `linearHomComplexSingleKroneckerSection k K Y i g` is the cohomology class of any cocycle with
underlying morphism `retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) ≫ g`. -/
lemma linearHomComplexSingleKroneckerSection_apply (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hφ : Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) =
      retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) ≫ g) :
    linearHomComplexSingleKroneckerSection k K Y i g =
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i).hom φ := by
  let ψ := TauCeti.ChainComplex.cocycleOfComp k Y
    (X := K.restriction ComplexShape.embeddingDownIntUpInt)
    ((K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
      retraction (K.iCycles (-i)) ≫ K.homologyπ (-i))
    (restrictionDownIntUpInt_d_comp_retraction_iCycles_comp_homologyπ K i) g
  have hψ : (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    rw [TauCeti.ChainComplex.iCycles_cocycleOfComp, Category.assoc, Category.assoc, hφ]
    exact Category.id_comp _
  rw [linearHomComplexSingleKroneckerSection, LinearMap.comp_apply,
    TauCeti.ChainComplex.homologyClassOfComp_eq _ _ g ψ
      (TauCeti.ChainComplex.iCycles_cocycleOfComp _ _ g)]
  exact linearHomComplexSingleHomologyIso_inv_homologyπ K Y i φ ψ hψ

/-- `linearHomComplexSingleKroneckerSection` is a right inverse of
`linearHomComplexSingleKronecker`. -/
@[simp]
lemma linearHomComplexSingleKronecker_linearHomComplexSingleKroneckerSection (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y) :
    linearHomComplexSingleKronecker k K Y i
        (linearHomComplexSingleKroneckerSection k K Y i g) = g := by
  rw [linearHomComplexSingleKronecker_eq, linearHomComplexSingleKroneckerSection,
    LinearMap.comp_apply, ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    ← cancel_epi (K.homologyπ (-i)), homologyπ_restrictionDownIntUpIntHomologyIso_inv_assoc,
    TauCeti.ChainComplex.homologyπ_kronecker_homologyClassOfComp,
    restrictionDownIntUpIntCyclesIso_inv_iCycles_assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, IsSplitMono.id_assoc]

/-- **Coefficient naturality of `linearHomComplexSingleKroneckerSection`**:
`linearHomComplexSingleKroneckerSection` commutes with postcomposition by any morphism
`h : Y₁ ⟶ Y₂`. -/
theorem linearHomComplexSingleKroneckerSection_coefficient_naturality {Y₁ Y₂ : C} (h : Y₁ ⟶ Y₂)
    (i : ℤ) [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y₁) :
    (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map h)) i).hom
        (linearHomComplexSingleKroneckerSection k K Y₁ i g) =
      linearHomComplexSingleKroneckerSection k K Y₂ i (g ≫ h) := by
  apply (linearHomComplexSingleHomologyIso k K Y₂ i).toLinearEquiv.injective
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, ← ModuleCat.comp_apply,
    homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom k K h i, ModuleCat.comp_apply]
  simp only [linearHomComplexSingleKroneckerSection, LinearMap.comp_apply,
    ← ModuleCat.comp_apply (linearHomComplexSingleHomologyIso k K _ i).inv,
    Iso.inv_hom_id, ModuleCat.id_apply]
  exact TauCeti.ChainComplex.homologyClassOfComp_coefficient_naturality _ _ g h

end Kronecker

section Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {k : Type*} [CommRing k] [Linear k C] {K : CochainComplex C ℤ} {Y : C}

attribute [local instance] projective_restrictionDownIntUpInt_cycles_sub_one
  isSplitMono_restrictionDownIntUpInt_iCycles_sub_one
  isSplitMono_restrictionDownIntUpInt_iCycles_self

private lemma linearHomComplexSingleHomologyIso_hom_linearHomComplexSingleExtToHomology
    (i : ℤ) [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w} (K.homology (1 - i)) Y 1) :
    (linearHomComplexSingleHomologyIso k K Y i).hom.hom
        (linearHomComplexSingleExtToHomology.{w} k K Y i e) =
      TauCeti.ChainComplex.extToHomology.{w} k
        (K.restriction ComplexShape.embeddingDownIntUpInt) Y i (i - 1)
        ((TauCeti.extLinearEquivOfIso k
          (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm
          (Iso.refl Y) 1) e) := by
  set X : _root_.ChainComplex C ℤ := K.restriction ComplexShape.embeddingDownIntUpInt
  have hK : (ShortComplex.mk (kernel.ι (K.homologyπ (1 - i))) (K.homologyπ (1 - i))
      (kernel.condition _)).ShortExact := TauCeti.kernelSequence_shortExact _
  have hL : (ShortComplex.mk (kernel.ι (X.homologyπ (i - 1))) (X.homologyπ (i - 1))
      (kernel.condition _)).ShortExact := TauCeti.kernelSequence_shortExact _
  obtain ⟨β, rfl⟩ := TauCeti.homBoundary_surjective k hK Y e
  rw [TauCeti.homBoundary_apply]
  let b : kernel (X.homologyπ (i - 1)) ⟶ kernel (K.homologyπ (1 - i)) :=
    kernel.map _ _ (K.restrictionDownIntUpIntCyclesIso (i - 1) (1 - i) (by omega)).hom
      (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).hom
      (homologyπ_restrictionDownIntUpIntHomologyIso_hom ..)
  have hb : (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).inv ≫
      X.toBoundaries i (i - 1) ≫ b = K.toBoundaries (-i) (1 - i) := by
    rw [← cancel_mono (kernel.ι _), ← cancel_mono (K.iCycles _)]
    dsimp only [b, X]
    simp only [Category.assoc, kernel.lift_ι, toBoundaries_ι, toCycles_i_assoc,
      restrictionDownIntUpIntCyclesIso_hom_iCycles, toBoundaries_ι_assoc, toCycles_i]
    rw [K.restriction_d_eq ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f i)
      (show ComplexShape.embeddingDownIntUpInt.f (i - 1) = 1 - i by simp),
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hbb := congrArg (· ≫ β) hb
  rw [Category.assoc, Category.assoc] at hbb
  let ψ := TauCeti.ChainComplex.cocycleOfComp k Y (X := X) (X.toBoundaries i (i - 1))
    (X.d_toBoundaries _ i (i - 1)) (b ≫ β)
  let φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i :=
    (i * (i + 1) / 2).negOnePow • cyclesMap (linearHomComplexSingleIso k K Y).inv i ψ
  have hφ_iCycles :
      Cochain.toSingleEquiv (neg_add_cancel i)
          ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) =
        K.toBoundaries (-i) (1 - i) ≫ β := by
    have hi : (linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ =
        (i * (i + 1) / 2).negOnePow •
          (linearHomComplexSingleIso k K Y).inv.f i ((X.linearYonedaObj k Y).iCycles i ψ) := by
      dsimp only [X]
      simp only [φ, Units.smul_def, map_zsmul, moduleCat_iCycles_cyclesMap_apply]
    have hlin :
        Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
            ((linearHomComplexSingleIso k K Y).inv.f i
              ((X.linearYonedaObj k Y).iCycles i ψ)) =
          (i * (i + 1) / 2).negOnePow •
            ((K.restrictionXIso ComplexShape.embeddingDownIntUpInt
              (ComplexShape.embeddingDownIntUpInt_f i)).inv ≫
              (X.linearYonedaObj k Y).iCycles i ψ) := by
      have h1 := linearHomComplexSingleIso_inv_f_apply (k := k) K Y i
        ((X.linearYonedaObj k Y).iCycles i ψ)
      refine (congrArg (Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)) h1).trans ?_
      refine (_root_.map_zsmul
        (Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)) _ _).trans ?_
      congr 1
      exact (Cochain.toSingleEquiv_toSingleMk _ _).trans (Category.id_comp _).symm
    rw [hi, Units.smul_def]
    refine (_root_.map_zsmul
      (Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)) _ _).trans ?_
    rw [← Units.smul_def, hlin, Int.negOnePow_smul_negOnePow_smul,
      TauCeti.ChainComplex.iCycles_cocycleOfComp]
    exact hbb
  have hψ : (X.linearYonedaObj k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    rw [TauCeti.ChainComplex.iCycles_cocycleOfComp]
    have hc : Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) =
        K.toBoundaries (-i) (1 - i) ≫ β := hφ_iCycles
    rw [hc, ← hbb]
    exact (Category.id_comp _).symm
  have hExt : linearHomComplexSingleExtToHomology.{w} k K Y i
        (hK.extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ :=
    linearHomComplexSingleExtToHomology_extClass_comp_mk₀ K Y i β φ hφ_iCycles
  rw [hExt, linearHomComplexSingleHomologyIso_hom_homologyπ K Y i φ ψ hψ]
  have hn := ShortComplex.ShortExact.extClass_naturality hL hK
    { τ₁ := b
      τ₂ := (K.restrictionDownIntUpIntCyclesIso (i - 1) (1 - i) (by omega)).hom
      τ₃ := (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).hom
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (homologyπ_restrictionDownIntUpIntHomologyIso_hom ..).symm }
  have he : TauCeti.extLinearEquivOfIso k
      (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm (Iso.refl Y) 1
      (hK.extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      hL.extClass.comp (Ext.mk₀ (b ≫ β)) (add_zero 1) := by
    rw [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
      ← Ext.comp_assoc_of_third_deg_zero, ← hn, Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀]
  rw [he]
  exact (TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ i (i - 1) (b ≫ β) ψ
    (TauCeti.ChainComplex.iCycles_cocycleOfComp _ _ _)).symm

variable (k K Y) in
/-- **Split direct-product decomposition of the universal coefficient sequence** for
`linearHomComplex`: when `K.cycles (1 - i)` is projective and `K.iCycles (1 - i)` and
`K.iCycles (-i)` split, cohomology in degree `i` decomposes `k`-linearly as
`Ext¹(H¹⁻ⁱ(K), Y) × (H⁻ⁱ(K) ⟶ Y)`. -/
def linearHomComplexSingleUniversalCoefficientEquiv (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k]
      Ext.{w} (K.homology (1 - i)) Y 1 × (K.homology (-i) ⟶ Y) :=
  ((exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker.{w}
      (k := k) K Y i).splitSurjectiveEquiv
    (linearHomComplexSingleExtToHomology_injective.{w} (k := k) K Y i)
    ⟨linearHomComplexSingleKroneckerSection k K Y i,
      LinearMap.ext (linearHomComplexSingleKronecker_linearHomComplexSingleKroneckerSection
        i)⟩).val

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_symm_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (e : Ext.{w} (K.homology (1 - i)) Y 1) (g : K.homology (-i) ⟶ Y) :
    (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i).symm (e, g) =
      linearHomComplexSingleExtToHomology.{w} k K Y i e +
        linearHomComplexSingleKroneckerSection k K Y i g :=
  Function.Exact.splitSurjectiveEquiv_symm_apply _ _ _ e g

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_apply_snd (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i x).2 =
      linearHomComplexSingleKronecker k K Y i x :=
  Function.Exact.splitSurjectiveEquiv_apply_snd _ _ _ x

/-- **Naturality of `linearHomComplexSingleExtToHomology` in the complex**: pulling an extension
back along `homologyMap φ (1 - i)` and including it into cohomology agrees with including first and
pulling back along `linearHomComplexPrecomp k φ _`. -/
theorem linearHomComplexSingleExtToHomology_naturality {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂)
    (i : ℤ) [Projective (K₁.cycles (1 - i))] [IsSplitMono (K₁.iCycles (1 - i))]
    [Projective (K₂.cycles (1 - i))] [IsSplitMono (K₂.iCycles (1 - i))]
    (e : Ext.{w} (K₂.homology (1 - i)) Y 1) :
    linearHomComplexSingleExtToHomology.{w} k K₁ Y i
        ((Ext.mk₀ (homologyMap φ (1 - i))).comp e (zero_add 1)) =
      (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom
        (linearHomComplexSingleExtToHomology.{w} k K₂ Y i e) := by
  apply (linearHomComplexSingleHomologyIso k K₁ Y i).toLinearEquiv.injective
  have hext :
      (TauCeti.extLinearEquivOfIso k
          (K₁.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm (Iso.refl Y) 1)
        ((Ext.mk₀ (homologyMap φ (1 - i))).comp e (zero_add 1)) =
      (Ext.mk₀ (homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt)
          (i - 1))).comp
        ((TauCeti.extLinearEquivOfIso k
          (K₂.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm
          (Iso.refl Y) 1) e) (zero_add 1) := by
    simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀,
      ← homologyMap_restrictionMap_restrictionDownIntUpIntHomologyIso_hom]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, ← ModuleCat.comp_apply,
    homologyMap_precomp_linearHomComplexSingleHomologyIso_hom k φ Y i, ModuleCat.comp_apply,
    linearHomComplexSingleHomologyIso_hom_linearHomComplexSingleExtToHomology,
    linearHomComplexSingleHomologyIso_hom_linearHomComplexSingleExtToHomology, hext]
  exact TauCeti.ChainComplex.extToHomology_naturality
    (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i (i - 1) _

/-- **Naturality of `linearHomComplexSingleExtToHomology` in the coefficient object**: pushing an
extension forward along `g : Y₁ ⟶ Y₂` and including it into cohomology agrees with including first
and applying `linearHomComplexPostcomp`. -/
theorem linearHomComplexSingleExtToHomology_coefficient_naturality {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
    (i : ℤ) [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w} (K.homology (1 - i)) Y₁ 1) :
    linearHomComplexSingleExtToHomology.{w} k K Y₂ i (e.comp (Ext.mk₀ g) (add_zero 1)) =
      (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom
        (linearHomComplexSingleExtToHomology.{w} k K Y₁ i e) := by
  apply (linearHomComplexSingleHomologyIso k K Y₂ i).toLinearEquiv.injective
  have hext :
      (TauCeti.extLinearEquivOfIso k
          (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm
          (Iso.refl Y₂) 1) (e.comp (Ext.mk₀ g) (add_zero 1)) =
      ((TauCeti.extLinearEquivOfIso k
          (K.restrictionDownIntUpIntHomologyIso (i - 1) (1 - i) (by omega)).symm
          (Iso.refl Y₁) 1) e).comp (Ext.mk₀ g) (add_zero 1) := by
    simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    exact (Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)).symm
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, ← ModuleCat.comp_apply,
    homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom k K g i, ModuleCat.comp_apply,
    linearHomComplexSingleHomologyIso_hom_linearHomComplexSingleExtToHomology,
    linearHomComplexSingleHomologyIso_hom_linearHomComplexSingleExtToHomology, hext]
  exact TauCeti.ChainComplex.extToHomology_coefficient_naturality g i (i - 1) _

end Ext

end CochainComplex
