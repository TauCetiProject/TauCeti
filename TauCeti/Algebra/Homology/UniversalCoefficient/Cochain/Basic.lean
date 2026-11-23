/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.Restriction.Surjective
public import TauCeti.Algebra.Homology.LinearHomComplex.Single.Comparison
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
import TauCeti.Algebra.Homology.ModuleCat.Basic
import TauCeti.Algebra.Ring.NegOnePow
import TauCeti.LinearAlgebra.Exact

/-!
# Universal coefficient sequence for dual cochain complexes

For a `ℤ`-indexed cochain complex `K` in a `k`-linear abelian category `C` and an object `Y : C`,
`CochainComplex.linearHomComplexSingleIso`
(`TauCeti.Algebra.Homology.LinearHomComplex.Single.Comparison`) identifies the `k`-linear Hom
complex `Hom(K, Y[0])` (`CochainComplex.linearHomComplex`) with the linear Yoneda complex
`Hom(K⁻, Y)` of the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ` (the restriction of `K` along `n ↦ -n`).
Through the unsigned cohomology comparison `CochainComplex.linearHomComplexSingleHomologyIso` and
the universal coefficient sequence of chain complexes (`TauCeti.Algebra.Homology.Kronecker` and
`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`), this file establishes the universal
`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`), this file establishes the universal
coefficient sequence of the dual complex:

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`,

exact when the cocycles of `K` in degrees `1 - i` and `-i` split off and those in degree `1 - i`
are projective, for instance for a complex of free abelian groups.

## Main definitions and results

* `CochainComplex.linearHomComplexSingleKronecker`: the Kronecker map
  `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, characterized by
  `CochainComplex.homologyπ_linearHomComplexSingleKronecker`.
* `CochainComplex.linearHomComplexSingleKronecker_bijective` and
  `CochainComplex.linearHomComplexSingleKroneckerEquiv`: the Kronecker map is bijective for an
  injective object `Y`.
* `CochainComplex.linearHomComplexSingleKronecker_surjective`: it is surjective when the cocycles
  of `K` split off in degree `-i`.
* `CochainComplex.linearHomComplexSingleExtToHomology` (characterized by
  `CochainComplex.linearHomComplexSingleExtToHomology_extClass_comp_mk₀`),
  `CochainComplex.linearHomComplexSingleExtToHomology_injective`, and
  `CochainComplex.exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker`: the
  `Ext¹` term of the universal coefficient sequence and exactness at its first two places.
* Naturality of both maps (`CochainComplex.linearHomComplexSingleKronecker_naturality`,
  `CochainComplex.linearHomComplexSingleKronecker_coefficient_naturality`,
  `CochainComplex.linearHomComplexSingleExtToHomology_naturality`, and
  `CochainComplex.linearHomComplexSingleExtToHomology_coefficient_naturality`).
* `CochainComplex.linearHomComplexSingleKronecker_bijective_of_projective_homology`,
  `CochainComplex.linearHomComplexSingleKroneckerEquivOfProjectiveHomology`, and
  `CochainComplex.isZero_homology_linearHomComplex_of_projective_homology`: the Kronecker
  isomorphism and cohomology vanishing when `H¹⁻ⁱ(K)` is projective and the cycle inclusions split.
* `CochainComplex.linearHomComplexSingleKroneckerSection` (natural in `Y`) and
  `CochainComplex.linearHomComplexSingleUniversalCoefficientEquiv`: chosen splitting section and
  direct-product decomposition.

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

/-- Surjectivity of `ComplexShape.embeddingDownIntUpInt.f` stated with that projection so
`restrictionCyclesIsoOfSurjective` and `restrictionHomologyIsoOfSurjective` match without unfolding
the embedding. -/
private lemma surjective_embeddingDownIntUpInt_f :
    Function.Surjective ComplexShape.embeddingDownIntUpInt.f :=
  neg_surjective

private lemma projective_restriction_cycles_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [Projective (K.cycles (1 - i))] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
  K.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

private lemma isSplitMono_restriction_iCycles_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
  K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

private lemma isSplitMono_restriction_iCycles_self (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i) :=
  K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)

private lemma projective_restriction_homology_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [Projective (K.homology (1 - i))] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).homology (i - 1)) :=
  K.projective_restriction_homology_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

private lemma restriction_d_comp_retraction_iCycles_comp_homologyπ
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

attribute [local instance] projective_restriction_cycles_sub_one
  isSplitMono_restriction_iCycles_sub_one
  isSplitMono_restriction_iCycles_self
  projective_restriction_homology_sub_one

section Kronecker

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type*} [Ring k] [Linear k C]
  (K : CochainComplex C ℤ) (Y : C)

variable (k) in
/-- **The Kronecker map** `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` of a cochain complex `K`
indexed by `ℤ`, evaluating the cohomology classes of the Hom complex into `Y` placed in degree
zero on the cohomology classes of `K`: a cocycle of degree `i` is a morphism `K⁻ⁱ ⟶ Y` vanishing
on coboundaries, and its restriction to the cocycles of `K` descends to `H⁻ⁱ(K)`
(`CochainComplex.homologyπ_linearHomComplexSingleKronecker`). It is the Kronecker map
`TauCeti.ChainComplex.kronecker` of the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ`, transported along
`CochainComplex.linearHomComplexSingleHomologyIso`. -/
def linearHomComplexSingleKronecker (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i →ₗ[k] (K.homology (-i) ⟶ Y) :=
  (Linear.homCongr k (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
    (Iso.refl Y)).toLinearMap ∘ₗ
    TauCeti.ChainComplex.kronecker k _ Y i ∘ₗ
    (linearHomComplexSingleHomologyIso k K Y i).toLinearEquiv.toLinearMap

/-- **The Kronecker map on classes**: evaluating the class of a cocycle `φ` of `Hom(K, Y[0])` of
degree `i` on the class of a cocycle of `K` of degree `-i` is evaluating the morphism
`K⁻ⁱ ⟶ Y` underlying `φ` on that cocycle. -/
@[reassoc (attr := simp)]
lemma homologyπ_linearHomComplexSingleKronecker (i : ℤ)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i) :
    K.homologyπ (-i) ≫ linearHomComplexSingleKronecker k K Y i
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ) =
      K.iCycles (-i) ≫ Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
  let ψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i :=
    (i * (i + 1) / 2).negOnePow • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ
  have hψ : (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    dsimp only [ψ]
    rw [Units.smul_def, map_zsmul, moduleCat_iCycles_cyclesMap_apply, ← Units.smul_def,
      linearHomComplexSingleIso_hom_f_apply]
    exact Int.negOnePow_smul_negOnePow_smul _ _
  have hψ_rest : (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleEquiv (by simp : ComplexShape.embeddingDownIntUpInt.f i + i = 0)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) :=
    hψ
  simp only [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Iso.toLinearEquiv_apply,
    linearHomComplexSingleHomologyIso_hom_homologyπ K Y i φ ψ hψ,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
    homologyπ_restrictionHomologyIsoOfSurjective_inv_assoc,
    TauCeti.ChainComplex.kronecker_homologyπ]
  rw [hψ_rest, restrictionCyclesIsoOfSurjective_inv_iCycles_assoc,
    HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv]

/-- **The universal coefficient theorem for injective coefficients**: for an injective object
`Y`, the Kronecker map `Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` is bijective. -/
theorem linearHomComplexSingleKronecker_bijective [Injective Y] (i : ℤ) :
    Function.Bijective (linearHomComplexSingleKronecker k K Y i) := by
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp ((TauCeti.ChainComplex.kronecker_bijective i).comp
    (LinearEquiv.bijective _))

variable (k) in
/-- The Kronecker map as a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`, for an
injective object `Y`. -/
def linearHomComplexSingleKroneckerEquiv [Injective Y] (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective _ (linearHomComplexSingleKronecker_bijective K Y i)

/-- The equivalence `CochainComplex.linearHomComplexSingleKroneckerEquiv` is the Kronecker map. -/
@[simp]
lemma linearHomComplexSingleKroneckerEquiv_apply [Injective Y] (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKroneckerEquiv k K Y i x = linearHomComplexSingleKronecker k K Y i x :=
  (rfl)

/-- If the inclusion of the cocycles of `K` in degree `-i` is a split monomorphism, then every
morphism `H⁻ⁱ(K) ⟶ Y` is the evaluation of a cohomology class of `Hom(K, Y[0])` of degree `i`. -/
theorem linearHomComplexSingleKronecker_surjective (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    Function.Surjective (linearHomComplexSingleKronecker k K Y i) := by
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.surjective _).comp
    ((TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono i).comp (LinearEquiv.surjective _))

variable {K Y}

/-- **Naturality of `linearHomComplexSingleKronecker` in the complex**: pulling back along
`φ : K₁ ⟶ K₂` and evaluating on cohomology is pushing cohomology forward along `φ` and
evaluating. -/
theorem linearHomComplexSingleKronecker_naturality {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂)
    (i : ℤ) (x : (linearHomComplex k K₂ ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKronecker k K₁ Y i
        ((homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom x) =
      homologyMap φ (-i) ≫ linearHomComplexSingleKronecker k K₂ Y i x := by
  simp only [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Iso.toLinearEquiv_apply, Linear.homCongr_apply, Iso.refl_hom,
    Category.comp_id, ← ModuleCat.comp_apply,
    homologyMap_precomp_linearHomComplexSingleHomologyIso_hom k φ Y i]
  rw [ModuleCat.comp_apply, TauCeti.ChainComplex.kronecker_naturality,
    ← cancel_epi (K₁.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)).hom,
    Iso.hom_inv_id_assoc, ← Category.assoc,
    ← homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom
      ComplexShape.embeddingDownIntUpInt surjective_embeddingDownIntUpInt_f φ i (-i)
      (ComplexShape.embeddingDownIntUpInt_f i),
    Category.assoc, Iso.hom_inv_id_assoc]

/-- **Naturality of `linearHomComplexSingleKronecker` in the coefficient object**: postcomposing
with `g : Y₁ ⟶ Y₂` commutes with `linearHomComplexSingleKronecker`. -/
theorem linearHomComplexSingleKronecker_coefficient_naturality {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y₁)).homology i) :
    linearHomComplexSingleKronecker k K Y₂ i
        ((homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom x) =
      linearHomComplexSingleKronecker k K Y₁ i x ≫ g := by
  simp only [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Iso.toLinearEquiv_apply, Linear.homCongr_apply, Iso.refl_hom,
    Category.comp_id, ← ModuleCat.comp_apply,
    homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom k K g i]
  rw [ModuleCat.comp_apply, TauCeti.ChainComplex.kronecker_coefficient_naturality, Category.assoc]

/-- **The universal coefficient theorem with projective cohomology in degree `1 - i`**: when the
cycle inclusions in degrees `1 - i` and `-i` split, and `H¹⁻ⁱ(K)` is projective,
`linearHomComplexSingleKronecker` in degree `i` is bijective over any ring `k`. -/
theorem linearHomComplexSingleKronecker_bijective_of_projective_homology (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] [IsSplitMono (K.iCycles (-i))]
    [Projective (K.homology (1 - i))] :
    Function.Bijective (linearHomComplexSingleKronecker k K Y i) := by
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.bijective _).comp <|
    (TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_of_add_one_eq
      (k := k) (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y)
      (sub_add_cancel i 1)).comp
      (LinearEquiv.bijective _)

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
    hi.of_iso (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
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
      (restriction_d_comp_retraction_iCycles_comp_homologyπ K i)

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
    (restriction_d_comp_retraction_iCycles_comp_homologyπ K i) g
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
  dsimp only [linearHomComplexSingleKronecker, linearHomComplexSingleKroneckerSection,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Function.comp_apply]
  rw [Iso.toLinearEquiv_apply, ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
    ← cancel_epi (K.homologyπ (-i)), homologyπ_restrictionHomologyIsoOfSurjective_inv_assoc,
    TauCeti.ChainComplex.homologyπ_kronecker_homologyClassOfComp,
    restrictionCyclesIsoOfSurjective_inv_iCycles_assoc, Category.assoc, Category.assoc,
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
  {k : Type*} [CommRing k] [Linear k C] (K : CochainComplex C ℤ) (Y : C)

variable (k) in
/-- **The `Ext` term of the universal coefficient sequence** of the Hom complex into `Y[0]`: the
`k`-linear map `Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))`, defined when the cocycles of `K` in
degree `1 - i` are projective and split off `K¹⁻ⁱ`. It is the map
`TauCeti.ChainComplex.extToHomology` of the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ`, transported along
`CochainComplex.linearHomComplexSingleHomologyIso` and the identification of the homology of `K⁻` in
degree `i - 1` with `H¹⁻ⁱ(K)`. -/
def linearHomComplexSingleExtToHomology (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] :
    Ext.{w} (K.homology (1 - i)) Y 1 →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  (linearHomComplexSingleHomologyIso k K Y i).symm.toLinearEquiv.toLinearMap ∘ₗ
    TauCeti.ChainComplex.extToHomology k _ Y i (i - 1) ∘ₗ
    (TauCeti.extLinearEquivOfIso k
      (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).symm
      (Iso.refl Y) 1).toLinearMap

/-- **The characterization of `CochainComplex.linearHomComplexSingleExtToHomology`**: the class in
`Ext¹(H¹⁻ⁱ(K), Y)` of a morphism `β : B¹⁻ⁱ ⟶ Y` from the coboundaries of `K` goes to the class of
a cocycle `φ` of `Hom(K, Y[0])` of degree `i` whose underlying morphism `K⁻ⁱ ⟶ Y` is
`K⁻ⁱ ⟶ B¹⁻ⁱ ⟶ Y`. -/
lemma linearHomComplexSingleExtToHomology_extClass_comp_mk₀ (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (β : kernel (K.homologyπ (1 - i)) ⟶ Y)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hφ : Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) =
      K.toBoundaries (-i) (1 - i) ≫ β) :
    linearHomComplexSingleExtToHomology.{w} k K Y i
        ((TauCeti.kernelSequence_shortExact (K.homologyπ (1 - i))).extClass.comp (Ext.mk₀ β)
          (add_zero 1)) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ := by
  let b := kernel.map _ _
    (K.restrictionCyclesIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).hom
    (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).hom
    (K.homologyπ_restrictionHomologyIsoOfSurjective_hom ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp))
  -- state the kernel sequences with explicit terms, so that rewriting sees their objects
  have hK : (ShortComplex.mk (kernel.ι (K.homologyπ (1 - i))) _ (kernel.condition _)).ShortExact :=
    TauCeti.kernelSequence_shortExact _
  have hL : (ShortComplex.mk (kernel.ι ((K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ
      (i - 1))) _ (kernel.condition _)).ShortExact := TauCeti.kernelSequence_shortExact _
  -- the extension classes of the kernel sequences of `K⁻` and `K` correspond
  have hn := ShortComplex.ShortExact.extClass_naturality hL hK
    { τ₁ := b
      τ₂ := (K.restrictionCyclesIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).hom
      τ₃ := (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).hom
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (K.homologyπ_restrictionHomologyIsoOfSurjective_hom
        ComplexShape.embeddingDownIntUpInt surjective_embeddingDownIntUpInt_f (i - 1) (1 - i)
        (by simp)).symm }
  have he : TauCeti.extLinearEquivOfIso k
      (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).symm (Iso.refl Y) 1
      (hK.extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      hL.extClass.comp (Ext.mk₀ (b ≫ β)) (add_zero 1) := by
    rw [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
      ← Ext.comp_assoc_of_third_deg_zero, ← hn, Ext.comp_assoc_of_second_deg_zero,
      Ext.mk₀_comp_mk₀]
  let ψ : (_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).cycles i :=
    (i * (i + 1) / 2).negOnePow • cyclesMap (linearHomComplexSingleIso k K Y).hom i φ
  have hψ_cocycle : (_root_.ChainComplex.linearYonedaObj
        (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    dsimp only [ψ]
    rw [Units.smul_def, map_zsmul, moduleCat_iCycles_cyclesMap_apply, ← Units.smul_def,
      linearHomComplexSingleIso_hom_f_apply]
    exact Int.negOnePow_smul_negOnePow_smul _ _
  have hψ_bound : (_root_.ChainComplex.linearYonedaObj _ k Y).iCycles i ψ =
      (K.restriction ComplexShape.embeddingDownIntUpInt).toBoundaries i (i - 1) ≫ b ≫ β := by
    have hψ_rest : (_root_.ChainComplex.linearYonedaObj _ k Y).iCycles i ψ =
        Cochain.toSingleEquiv (by simp : ComplexShape.embeddingDownIntUpInt.f i + i = 0)
          ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) :=
      hψ_cocycle
    rw [hψ_rest]
    exact (cancel_epi (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).inv).1
      ((HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv _ _ _ _ (neg_add_cancel i) _
        _).trans (hφ.trans ((K.restrictionXIso_inv_comp_toBoundaries_kernelMap_assoc
          ComplexShape.embeddingDownIntUpInt surjective_embeddingDownIntUpInt_f i (i - 1) (-i)
          (1 - i) (ComplexShape.embeddingDownIntUpInt_f i) (by simp) β).symm)))
  refine Eq.trans (congrArg (linearHomComplexSingleHomologyIso k K Y i).symm.hom.hom
    ((congrArg (TauCeti.ChainComplex.extToHomology k _ Y i (i - 1)) he).trans
      (TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ i (i - 1) (b ≫ β) ψ hψ_bound))) ?_
  exact linearHomComplexSingleHomologyIso_inv_homologyπ K Y i φ ψ hψ_cocycle

/-- **Injectivity in the universal coefficient sequence** of the Hom complex into `Y[0]`: the map
`Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem linearHomComplexSingleExtToHomology_injective (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] :
    Function.Injective (linearHomComplexSingleExtToHomology.{w} k K Y i) := by
  rw [linearHomComplexSingleExtToHomology, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.injective _).comp
    ((TauCeti.ChainComplex.extToHomology_injective (sub_add_cancel i 1)).comp
      (LinearEquiv.injective _))

/-- **Exactness in the middle of the universal coefficient sequence** of the Hom complex into
`Y[0]`: a cohomology class of `Hom(K, Y[0])` of degree `i` evaluates to zero on `H⁻ⁱ(K)` exactly
when it comes from `Ext¹(H¹⁻ⁱ(K), Y)`. -/
theorem exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Function.Exact (linearHomComplexSingleExtToHomology.{w} k K Y i)
      (linearHomComplexSingleKronecker k K Y i) := by
  rw [linearHomComplexSingleExtToHomology, linearHomComplexSingleKronecker,
    ← Iso.toLinearEquiv_symm, LinearEquiv.postcomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact, LinearEquiv.precomp_exact_iff_exact]
  exact TauCeti.ChainComplex.exact_extToHomology_kronecker (sub_add_cancel i 1)

variable {K Y}

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
          (K₁.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
            surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).symm (Iso.refl Y) 1)
        ((Ext.mk₀ (homologyMap φ (1 - i))).comp e (zero_add 1)) =
      (Ext.mk₀ (homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt)
          (i - 1))).comp
        ((TauCeti.extLinearEquivOfIso k
          (K₂.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
            surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).symm
          (Iso.refl Y) 1) e) (zero_add 1) := by
    simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀,
      ← homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom
        ComplexShape.embeddingDownIntUpInt surjective_embeddingDownIntUpInt_f]
  simp only [linearHomComplexSingleExtToHomology, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Iso.toLinearEquiv_apply, Iso.symm_hom, ← ModuleCat.comp_apply,
    Iso.inv_hom_id, ModuleCat.id_apply]
  rw [Category.assoc, homologyMap_precomp_linearHomComplexSingleHomologyIso_hom k φ Y i,
    Iso.inv_hom_id_assoc, hext]
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
          (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
            surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).symm
          (Iso.refl Y₂) 1) (e.comp (Ext.mk₀ g) (add_zero 1)) =
      ((TauCeti.extLinearEquivOfIso k
          (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
            surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)).symm
          (Iso.refl Y₁) 1) e).comp (Ext.mk₀ g) (add_zero 1) := by
    simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    exact (Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)).symm
  simp only [linearHomComplexSingleExtToHomology, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Iso.toLinearEquiv_apply, Iso.symm_hom, ← ModuleCat.comp_apply,
    Iso.inv_hom_id, ModuleCat.id_apply]
  rw [Category.assoc, homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom k K g i,
    Iso.inv_hom_id_assoc, hext]
  exact TauCeti.ChainComplex.extToHomology_coefficient_naturality g i (i - 1) _

end Ext

end CochainComplex
