/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.Restriction.Surjective
public import TauCeti.Algebra.Homology.LinearHomComplex.Single.Comparison
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality

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

private abbrev restrictionDownHomologyIso (K : CochainComplex C ℤ) (i : ℤ) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homology i ≅ K.homology (-i) :=
  K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)

private abbrev restrictionDownCyclesIso (K : CochainComplex C ℤ) (i : ℤ) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).cycles i ≅ K.cycles (-i) :=
  K.restrictionCyclesIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)

@[reassoc]
private lemma homologyπ_restrictionDownHomologyIso_inv (K : CochainComplex C ℤ) (i : ℤ) :
    K.homologyπ (-i) ≫ (restrictionDownHomologyIso K i).inv =
      (restrictionDownCyclesIso K i).inv ≫
        (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ i :=
  K.homologyπ_restrictionHomologyIsoOfSurjective_inv ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)

private abbrev restrictionDownHomologySubOneIso (K : CochainComplex C ℤ) (i : ℤ) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homology (i - 1) ≅ K.homology (1 - i) :=
  K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

private abbrev restrictionDownCyclesSubOneIso (K : CochainComplex C ℤ) (i : ℤ) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1) ≅ K.cycles (1 - i) :=
  K.restrictionCyclesIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

private lemma homologyπ_restrictionDownHomologySubOneIso_hom (K : CochainComplex C ℤ) (i : ℤ) :
    (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ (i - 1) ≫
        (restrictionDownHomologySubOneIso K i).hom =
      (restrictionDownCyclesSubOneIso K i).hom ≫ K.homologyπ (1 - i) :=
  K.homologyπ_restrictionHomologyIsoOfSurjective_hom ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

private abbrev restrictionDownICyclesRetraction (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    (K.restriction ComplexShape.embeddingDownIntUpInt).X i ⟶
      (K.restriction ComplexShape.embeddingDownIntUpInt).cycles i :=
  K.restrictionICyclesRetractionOfSurjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f i (-i)
    (ComplexShape.embeddingDownIntUpInt_f i) (retraction (K.iCycles (-i)))

private lemma iCycles_restrictionDownICyclesRetraction (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    (K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i ≫
        restrictionDownICyclesRetraction K i = 𝟙 _ :=
  K.iCycles_restrictionICyclesRetractionOfSurjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f i (-i)
    (ComplexShape.embeddingDownIntUpInt_f i) (retraction (K.iCycles (-i))) (IsSplitMono.id _)

/-- Transport a naturality square across a three-factor `LinearMap` composition. -/
private lemma linearMap_comp_three_naturality {R : Type*} [Semiring R]
    {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : Type*}
    [AddCommMonoid A₁] [AddCommMonoid A₂] [AddCommMonoid B₁] [AddCommMonoid B₂]
    [AddCommMonoid C₁] [AddCommMonoid C₂] [AddCommMonoid D₁] [AddCommMonoid D₂]
    [Module R A₁] [Module R A₂] [Module R B₁] [Module R B₂]
    [Module R C₁] [Module R C₂] [Module R D₁] [Module R D₂]
    {a₁ : A₁ →ₗ[R] B₁} {m₁ : B₁ →ₗ[R] C₁} {c₁ : C₁ →ₗ[R] D₁}
    {a₂ : A₂ →ₗ[R] B₂} {m₂ : B₂ →ₗ[R] C₂} {c₂ : C₂ →ₗ[R] D₂}
    {v₀ : A₁ →ₗ[R] A₂} {v₁ : B₁ →ₗ[R] B₂} {v₂ : C₁ →ₗ[R] C₂} {v₃ : D₁ →ₗ[R] D₂}
    (ha : v₁ ∘ₗ a₁ = a₂ ∘ₗ v₀) (hm : v₂ ∘ₗ m₁ = m₂ ∘ₗ v₁) (hc : v₃ ∘ₗ c₁ = c₂ ∘ₗ v₂) :
    v₃ ∘ₗ (c₁ ∘ₗ m₁ ∘ₗ a₁) = (c₂ ∘ₗ m₂ ∘ₗ a₂) ∘ₗ v₀ := by
  calc
    v₃ ∘ₗ (c₁ ∘ₗ m₁ ∘ₗ a₁)
      = (v₃ ∘ₗ c₁) ∘ₗ m₁ ∘ₗ a₁ := by simp only [LinearMap.comp_assoc]
    _ = c₂ ∘ₗ (v₂ ∘ₗ m₁) ∘ₗ a₁ := by rw [hc]; simp only [LinearMap.comp_assoc]
    _ = c₂ ∘ₗ m₂ ∘ₗ (v₁ ∘ₗ a₁) := by rw [hm]; simp only [LinearMap.comp_assoc]
    _ = (c₂ ∘ₗ m₂ ∘ₗ a₂) ∘ₗ v₀ := by rw [ha]; simp only [LinearMap.comp_assoc]

private lemma projective_restriction_cycles_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [Projective (K.cycles (1 - i))] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).cycles (i - 1)) :=
  K.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

private lemma isSplitMono_restriction_iCycles_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (1 - i))] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles (i - 1)) :=
  K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

private lemma isSplitMono_restriction_iCycles_self (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    IsSplitMono ((K.restriction ComplexShape.embeddingDownIntUpInt).iCycles i) :=
  K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)

private lemma projective_restriction_homology_sub_one (K : CochainComplex C ℤ) (i : ℤ)
    [Projective (K.homology (1 - i))] :
    Projective ((K.restriction ComplexShape.embeddingDownIntUpInt).homology (i - 1)) :=
  K.projective_restriction_homology_of_surjective ComplexShape.embeddingDownIntUpInt
    ComplexShape.surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) (by simp)

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
  (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y)).toLinearMap ∘ₗ
    TauCeti.ChainComplex.kronecker k _ Y i ∘ₗ
    (linearHomComplexSingleHomologyIso k K Y i).toLinearEquiv.toLinearMap

private lemma linearHomComplexSingleKronecker_eq (i : ℤ) :
    linearHomComplexSingleKronecker k K Y i =
      (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y)).toLinearMap ∘ₗ
        TauCeti.ChainComplex.kronecker k _ Y i ∘ₗ
        (linearHomComplexSingleHomologyIso k K Y i).hom.hom := by
  rw [linearHomComplexSingleKronecker, CategoryTheory.Iso.toLinearMap_toLinearEquiv]

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
  rw [linearHomComplexSingleKronecker, LinearMap.coe_comp, LinearMap.coe_comp,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    Function.comp_apply, Function.comp_apply, Iso.toLinearEquiv_apply, ← ModuleCat.comp_apply,
    homologyπ_linearHomComplexSingleHomologyIso_hom, ModuleCat.comp_apply,
    Linear.homCongr_apply, Iso.refl_hom, Category.comp_id,
    homologyπ_restrictionDownHomologyIso_inv_assoc,
    TauCeti.ChainComplex.kronecker_homologyπ]
  refine (congrArg (_ ≫ _ ≫ ·)
    (iCycles_linearHomComplexSingleCyclesIso_hom_apply K Y i φ)).trans ?_
  rw [restrictionCyclesIsoOfSurjective_inv_iCycles_assoc, Iso.inv_hom_id_assoc]

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

private lemma linearHomComplexSingleKronecker_naturality_hom {K₁ K₂ : CochainComplex C ℤ}
    (φ : K₁ ⟶ K₂) (i : ℤ) :
    homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i ≫
        ModuleCat.ofHom (linearHomComplexSingleKronecker k K₁ Y i) =
      ModuleCat.ofHom (linearHomComplexSingleKronecker k K₂ Y i) ≫
        ModuleCat.ofHom (Linear.leftComp k Y (homologyMap φ (-i))) := by
  refine ModuleCat.hom_ext ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, linearHomComplexSingleKronecker_eq]
  -- Transport naturality along homology comparison, chain Kronecker, and homCongr.
  have h1 := congrArg ModuleCat.Hom.hom
    (homologyMap_precomp_linearHomComplexSingleHomologyIso_hom (k := k) φ Y i).symm
  simp only [ModuleCat.hom_comp] at h1
  have h2 : Linear.leftComp k Y (homologyMap
        (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i) ∘ₗ
      TauCeti.ChainComplex.kronecker k _ Y i =
      TauCeti.ChainComplex.kronecker k _ Y i ∘ₗ
        (homologyMap
          (K := _root_.ChainComplex.linearYonedaObj
            (K₂.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          (L := _root_.ChainComplex.linearYonedaObj
            (K₁.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
            (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op)
          i).hom :=
    LinearMap.ext fun x ↦ (TauCeti.ChainComplex.kronecker_naturality _ i x).symm
  have h3 :
      Linear.leftComp k Y (homologyMap φ (-i)) ∘ₗ
        (Linear.homCongr k (restrictionDownHomologyIso K₂ i) (Iso.refl Y)).toLinearMap =
      (Linear.homCongr k (restrictionDownHomologyIso K₁ i) (Iso.refl Y)).toLinearMap ∘ₗ
        Linear.leftComp k Y (homologyMap
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i) := by
    ext g
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Linear.leftComp_apply, Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
    have hinv : homologyMap φ (-i) ≫ (K₂.restrictionDownHomologyIso i).inv =
        (K₁.restrictionDownHomologyIso i).inv ≫
          homologyMap (HomologicalComplex.restrictionMap φ
            ComplexShape.embeddingDownIntUpInt) i := by
      dsimp only [restrictionDownHomologyIso]
      rw [Iso.comp_inv_eq, Category.assoc,
        homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom,
        Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hinv, Category.assoc]
  exact (linearMap_comp_three_naturality h1 h2 h3).symm

/-- **Naturality of `linearHomComplexSingleKronecker` in the complex**: pulling back along
`φ : K₁ ⟶ K₂` and evaluating on cohomology is pushing cohomology forward along `φ` and
evaluating. -/
theorem linearHomComplexSingleKronecker_naturality {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂)
    (i : ℤ) (x : (linearHomComplex k K₂ ((singleFunctor C 0).obj Y)).homology i) :
    linearHomComplexSingleKronecker k K₁ Y i
        ((homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom x) =
      homologyMap φ (-i) ≫ linearHomComplexSingleKronecker k K₂ Y i x :=
  ConcreteCategory.congr_hom (linearHomComplexSingleKronecker_naturality_hom φ i) x

private lemma linearHomComplexSingleKronecker_coefficient_naturality_hom {Y₁ Y₂ : C}
    (g : Y₁ ⟶ Y₂) (i : ℤ) :
    homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i ≫
        ModuleCat.ofHom (linearHomComplexSingleKronecker k K Y₂ i) =
      ModuleCat.ofHom (linearHomComplexSingleKronecker k K Y₁ i) ≫
        ModuleCat.ofHom (Linear.rightComp k (K.homology (-i)) g) := by
  refine ModuleCat.hom_ext ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, linearHomComplexSingleKronecker_eq]
  -- Transport naturality along homology comparison, chain Kronecker, and homCongr.
  have h1 := congrArg ModuleCat.Hom.hom
    (homologyMap_postcomp_linearHomComplexSingleHomologyIso_hom (k := k) K g i).symm
  simp only [ModuleCat.hom_comp] at h1
  have h2 : Linear.rightComp k _ g ∘ₗ TauCeti.ChainComplex.kronecker k _ Y₁ i =
      TauCeti.ChainComplex.kronecker k _ Y₂ i ∘ₗ
        (homologyMap (_root_.ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) g) i).hom :=
    LinearMap.ext fun x ↦ (TauCeti.ChainComplex.kronecker_coefficient_naturality g i x).symm
  have h3 :
      Linear.rightComp k (K.homology (-i)) g ∘ₗ
        (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y₁)).toLinearMap =
      (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y₂)).toLinearMap ∘ₗ
        Linear.rightComp k _ g := by
    ext f
    simp [Linear.homCongr_apply, Linear.rightComp_apply, Category.assoc]
  exact (linearMap_comp_three_naturality h1 h2 h3).symm

/-- **Naturality of `linearHomComplexSingleKronecker` in the coefficient object**: postcomposing
with `g : Y₁ ⟶ Y₂` commutes with `linearHomComplexSingleKronecker`. -/
theorem linearHomComplexSingleKronecker_coefficient_naturality {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y₁)).homology i) :
    linearHomComplexSingleKronecker k K Y₂ i
        ((homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom x) =
      linearHomComplexSingleKronecker k K Y₁ i x ≫ g :=
  ConcreteCategory.congr_hom (linearHomComplexSingleKronecker_coefficient_naturality_hom g i) x

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
    hi.of_iso (restrictionDownHomologyIso K i)
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
  (linearHomComplexSingleHomologyIso k K Y i).symm.toLinearEquiv.toLinearMap ∘ₗ
    TauCeti.ChainComplex.kroneckerSectionOfRetraction k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i
      (restrictionDownICyclesRetraction K i)
      (iCycles_restrictionDownICyclesRetraction K i) ∘ₗ
    (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y)).symm.toLinearMap

private lemma linearHomComplexSingleKroneckerSection_eq (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    linearHomComplexSingleKroneckerSection k K Y i =
      (linearHomComplexSingleHomologyIso k K Y i).inv.hom ∘ₗ
        TauCeti.ChainComplex.kroneckerSectionOfRetraction k
          (K.restriction ComplexShape.embeddingDownIntUpInt) Y i
          (restrictionDownICyclesRetraction K i)
          (iCycles_restrictionDownICyclesRetraction K i) ∘ₗ
        (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y)).symm.toLinearMap := by
  rw [linearHomComplexSingleKroneckerSection, CategoryTheory.Iso.toLinearMap_toLinearEquiv,
    Iso.symm_hom]

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
  rw [Cochain.toSingleLinearEquiv_apply, AddEquiv.toFun_eq_coe] at hφ
  let g' : (K.restriction ComplexShape.embeddingDownIntUpInt).homology i ⟶ Y :=
    (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y)).symm g
  let ψ := TauCeti.ChainComplex.cocycleOfComp k Y
    (X := K.restriction ComplexShape.embeddingDownIntUpInt)
    (restrictionDownICyclesRetraction K i ≫
      (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ i)
    (by
      rw [← HomologicalComplex.toCycles_i_assoc,
        reassoc_of% (iCycles_restrictionDownICyclesRetraction K i),
        HomologicalComplex.toCycles_comp_homologyπ])
    g'
  have hψ : ((_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i).hom ψ =
      (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        Cochain.toSingleEquiv (neg_add_cancel i)
          (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    have hψ0 : (restrictionDownICyclesRetraction K i ≫
          (K.restriction ComplexShape.embeddingDownIntUpInt).homologyπ i) ≫ g' =
        (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
          Cochain.toSingleEquiv (neg_add_cancel i)
            (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
      dsimp only [g']
      rw [Linear.homCongr_symm_apply, Iso.refl_inv, Category.comp_id, ← Category.assoc,
        HomologicalComplex.restrictionICyclesRetractionOfSurjective_comp_homologyπ
          ComplexShape.embeddingDownIntUpInt ComplexShape.surjective_embeddingDownIntUpInt_f]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hφ]
    exact (TauCeti.ChainComplex.iCycles_cocycleOfComp _ _ g').trans hψ0
  exact (congrArg (linearHomComplexSingleHomologyIso k K Y i).inv.hom
    (TauCeti.ChainComplex.kroneckerSectionOfRetraction_apply i
      (restrictionDownICyclesRetraction K i) (iCycles_restrictionDownICyclesRetraction K i) g' ψ
      ((TauCeti.ChainComplex.iCycles_cocycleOfComp _ _ g').trans (Category.assoc ..)))).trans
    (linearHomComplexSingleHomologyIso_inv_homologyπ K Y i φ ψ hψ)

/-- `linearHomComplexSingleKroneckerSection` is a right inverse of
`linearHomComplexSingleKronecker`. -/
@[simp]
lemma linearHomComplexSingleKronecker_linearHomComplexSingleKroneckerSection (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y) :
    linearHomComplexSingleKronecker k K Y i
        (linearHomComplexSingleKroneckerSection k K Y i g) = g := by
  simp only [linearHomComplexSingleKronecker, linearHomComplexSingleKroneckerSection,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Iso.toLinearEquiv_apply, Iso.symm_hom,
    ← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply,
    TauCeti.ChainComplex.kronecker_kroneckerSectionOfRetraction, LinearEquiv.apply_symm_apply]

private lemma linearHomComplexSingleKroneckerSection_coefficient_naturality_hom {Y₁ Y₂ : C}
    (h : Y₁ ⟶ Y₂) (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    ModuleCat.ofHom (linearHomComplexSingleKroneckerSection k K Y₁ i) ≫
        homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map h)) i =
      ModuleCat.ofHom (Linear.rightComp k (K.homology (-i)) h) ≫
        ModuleCat.ofHom (linearHomComplexSingleKroneckerSection k K Y₂ i) := by
  refine ModuleCat.hom_ext ?_
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, linearHomComplexSingleKroneckerSection_eq]
  -- Transport naturality along homCongr.symm, chain kroneckerSection, and homology comparison.
  have h1 :
      Linear.rightComp k ((K.restriction ComplexShape.embeddingDownIntUpInt).homology i) h ∘ₗ
        (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y₁)).symm.toLinearMap =
      (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y₂)).symm.toLinearMap ∘ₗ
        Linear.rightComp k (K.homology (-i)) h := by
    ext g
    simp [Linear.homCongr_symm_apply, Linear.rightComp_apply, Category.assoc]
  have h2 :
      (homologyMap (_root_.ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) h) i).hom ∘ₗ
        TauCeti.ChainComplex.kroneckerSectionOfRetraction k
          (K.restriction ComplexShape.embeddingDownIntUpInt) Y₁ i
          (restrictionDownICyclesRetraction K i)
          (iCycles_restrictionDownICyclesRetraction K i) =
      TauCeti.ChainComplex.kroneckerSectionOfRetraction k
          (K.restriction ComplexShape.embeddingDownIntUpInt) Y₂ i
          (restrictionDownICyclesRetraction K i)
          (iCycles_restrictionDownICyclesRetraction K i) ∘ₗ
        Linear.rightComp k ((K.restriction ComplexShape.embeddingDownIntUpInt).homology i) h :=
    LinearMap.ext fun g ↦
      TauCeti.ChainComplex.kroneckerSectionOfRetraction_coefficient_naturality h i
        (restrictionDownICyclesRetraction K i) (iCycles_restrictionDownICyclesRetraction K i) g
  have h3 := congrArg ModuleCat.Hom.hom
    (homologyMap_postcomp_linearHomComplexSingleHomologyIso_inv (k := k) K h i)
  simp only [ModuleCat.hom_comp] at h3
  exact linearMap_comp_three_naturality h1 h2 h3

/-- **Coefficient naturality of `linearHomComplexSingleKroneckerSection`**:
`linearHomComplexSingleKroneckerSection` commutes with postcomposition by any morphism
`h : Y₁ ⟶ Y₂`. -/
theorem linearHomComplexSingleKroneckerSection_coefficient_naturality {Y₁ Y₂ : C} (h : Y₁ ⟶ Y₂)
    (i : ℤ) [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y₁) :
    (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map h)) i).hom
        (linearHomComplexSingleKroneckerSection k K Y₁ i g) =
      linearHomComplexSingleKroneckerSection k K Y₂ i (g ≫ h) :=
  ConcreteCategory.congr_hom
    (linearHomComplexSingleKroneckerSection_coefficient_naturality_hom h i) g

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
    (TauCeti.extLinearEquivOfIso k (restrictionDownHomologySubOneIso K i).symm
      (Iso.refl Y) 1).toLinearMap

private lemma linearHomComplexSingleExtToHomology_eq (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] :
    linearHomComplexSingleExtToHomology.{w} k K Y i =
      (linearHomComplexSingleHomologyIso k K Y i).inv.hom ∘ₗ
        TauCeti.ChainComplex.extToHomology k _ Y i (i - 1) ∘ₗ
        (TauCeti.extLinearEquivOfIso k (restrictionDownHomologySubOneIso K i).symm
          (Iso.refl Y) 1).toLinearMap := by
  rw [linearHomComplexSingleExtToHomology, CategoryTheory.Iso.toLinearMap_toLinearEquiv,
    Iso.symm_hom]

/-- Transporting an extension class of the kernel sequence of `K` in degree `1 - i` along
`restrictionHomologyIsoOfSurjective` gives the corresponding extension class of the kernel sequence
of `K.restriction embeddingDownIntUpInt` in degree `i - 1`, precomposed with the induced boundary
isomorphism. -/
private lemma extLinearEquivOfIso_restrictionHomologyIso_kernelSequence_extClass_comp_mk₀
    (i : ℤ) (β : kernel (K.homologyπ (1 - i)) ⟶ Y) :
    TauCeti.extLinearEquivOfIso k (restrictionDownHomologySubOneIso K i).symm (Iso.refl Y) 1
        ((K.boundaries_shortExact (1 - i)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      ((K.restriction ComplexShape.embeddingDownIntUpInt).boundaries_shortExact
        (i - 1)).extClass.comp
        (Ext.mk₀ (kernel.map _ _ (restrictionDownCyclesSubOneIso K i).hom
          (restrictionDownHomologySubOneIso K i).hom
          (homologyπ_restrictionDownHomologySubOneIso_hom K i) ≫ β))
        (add_zero 1) := by
  have hn := ShortComplex.ShortExact.extClass_naturality
    ((K.restriction ComplexShape.embeddingDownIntUpInt).boundaries_shortExact (i - 1))
    (K.boundaries_shortExact (1 - i))
    { τ₁ := kernel.map _ _ (restrictionDownCyclesSubOneIso K i).hom
        (restrictionDownHomologySubOneIso K i).hom
        (homologyπ_restrictionDownHomologySubOneIso_hom K i)
      τ₂ := (restrictionDownCyclesSubOneIso K i).hom
      τ₃ := (restrictionDownHomologySubOneIso K i).hom
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (homologyπ_restrictionDownHomologySubOneIso_hom K i).symm }
  rw [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    ← Ext.comp_assoc_of_third_deg_zero, ← hn, Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]

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
  let b := kernel.map _ _ (restrictionDownCyclesSubOneIso K i).hom
    (restrictionDownHomologySubOneIso K i).hom
    (homologyπ_restrictionDownHomologySubOneIso_hom K i)
  let ψ := (linearHomComplexSingleCyclesIso k K Y i).hom.hom φ
  have hψ_bound : ((_root_.ChainComplex.linearYonedaObj
      (K.restriction ComplexShape.embeddingDownIntUpInt) k Y).iCycles i).hom ψ =
      (K.restriction ComplexShape.embeddingDownIntUpInt).toBoundaries i (i - 1) ≫ b ≫ β := by
    apply (cancel_epi (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f i)).inv).mp
    have h1 := restrictionXIso_inv_comp_iCycles_linearHomComplexSingleCyclesIso_hom_apply K Y i φ
    have h2 : Cochain.toSingleEquiv (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) =
        K.toBoundaries (-i) (1 - i) ≫ β := hφ
    exact h1.trans (h2.trans (K.restrictionXIso_inv_comp_toBoundaries_kernelMap_assoc
      ComplexShape.embeddingDownIntUpInt ComplexShape.surjective_embeddingDownIntUpInt_f
      i (i - 1) (-i) (1 - i) (ComplexShape.embeddingDownIntUpInt_f i) (by simp) β).symm)
  have h_ext := congrArg (TauCeti.ChainComplex.extToHomology k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i (i - 1))
    (extLinearEquivOfIso_restrictionHomologyIso_kernelSequence_extClass_comp_mk₀ (k := k) K Y i β)
  have h_ext2 := TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ i (i - 1) (b ≫ β) ψ hψ_bound
  have h_final := congrArg ((linearHomComplexSingleHomologyIso k K Y i).symm.toLinearEquiv)
    (h_ext.trans h_ext2)
  simp only [Iso.toLinearEquiv_apply, Iso.symm_hom, ← ModuleCat.comp_apply] at h_final
  rw [homologyπ_linearHomComplexSingleHomologyIso_inv, ← ModuleCat.comp_apply,
    Iso.hom_inv_id_assoc] at h_final
  exact h_final

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
  (linearHomComplexSingleHomologyIso k K Y i).toLinearEquiv.trans
    ((TauCeti.ChainComplex.universalCoefficientEquivOfRetraction.{w} k
        (K.restriction ComplexShape.embeddingDownIntUpInt) Y (sub_add_cancel i 1)
        (restrictionDownICyclesRetraction K i)
        (iCycles_restrictionDownICyclesRetraction K i)).trans
      ((TauCeti.extLinearEquivOfIso k (restrictionDownHomologySubOneIso K i).symm
          (Iso.refl Y) 1).symm.prodCongr
        (Linear.homCongr k (restrictionDownHomologyIso K i) (Iso.refl Y))))

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_symm_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (e : Ext.{w} (K.homology (1 - i)) Y 1) (g : K.homology (-i) ⟶ Y) :
    (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i).symm (e, g) =
      linearHomComplexSingleExtToHomology.{w} k K Y i e +
        linearHomComplexSingleKroneckerSection k K Y i g := by
  simp only [linearHomComplexSingleUniversalCoefficientEquiv,
    linearHomComplexSingleExtToHomology, linearHomComplexSingleKroneckerSection,
    LinearEquiv.trans_symm, LinearEquiv.trans_apply, LinearEquiv.prodCongr_symm,
    LinearEquiv.prodCongr_apply, LinearEquiv.symm_symm, Iso.toLinearEquiv_symm,
    TauCeti.ChainComplex.universalCoefficientEquivOfRetraction_symm_apply,
    map_add, LinearMap.comp_apply, LinearEquiv.coe_coe]

@[simp]
lemma linearHomComplexSingleUniversalCoefficientEquiv_apply_snd (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    (linearHomComplexSingleUniversalCoefficientEquiv.{w} k K Y i x).2 =
      linearHomComplexSingleKronecker k K Y i x := by
  simp only [linearHomComplexSingleUniversalCoefficientEquiv, linearHomComplexSingleKronecker,
    LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    TauCeti.ChainComplex.universalCoefficientEquivOfRetraction_apply_snd,
    LinearMap.comp_apply, LinearEquiv.coe_coe]

private lemma linearHomComplexSingleExtToHomology_naturality_linearMap {K₁ K₂ : CochainComplex C ℤ}
    (φ : K₁ ⟶ K₂) (i : ℤ) [Projective (K₁.cycles (1 - i))] [IsSplitMono (K₁.iCycles (1 - i))]
    [Projective (K₂.cycles (1 - i))] [IsSplitMono (K₂.iCycles (1 - i))] :
    linearHomComplexSingleExtToHomology.{w} k K₁ Y i ∘ₗ
        ((Ext.mk₀ (homologyMap φ (1 - i))).precompOfLinear k Y (zero_add 1)) =
      (homologyMap (linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i).hom ∘ₗ
        linearHomComplexSingleExtToHomology.{w} k K₂ Y i := by
  rw [linearHomComplexSingleExtToHomology_eq, linearHomComplexSingleExtToHomology_eq]
  -- Transport naturality along extLinearEquivOfIso, chain extToHomology, and homology comparison.
  have h1 :
      ((Ext.mk₀ (homologyMap
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt)
          (i - 1))).precompOfLinear k Y (zero_add 1)) ∘ₗ
        (TauCeti.extLinearEquivOfIso k (restrictionDownHomologySubOneIso K₂ i).symm
          (Iso.refl Y) 1).toLinearMap =
      (TauCeti.extLinearEquivOfIso k (restrictionDownHomologySubOneIso K₁ i).symm
          (Iso.refl Y) 1).toLinearMap ∘ₗ
        ((Ext.mk₀ (homologyMap φ (1 - i))).precompOfLinear k Y (zero_add 1)) := by
    ext e
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Ext.bilinearCompOfLinear_apply_apply, TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv,
      Iso.refl_hom, Ext.comp_mk₀_id]
    rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀,
      ← homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom
        ComplexShape.embeddingDownIntUpInt ComplexShape.surjective_embeddingDownIntUpInt_f]
  have h2 :
      (homologyMap
          (K := _root_.ChainComplex.linearYonedaObj
            (K₂.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          (L := _root_.ChainComplex.linearYonedaObj
            (K₁.restriction ComplexShape.embeddingDownIntUpInt) k Y)
          ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map
            (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt).op)
          i).hom ∘ₗ
        TauCeti.ChainComplex.extToHomology.{w} k _ Y i (i - 1) =
      TauCeti.ChainComplex.extToHomology.{w} k _ Y i (i - 1) ∘ₗ
        ((Ext.mk₀ (homologyMap
          (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt)
          (i - 1))).precompOfLinear k Y (zero_add 1)) :=
    LinearMap.ext fun e ↦ (TauCeti.ChainComplex.extToHomology_naturality
      (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt) i (i - 1) e).symm
  have h3 := congrArg ModuleCat.Hom.hom
    (homologyMap_precomp_linearHomComplexSingleHomologyIso_inv (k := k) φ Y i)
  simp only [ModuleCat.hom_comp] at h3
  exact (linearMap_comp_three_naturality h1 h2 h3).symm

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
        (linearHomComplexSingleExtToHomology.{w} k K₂ Y i e) :=
  LinearMap.congr_fun (linearHomComplexSingleExtToHomology_naturality_linearMap φ i) e

private lemma linearHomComplexSingleExtToHomology_coefficient_naturality_linearMap
    {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] :
    linearHomComplexSingleExtToHomology.{w} k K Y₂ i ∘ₗ
        ((Ext.mk₀ g).postcompOfLinear k _ (add_zero 1)) =
      (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom ∘ₗ
        linearHomComplexSingleExtToHomology.{w} k K Y₁ i := by
  rw [linearHomComplexSingleExtToHomology_eq, linearHomComplexSingleExtToHomology_eq]
  -- Transport naturality along extLinearEquivOfIso, chain extToHomology, and homology comparison.
  have h1 :
      ((Ext.mk₀ g).postcompOfLinear k _ (add_zero 1)) ∘ₗ
        (TauCeti.extLinearEquivOfIso k (restrictionDownHomologySubOneIso K i).symm
          (Iso.refl Y₁) 1).toLinearMap =
      (TauCeti.extLinearEquivOfIso k (restrictionDownHomologySubOneIso K i).symm
          (Iso.refl Y₂) 1).toLinearMap ∘ₗ
        ((Ext.mk₀ g).postcompOfLinear k _ (add_zero 1)) := by
    ext e
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.flip_apply,
      Ext.bilinearCompOfLinear_apply_apply, TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv,
      Iso.refl_hom, Ext.comp_mk₀_id]
    exact Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1)
  have h2 :
      (homologyMap (_root_.ChainComplex.linearYonedaObjMap k
          (K.restriction ComplexShape.embeddingDownIntUpInt) g) i).hom ∘ₗ
        TauCeti.ChainComplex.extToHomology.{w} k _ Y₁ i (i - 1) =
      TauCeti.ChainComplex.extToHomology.{w} k _ Y₂ i (i - 1) ∘ₗ
        ((Ext.mk₀ g).postcompOfLinear k _ (add_zero 1)) :=
    LinearMap.ext fun e ↦
      (TauCeti.ChainComplex.extToHomology_coefficient_naturality g i (i - 1) e).symm
  have h3 := congrArg ModuleCat.Hom.hom
    (homologyMap_postcomp_linearHomComplexSingleHomologyIso_inv (k := k) K g i)
  simp only [ModuleCat.hom_comp] at h3
  exact (linearMap_comp_three_naturality h1 h2 h3).symm

/-- **Naturality of `linearHomComplexSingleExtToHomology` in the coefficient object**: pushing an
extension forward along `g : Y₁ ⟶ Y₂` and including it into cohomology agrees with including first
and applying `linearHomComplexPostcomp`. -/
theorem linearHomComplexSingleExtToHomology_coefficient_naturality {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂)
    (i : ℤ) [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w} (K.homology (1 - i)) Y₁ 1) :
    linearHomComplexSingleExtToHomology.{w} k K Y₂ i (e.comp (Ext.mk₀ g) (add_zero 1)) =
      (homologyMap (linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i).hom
        (linearHomComplexSingleExtToHomology.{w} k K Y₁ i e) :=
  LinearMap.congr_fun
    (linearHomComplexSingleExtToHomology_coefficient_naturality_linearMap g i) e

end Ext

end CochainComplex
