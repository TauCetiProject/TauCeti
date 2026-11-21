/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import TauCeti.Algebra.Homology.LinearHomComplex.Single.Comparison
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
import TauCeti.Algebra.Homology.Embedding.Restriction.Surjective
import TauCeti.LinearAlgebra.Exact

/-!
# The universal coefficient theorem for `linearHomComplex` into a degree-zero object

For a `ℤ`-indexed cochain complex `K` in a `k`-linear abelian category `C` and an object `Y : C`,
`CochainComplex.linearHomComplex k K ((singleFunctor C 0).obj Y)` has degree-`i` cochains
identified with `K.X (-i) ⟶ Y` via `Cochain.toSingleLinearEquiv (neg_add_cancel i)`, with
differential `f ↦ (-1)^(i + 1) • (K.d (-(i + 1)) (-i) ≫ f)`
(`TauCeti.Algebra.Homology.LinearHomComplex.Single.Basic`).

Reindexing `K` along `n ↦ -n` (`ComplexShape.embeddingDownIntUpInt`) gives a chain complex `K'`
whose unsigned dual `K'.linearYonedaObj k Y` is compared with `linearHomComplex k K Y[0]` on
complexes (`TauCeti.linearHomComplexSingle₀Iso`) and on cohomology
(`TauCeti.linearHomComplexSingle₀HomologyIso`) in
`TauCeti.Algebra.Homology.LinearHomComplex.Single.Comparison`.

When `k` is commutative (`[CommRing k]`) and `C` has `Ext` (`[HasExt C]`), transporting the
chain-complex universal coefficient sequence (`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`)
yields, for `i + j = 1` (i.e. `j = 1 - i`), the split short exact sequence

`0 ⟶ Ext¹(Hʲ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`

when `Zʲ(K)` is projective and `Z⁻ⁱ(K) ⟶ K⁻ⁱ`, `Zʲ(K) ⟶ Kʲ` split. Both maps are natural in `K`
and `Y`; the splitting (`TauCeti.cochainKroneckerSection`) is natural in `Y` (non-naturality in `K`
is proved in `TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.NonNaturality`).

## Main definitions and results

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

section RestrictionHelpers

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reindexing a `ℤ`-indexed cochain complex `K` along `n ↦ -n` as a chain complex. -/
private abbrev negChain (K : CochainComplex C ℤ) : ChainComplex C ℤ :=
  K.restriction ComplexShape.embeddingDownIntUpInt

private lemma surjective_embeddingDownIntUpInt_f :
    Function.Surjective ComplexShape.embeddingDownIntUpInt.f :=
  neg_involutive.surjective

private lemma negChain_f_sub_one {i j : ℤ} (hij : i + j = 1) :
    ComplexShape.embeddingDownIntUpInt.f (i - 1) = j := by
  rw [ComplexShape.embeddingDownIntUpInt_f]; omega

private abbrev negChainHomologyIso (K : CochainComplex C ℤ) {i j : ℤ} (hij : i + j = 1) :
    (negChain K).homology (i - 1) ≅ K.homology j :=
  K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j (negChain_f_sub_one hij)

private lemma negChain_projective_cycles (K : CochainComplex C ℤ) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] :
    Projective ((negChain K).cycles (i - 1)) :=
  K.projective_restriction_cycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j (negChain_f_sub_one hij)

private lemma negChain_isSplitMono_iCycles (K : CochainComplex C ℤ) {i j : ℤ} (hij : i + j = 1)
    [IsSplitMono (K.iCycles j)] :
    IsSplitMono ((negChain K).iCycles (i - 1)) :=
  K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j (negChain_f_sub_one hij)

private lemma negChain_projective_homology (K : CochainComplex C ℤ) {i j : ℤ} (hij : i + j = 1)
    [Projective (K.homology j)] :
    Projective ((negChain K).homology (i - 1)) :=
  K.projective_restriction_homology_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) j (negChain_f_sub_one hij)

private lemma negChain_isSplitMono_iCycles_self (K : CochainComplex C ℤ) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] :
    IsSplitMono ((negChain K).iCycles i) :=
  K.isSplitMono_restriction_iCycles_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)

private lemma restrictionXIso_hom_comp (K : CochainComplex C ℤ) (i : ℤ) {Z : C}
    (g : K.X (-i) ⟶ Z) :
    (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
      (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫ g = g :=
  Category.id_comp g

/-- Comparison morphism from degree-`(i - 1)` boundaries of `negChain K` to degree-`j` boundaries
of `K` induced by the cycle and homology comparison isomorphisms along `n ↦ -n`. -/
private def negChainBoundariesMap (K : CochainComplex C ℤ) {i j : ℤ} (hij : i + j = 1) :
    kernel ((negChain K).homologyπ (i - 1)) ⟶ kernel (K.homologyπ j) :=
  kernel.map ((negChain K).homologyπ (i - 1)) (K.homologyπ j)
    (K.restrictionCyclesIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f (i - 1) j (negChain_f_sub_one hij)).hom
    (negChainHomologyIso K hij).hom
    (K.homologyπ_restrictionHomologyIsoOfSurjective_hom ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f (i - 1) j (negChain_f_sub_one hij))

/-- Boundary compatibility under `n ↦ -n`: `toBoundaries` on `negChain K` followed by
`negChainBoundariesMap` matches `K.toBoundaries (-i) j` after `restrictionXIso`. -/
private lemma negChain_toBoundaries_comp_boundariesMap (K : CochainComplex C ℤ) {i j : ℤ}
    (hij : i + j = 1) :
    (negChain K).toBoundaries i (i - 1) ≫ negChainBoundariesMap K hij =
      (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
        (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫ K.toBoundaries (-i) j := by
  -- Cancel the boundary and cycle monomorphisms to reduce to the differential formula.
  rw [← cancel_mono (kernel.ι (K.homologyπ j)), ← cancel_mono (K.iCycles j)]
  simp only [Category.assoc, negChainBoundariesMap, kernel.lift_ι,
    HomologicalComplex.toBoundaries_ι_assoc, HomologicalComplex.toBoundaries_ι,
    HomologicalComplex.restrictionCyclesIsoOfSurjective_hom_iCycles,
    HomologicalComplex.toCycles_i_assoc, HomologicalComplex.toCycles_i]
  rw [K.restriction_d_eq ComplexShape.embeddingDownIntUpInt
    (ComplexShape.embeddingDownIntUpInt_f i) (negChain_f_sub_one hij), Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end RestrictionHelpers

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
  have := negChain_isSplitMono_iCycles K hij
  have := negChain_isSplitMono_iCycles_self K i
  have := negChain_projective_homology K hij
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
is a `k`-linear equivalence `Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (K.homology (-i) ⟶ Y)`. -/
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
  have := negChain_projective_cycles K hij
  have := negChain_isSplitMono_iCycles K hij
  (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom.comp <|
    (ChainComplex.extToHomology.{w} k (negChain K) Y i (i - 1)).comp
      (extLinearEquivOfIso k (negChainHomologyIso K hij).symm (Iso.refl Y) 1).toLinearMap

/-- Extension-class transport under `n ↦ -n`: transporting the extension class of
`β : Bʲ(K) ⟶ Y` along `negChainHomologyIso` gives the extension class of
`negChainBoundariesMap K hij ≫ β` on `negChain K`. -/
private lemma extLinearEquivOfIso_negChain_extClass_comp_mk₀ {i j : ℤ}
    (hij : i + j = 1) (β : kernel (K.homologyπ j) ⟶ Y) :
    (extLinearEquivOfIso k (negChainHomologyIso K hij).symm (Iso.refl Y) 1)
      ((kernelSequence_shortExact (K.homologyπ j)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
    (kernelSequence_shortExact ((negChain K).homologyπ (i - 1))).extClass.comp
      (Ext.mk₀ (negChainBoundariesMap K hij ≫ β)) (add_zero 1) := by
  -- Assemble the morphism between the boundary-cycle-homology short exact sequences.
  let s : ShortComplex.mk (kernel.ι ((negChain K).homologyπ (i - 1)))
        ((negChain K).homologyπ (i - 1)) (kernel.condition _) ⟶
      ShortComplex.mk (kernel.ι (K.homologyπ j)) (K.homologyπ j) (kernel.condition _) :=
    { τ₁ := negChainBoundariesMap K hij
      τ₂ := (K.restrictionCyclesIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f (i - 1) j (negChain_f_sub_one hij)).hom
      τ₃ := (negChainHomologyIso K hij).hom
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (K.homologyπ_restrictionHomologyIsoOfSurjective_hom
        ComplexShape.embeddingDownIntUpInt surjective_embeddingDownIntUpInt_f
        (i - 1) j (negChain_f_sub_one hij)).symm }
  have hn := ShortComplex.ShortExact.extClass_naturality
    (kernelSequence_shortExact ((negChain K).homologyπ (i - 1)))
    (kernelSequence_shortExact (K.homologyπ j)) s
  dsimp only [s, ShortComplex.kernelSequence] at hn ⊢
  rw [extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    ← Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (zero_add 1), ← hn,
    Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 0) (add_zero 1), Ext.mk₀_comp_mk₀]

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
  have := negChain_projective_cycles K hij
  have := negChain_isSplitMono_iCycles K hij
  -- Build the matching cocycle `ψ` on `negChain K` via the boundary comparison map.
  let ψ := ChainComplex.cocycleOfComp k Y (X := negChain K)
    ((negChain K).toBoundaries i (i - 1)) ((negChain K).d_toBoundaries _ i (i - 1))
    (negChainBoundariesMap K hij ≫ β)
  have hψ : ((negChain K).linearYonedaObj k Y).iCycles i ψ =
      Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)
        (((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i).hom φ) := by
    rw [ChainComplex.iCycles_cocycleOfComp, ← Category.assoc,
      negChain_toBoundaries_comp_boundariesMap K hij, Category.assoc, hφ]
    exact restrictionXIso_hom_comp K i _
  -- Transport the extension class to `negChain K`, evaluate `ChainComplex.extToHomology`, and
  -- return to `linearHomComplex` along `linearHomComplexSingle₀HomologyIso`.
  have harg := extLinearEquivOfIso_negChain_extClass_comp_mk₀ (k := k) (K := K) (Y := Y) hij β
  exact (congrArg (fun e ↦ (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom
      (ChainComplex.extToHomology k (negChain K) Y i (i - 1) e)) harg).trans
    ((congrArg (linearHomComplexSingle₀HomologyIso k K Y i).inv.hom
      (ChainComplex.extToHomology_extClass_comp_mk₀ i (i - 1)
        (negChainBoundariesMap K hij ≫ β) ψ (ChainComplex.iCycles_cocycleOfComp _ _ _))).trans
      (linearHomComplexSingle₀HomologyIso_inv_homologyπ K Y i φ ψ hψ))

/-- **Injectivity of `cochainExtToHomology`**: in bidegree `i + j = 1`, the map
`Ext¹(Hʲ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem cochainExtToHomology_injective {i j : ℤ} (hij : i + j = 1) [Projective (K.cycles j)]
    [IsSplitMono (K.iCycles j)] :
    Function.Injective (cochainExtToHomology.{w} k K Y hij) := by
  have := negChain_projective_cycles K hij
  have := negChain_isSplitMono_iCycles K hij
  exact (linearHomComplexSingle₀HomologyIso k K Y i).symm.toLinearEquiv.injective.comp <|
    (ChainComplex.extToHomology_injective (k := k) (X := negChain K) (Y := Y)
      (show i - 1 + 1 = i by omega)).comp
        (extLinearEquivOfIso k (negChainHomologyIso K hij).symm (Iso.refl Y) 1).injective

/-- **Middle exactness of the universal coefficient sequence for `linearHomComplex`**: for
`i + j = 1`, the image of `cochainExtToHomology` is the kernel of `cochainKronecker`. -/
theorem exact_cochainExtToHomology_cochainKronecker {i j : ℤ} (hij : i + j = 1)
    [Projective (K.cycles j)] [IsSplitMono (K.iCycles j)] :
    Function.Exact (cochainExtToHomology.{w} k K Y hij) (cochainKronecker k K Y i) := by
  have := negChain_projective_cycles K hij
  have := negChain_isSplitMono_iCycles K hij
  have h1 : cochainExtToHomology.{w} k K Y hij =
      ((linearHomComplexSingle₀HomologyIso k K Y i).toLinearEquiv.symm.toLinearMap.comp
        (ChainComplex.extToHomology.{w} k (negChain K) Y i (i - 1))).comp
        (extLinearEquivOfIso k (negChainHomologyIso K hij).symm (Iso.refl Y) 1).toLinearMap := by
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
  have := negChain_projective_cycles K₁ hij
  have := negChain_isSplitMono_iCycles K₁ hij
  have := negChain_projective_cycles K₂ hij
  have := negChain_isSplitMono_iCycles K₂ hij
  apply (linearHomComplexSingle₀HomologyIso k K₁ Y i).toLinearEquiv.injective
  have hext : (extLinearEquivOfIso k (negChainHomologyIso K₁ hij).symm (Iso.refl Y) 1)
      ((Ext.mk₀ (homologyMap φ j)).comp e (zero_add 1)) =
      (Ext.mk₀ (homologyMap (HomologicalComplex.restrictionMap φ ComplexShape.embeddingDownIntUpInt)
        (i - 1))).comp
          ((extLinearEquivOfIso k (negChainHomologyIso K₂ hij).symm (Iso.refl Y) 1) e)
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
  have := negChain_projective_cycles K hij
  have := negChain_isSplitMono_iCycles K hij
  apply (linearHomComplexSingle₀HomologyIso k K Y₂ i).toLinearEquiv.injective
  have hext : (extLinearEquivOfIso k (negChainHomologyIso K hij).symm (Iso.refl Y₂) 1)
      (e.comp (Ext.mk₀ g) (add_zero 1)) =
      ((extLinearEquivOfIso k (negChainHomologyIso K hij).symm (Iso.refl Y₁) 1) e).comp
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
