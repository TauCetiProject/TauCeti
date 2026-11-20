/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Single
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
import TauCeti.Algebra.Homology.Embedding.Restriction.Surjective

/-!
# The universal coefficient sequence for cochain complexes

Let `K` be a cochain complex indexed by `ℤ` in a `k`-linear abelian category `C`, and let `Y : C`.
In `TauCeti.Algebra.Homology.LinearHomComplex.Single`, regrading `K` into the chain complex
`X = K.restriction ComplexShape.embeddingDownIntUpInt` with `Xᵢ = K⁻ⁱ` identifies
`CochainComplex.linearHomComplex k K ((singleFunctor C 0).obj Y)` with
`ChainComplex.linearYonedaObj X k Y` via `CochainComplex.linearHomComplexSingleIso`, inducing a
sign-free `k`-linear cohomology equivalence `CochainComplex.linearHomComplexSingleHomologyEquiv`
natural in both `K` and `Y`.

Transporting `TauCeti.ChainComplex` along this equivalence and
`HomologicalComplex.restrictionHomologyIsoOfSurjective` gives the cochain Kronecker map
`CochainComplex.kronecker : Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)` and its section
`CochainComplex.kroneckerSection` (characterized on cocycles by
`CochainComplex.kroneckerSection_apply`) over any ring `k`. When `Y` is injective or when
`K.iCycles (1 - i)` and `K.iCycles (-i)` split and `H¹⁻ⁱ(K)` is projective, the Kronecker map is a
`k`-linear equivalence (`CochainComplex.kroneckerEquiv`,
`CochainComplex.kroneckerEquivOfProjectiveHomology`), so cohomology vanishes whenever `H⁻ⁱ(K)` does
(`CochainComplex.isZero_homology_linearHomComplex_singleFunctor_obj_of_projective_homology`).

When `k` is commutative and `C` has `Ext`, this further gives the universal coefficient sequence for
cochain complexes:

`0 ⟶ Ext¹(H¹⁻ⁱ(K), Y) ⟶ Hⁱ(Hom(K, Y[0])) ⟶ (H⁻ⁱ(K) ⟶ Y) ⟶ 0`

when `K.cycles (1 - i)` is projective and `K.iCycles (1 - i)` and `K.iCycles (-i)` are split
monomorphisms (`CochainComplex.extToHomology`, characterized on cocycles by
`CochainComplex.extToHomology_extClass_comp_mk₀`, `CochainComplex.kronecker`,
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

section UniversalCoefficient

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Typed alias for `neg_surjective` so `abstractNestedProofs` inside `def kronecker` and
`def extToHomology` keeps the exact type `Function.Surjective ComplexShape.embeddingDownIntUpInt.f`
at `implicit` transparency. -/
private lemma surjective_embeddingDownIntUpInt_f :
    Function.Surjective ComplexShape.embeddingDownIntUpInt.f :=
  neg_surjective

section Ring

variable {K : CochainComplex C ℤ} {k : Type w} [Ring k] [Linear k C] {Y : C}

variable (K k Y) in
/-- **The Kronecker map for cochain complexes**
`Hⁱ(Hom(K, Y[0])) →ₗ[k] (H⁻ⁱ(K) ⟶ Y)`: evaluates a degree-`i` cohomology class of
`linearHomComplex k K ((singleFunctor C 0).obj Y)` on homology classes of `K` in degree `-i`. -/
def kronecker (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i →ₗ[k] (K.homology (-i) ⟶ Y) :=
  (Linear.homCongr k
    (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
    (Iso.refl Y)).toLinearMap ∘ₗ
    TauCeti.ChainComplex.kronecker k (K.restriction ComplexShape.embeddingDownIntUpInt) Y i ∘ₗ
    (K.linearHomComplexSingleHomologyEquiv k Y i).toLinearMap

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
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ)) = 0 := by
    -- Cross the `ModuleCat` coercion on `(X.linearYonedaObj k Y).d` and unfold `restriction_d`;
    -- `ComplexShape.embeddingDownIntUpInt.f n = -n` holds definitionally.
    erw [TauCeti.ChainComplex.linearYonedaObj_d_apply]
    rw [HomologicalComplex.restriction_d]
    exact hd'
  let ψ := (X.linearYonedaObj k Y).moduleCatCyclesMk _ (i + 1) (by simp) hd
  have hψ := (X.linearYonedaObj k Y).iCycles_moduleCatCyclesMk i _ (i + 1) (by simp) hd
  let hIso := K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)
  let cIso := K.restrictionCyclesIsoOfSurjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)
  -- Type the underlying cocycle explicitly as a morphism `X.X i ⟶ Y` (unfolding `linearYonedaObj`).
  let f : X.X i ⟶ Y := (X.linearYonedaObj k Y).iCycles i ψ
  have hf : f = Cochain.toSingleEquiv (neg_add_cancel i)
      ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := hψ
  calc
    K.homologyπ (-i) ≫ K.kronecker k Y i
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ)
      = K.homologyπ (-i) ≫ hIso.inv ≫
          TauCeti.ChainComplex.kronecker k X Y i ((X.linearYonedaObj k Y).homologyπ i ψ) := by
        simp only [kronecker, LinearMap.comp_apply, LinearEquiv.coe_coe, Linear.homCongr_apply,
          Iso.refl_hom, Category.comp_id, hIso, X]
        rw [linearHomComplexSingleHomologyEquiv_homologyπ k i φ ψ hψ]
    _ = cIso.inv ≫ X.homologyπ i ≫
          TauCeti.ChainComplex.kronecker k X Y i ((X.linearYonedaObj k Y).homologyπ i ψ) := by
        rw [← Category.assoc, homologyπ_restrictionHomologyIsoOfSurjective_inv, Category.assoc]
    _ = cIso.inv ≫ X.iCycles i ≫ f := by
        -- `TauCeti.ChainComplex.kronecker_homologyπ` matches `f` by definitional unfolding of
        -- `(X.linearYonedaObj k Y).X i`.
        exact congrArg (cIso.inv ≫ ·) (TauCeti.ChainComplex.kronecker_homologyπ i ψ)
    _ = K.iCycles (-i) ≫ (K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).inv ≫ f := by
        rw [← Category.assoc, restrictionCyclesIsoOfSurjective_inv_iCycles, Category.assoc]
    _ = K.iCycles (-i) ≫ Cochain.toSingleEquiv (neg_add_cancel i)
          ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
        rw [hf]
        simp only [restrictionXIso, eqToIso.inv]
        -- `(K.restriction ComplexShape.embeddingDownIntUpInt).X i` is `K.X (-i)` definitionally.
        erw [eqToHom_refl, Category.id_comp]

/-- **Naturality of the cochain Kronecker map** in the source cochain complex `K`. -/
lemma kronecker_naturality {K' : CochainComplex C ℤ} (φ : K' ⟶ K) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K'.kronecker k Y i
        (homologyMap (TauCeti.linearHomComplexPrecomp k φ ((singleFunctor C 0).obj Y)) i x) =
      homologyMap φ (-i) ≫ K.kronecker k Y i x := by
  have hinv := homologyMap_restrictionHomologyIsoOfSurjective_inv
    ComplexShape.embeddingDownIntUpInt surjective_embeddingDownIntUpInt_f φ i (-i)
    (ComplexShape.embeddingDownIntUpInt_f i)
  simp only [kronecker, LinearMap.comp_apply, LinearEquiv.coe_coe, Linear.homCongr_apply,
    Iso.refl_hom, Category.comp_id, linearHomComplexSingleHomologyEquiv_precomp,
    TauCeti.ChainComplex.kronecker_naturality, ← reassoc_of% hinv]

/-- **Coefficient naturality of the cochain Kronecker map** in `Y`. -/
lemma kronecker_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K.kronecker k Z i
        (homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i x) =
      K.kronecker k Y i x ≫ g := by
  simp only [kronecker, LinearMap.comp_apply, LinearEquiv.coe_coe, Linear.homCongr_apply,
    Iso.refl_hom, Category.comp_id, linearHomComplexSingleHomologyEquiv_postcomp,
    TauCeti.ChainComplex.kronecker_coefficient_naturality, Category.assoc]

/-- For an injective object `Y`, the cochain Kronecker map is bijective. -/
theorem kronecker_bijective [Injective Y] (i : ℤ) :
    Function.Bijective (K.kronecker k Y i) :=
  (Linear.homCongr k
    (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
    (Iso.refl Y)).bijective.comp
    ((TauCeti.ChainComplex.kronecker_bijective i).comp
      (K.linearHomComplexSingleHomologyEquiv k Y i).bijective)

variable (K k Y) in
/-- For an injective object `Y`, the cochain Kronecker map as a `k`-linear equivalence
`Hⁱ(Hom(K, Y[0])) ≃ₗ[k] (H⁻ⁱ(K) ⟶ Y)`. -/
def kroneckerEquiv [Injective Y] (i : ℤ) :
    (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i ≃ₗ[k] (K.homology (-i) ⟶ Y) :=
  LinearEquiv.ofBijective (K.kronecker k Y i) (kronecker_bijective i)

@[simp]
lemma kroneckerEquiv_apply [Injective Y] (i : ℤ)
    (x : (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i) :
    K.kroneckerEquiv k Y i x = K.kronecker k Y i x := by
  rfl

variable (K k Y) in
/-- **The splitting of the cochain universal coefficient sequence**: given a retraction of
`K.iCycles (-i)`, the `k`-linear right inverse `(H⁻ⁱ(K) ⟶ Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` of
`CochainComplex.kronecker` sending `g` to the cocycle class induced by `retraction (K.iCycles (-i))`
(`CochainComplex.kroneckerSection_apply`). -/
def kroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))] :
    (K.homology (-i) ⟶ Y) →ₗ[k] (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  (K.linearHomComplexSingleHomologyEquiv k Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.homologyClassOfComp k Y
      (X := K.restriction ComplexShape.embeddingDownIntUpInt)
      ((K.restrictionXIso ComplexShape.embeddingDownIntUpInt
          (ComplexShape.embeddingDownIntUpInt_f i)).hom ≫
        retraction (K.iCycles (-i)) ≫ K.homologyπ (-i))
      (by
        have hi : ComplexShape.embeddingDownIntUpInt.f i = -i :=
          ComplexShape.embeddingDownIntUpInt_f i
        have hi' : ComplexShape.embeddingDownIntUpInt.f ((ComplexShape.up ℤ).next i) =
            -((ComplexShape.up ℤ).next i) :=
          ComplexShape.embeddingDownIntUpInt_f _
        rw [HomologicalComplex.restriction_d_eq_assoc K ComplexShape.embeddingDownIntUpInt hi' hi,
          Iso.inv_hom_id_assoc, ← K.toCycles_i_assoc, IsSplitMono.id_assoc,
          toCycles_comp_homologyπ, comp_zero])

/-- **`CochainComplex.kroneckerSection` on cocycle representatives**: `K.kroneckerSection k Y i g`
is the class of any cocycle `φ` whose underlying morphism `K⁻ⁱ ⟶ Y` is
`retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) ≫ g`. -/
lemma kroneckerSection_apply (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hφ : Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) =
      retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) ≫ g) :
    K.kroneckerSection k Y i g =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ := by
  let e := ComplexShape.embeddingDownIntUpInt
  let X : ChainComplex C ℤ := K.restriction e
  have hi : e.f i = -i := ComplexShape.embeddingDownIntUpInt_f i
  have hf : X.d ((ComplexShape.up ℤ).next i) i ≫
      (K.restrictionXIso e hi).hom ≫ retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) = 0 := by
    have hi' : e.f ((ComplexShape.up ℤ).next i) = -((ComplexShape.up ℤ).next i) :=
      ComplexShape.embeddingDownIntUpInt_f _
    rw [HomologicalComplex.restriction_d_eq_assoc K e hi' hi, Iso.inv_hom_id_assoc,
      ← K.toCycles_i_assoc, IsSplitMono.id_assoc, toCycles_comp_homologyπ, comp_zero]
  let ψ := TauCeti.ChainComplex.cocycleOfComp k Y (X := X) _ hf g
  have hψ1 : (X.linearYonedaObj k Y).iCycles i ψ =
      ((K.restrictionXIso e hi).hom ≫ retraction (K.iCycles (-i)) ≫ K.homologyπ (-i)) ≫ g :=
    TauCeti.ChainComplex.iCycles_cocycleOfComp _ hf g
  have hψ : (X.linearYonedaObj k Y).iCycles i ψ =
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
    rw [hψ1, hφ]
    simp only [restrictionXIso, eqToIso.hom, Category.assoc]
    -- `X.X i` is `K.X (-i)` definitionally.
    erw [eqToHom_refl, Category.id_comp]
  apply (K.linearHomComplexSingleHomologyEquiv k Y i).injective
  rw [kroneckerSection, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    linearHomComplexSingleHomologyEquiv_homologyπ k i φ ψ hψ]
  exact TauCeti.ChainComplex.homologyClassOfComp_eq _ _ g ψ hψ1

/-- `CochainComplex.kroneckerSection` is a right inverse of `kronecker`. -/
@[simp]
lemma kronecker_kroneckerSection (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (g : K.homology (-i) ⟶ Y) :
    K.kronecker k Y i (K.kroneckerSection k Y i g) = g := by
  rw [← cancel_epi (K.homologyπ (-i))]
  simp only [kronecker, kroneckerSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, Linear.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [homologyπ_restrictionHomologyIsoOfSurjective_inv_assoc,
    TauCeti.ChainComplex.homologyπ_kronecker_homologyClassOfComp,
    restrictionCyclesIsoOfSurjective_inv_iCycles_assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, IsSplitMono.id_assoc]

/-- `CochainComplex.kroneckerSection` commutes with postcomposition by a coefficient morphism
`g : Y ⟶ Z`, for the same chosen retraction of `K.iCycles (-i)`. -/
lemma kroneckerSection_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [IsSplitMono (K.iCycles (-i))] (f : K.homology (-i) ⟶ Y) :
    homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i
        (K.kroneckerSection k Y i f) =
      K.kroneckerSection k Z i (f ≫ g) := by
  let e := ComplexShape.embeddingDownIntUpInt
  let X : ChainComplex C ℤ := K.restriction e
  have hi : e.f i = -i := ComplexShape.embeddingDownIntUpInt_f i
  have hf : X.d ((ComplexShape.up ℤ).next i) i ≫
      (K.restrictionXIso e hi).hom ≫ retraction (K.iCycles (-i)) ≫ K.homologyπ (-i) = 0 := by
    have hi' : e.f ((ComplexShape.up ℤ).next i) = -((ComplexShape.up ℤ).next i) :=
      ComplexShape.embeddingDownIntUpInt_f _
    rw [HomologicalComplex.restriction_d_eq_assoc K e hi' hi, Iso.inv_hom_id_assoc,
      ← K.toCycles_i_assoc, IsSplitMono.id_assoc, toCycles_comp_homologyπ, comp_zero]
  let ψ := TauCeti.ChainComplex.cocycleOfComp k Y (X := X) _ hf f
  have hψ : (X.linearYonedaObj k Y).iCycles i ψ =
      ((K.restrictionXIso e hi).hom ≫ retraction (K.iCycles (-i)) ≫ K.homologyπ (-i)) ≫ f :=
    TauCeti.ChainComplex.iCycles_cocycleOfComp _ hf f
  apply (K.linearHomComplexSingleHomologyEquiv k Z i).injective
  rw [linearHomComplexSingleHomologyEquiv_postcomp]
  simp only [kroneckerSection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [TauCeti.ChainComplex.homologyClassOfComp_eq _ hf f ψ hψ,
    X.homologyMap_linearYonedaObjMap_homologyπ_apply k]
  exact (TauCeti.ChainComplex.homologyClassOfComp_eq _ hf (f ≫ g) _
    ((X.iCycles_cyclesMap_linearYonedaObjMap_apply k g i ψ).trans
      (by rw [hψ, Category.assoc]))).symm

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
  have hj : ComplexShape.embeddingDownIntUpInt.f (i - 1) = 1 - i :=
    (ComplexShape.embeddingDownIntUpInt_f (i - 1)).trans (neg_sub i 1)
  have := (K.isSplitMono_iCycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K.isSplitMono_iCycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i)).2
    inferInstance
  have := (K.projective_homology_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  exact (Linear.homCongr k
    (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
      surjective_embeddingDownIntUpInt_f i (-i) (ComplexShape.embeddingDownIntUpInt_f i))
    (Iso.refl Y)).bijective.comp
    ((TauCeti.ChainComplex.kronecker_bijective_of_projective_homology_of_add_one_eq
      (sub_add_cancel i 1)).comp (K.linearHomComplexSingleHomologyEquiv k Y i).bijective)

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
    K.kroneckerEquivOfProjectiveHomology k Y i x = K.kronecker k Y i x := by
  rfl

/-- If `K.iCycles (1 - i)` and `K.iCycles (-i)` split, `K.homology (1 - i)` is projective, and
`K.homology (-i)` vanishes, then `Hⁱ(Hom(K, Y[0]))` vanishes. -/
theorem isZero_homology_linearHomComplex_singleFunctor_obj_of_projective_homology (i : ℤ)
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
`K.iCycles (1 - i)` is a split monomorphism. Characterized on cocycles by
`CochainComplex.extToHomology_extClass_comp_mk₀`. -/
def extToHomology (i : ℤ) [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Ext.{w'} (K.homology (1 - i)) Y 1 →ₗ[k]
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homology i :=
  have hj : ComplexShape.embeddingDownIntUpInt.f (i - 1) = 1 - i :=
    (ComplexShape.embeddingDownIntUpInt_f (i - 1)).trans (neg_sub i 1)
  have := (K.projective_cycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K.isSplitMono_iCycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  (K.linearHomComplexSingleHomologyEquiv k Y i).symm.toLinearMap ∘ₗ
    TauCeti.ChainComplex.extToHomology.{w'} k
      (K.restriction ComplexShape.embeddingDownIntUpInt) Y i (i - 1) ∘ₗ
    (TauCeti.extLinearEquivOfIso k
      (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).symm
      (Iso.refl Y) 1).toLinearMap

/-- **The characterization of `CochainComplex.extToHomology`**: the class in `Ext¹(H¹⁻ⁱ(K), Y)` of
a morphism `β : kernel (K.homologyπ (1 - i)) ⟶ Y` maps to the class of the cocycle
`K.toBoundaries (-i) (1 - i) ≫ β`, with no sign twist. -/
lemma extToHomology_extClass_comp_mk₀ (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (β : kernel (K.homologyπ (1 - i)) ⟶ Y)
    (φ : (linearHomComplex k K ((singleFunctor C 0).obj Y)).cycles i)
    (hφ : Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) =
      K.toBoundaries (-i) (1 - i) ≫ β) :
    extToHomology.{w'} K k Y i
        ((TauCeti.kernelSequence_shortExact (K.homologyπ (1 - i))).extClass.comp
          (Ext.mk₀ β) (add_zero 1)) =
      (linearHomComplex k K ((singleFunctor C 0).obj Y)).homologyπ i φ := by
  let e := ComplexShape.embeddingDownIntUpInt
  let X : ChainComplex C ℤ := K.restriction e
  have hi : e.f i = -i := ComplexShape.embeddingDownIntUpInt_f i
  have hj : e.f (i - 1) = 1 - i :=
    (ComplexShape.embeddingDownIntUpInt_f (i - 1)).trans (neg_sub i 1)
  have := (K.projective_cycles_restriction_iff_of_surjective e
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K.isSplitMono_iCycles_restriction_iff_of_surjective e
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  let cIso := K.restrictionCyclesIsoOfSurjective e surjective_embeddingDownIntUpInt_f
    (i - 1) (1 - i) hj
  let hIso := K.restrictionHomologyIsoOfSurjective e surjective_embeddingDownIntUpInt_f
    (i - 1) (1 - i) hj
  let b : kernel (X.homologyπ (i - 1)) ⟶ kernel (K.homologyπ (1 - i)) :=
    kernel.map (X.homologyπ (i - 1)) (K.homologyπ (1 - i)) cIso.hom hIso.hom
      (K.homologyπ_restrictionHomologyIsoOfSurjective_hom e surjective_embeddingDownIntUpInt_f
        (i - 1) (1 - i) hj)
  -- State the kernel sequences with explicit `ShortComplex.mk` so that extension-class endpoints
  -- reduce directly to `kernel (homologyπ _)` and `homology _` without unfolding `kernelSequence`.
  have hX : (ShortComplex.mk (kernel.ι (X.homologyπ (i - 1))) (X.homologyπ (i - 1))
      (kernel.condition _)).ShortExact := TauCeti.kernelSequence_shortExact _
  have hK : (ShortComplex.mk (kernel.ι (K.homologyπ (1 - i))) (K.homologyπ (1 - i))
      (kernel.condition _)).ShortExact := TauCeti.kernelSequence_shortExact _
  let s : ShortComplex.mk (kernel.ι (X.homologyπ (i - 1))) (X.homologyπ (i - 1))
        (kernel.condition _) ⟶
      ShortComplex.mk (kernel.ι (K.homologyπ (1 - i))) (K.homologyπ (1 - i))
        (kernel.condition _) :=
    { τ₁ := b
      τ₂ := cIso.hom
      τ₃ := hIso.hom
      comm₁₂ := kernel.lift_ι _ _ _
      comm₂₃ := (K.homologyπ_restrictionHomologyIsoOfSurjective_hom e
        surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).symm }
  have hnat := ShortComplex.ShortExact.extClass_naturality hX hK s
  dsimp only [s] at hnat
  have hbd : X.toBoundaries i (i - 1) ≫ b =
      (K.restrictionXIso e hi).hom ≫ K.toBoundaries (-i) (1 - i) := by
    rw [← cancel_mono (kernel.ι (K.homologyπ (1 - i))), ← cancel_mono (K.iCycles (1 - i))]
    simp only [Category.assoc, b, kernel.lift_ι_assoc, X, toBoundaries_ι_assoc, cIso,
      restrictionCyclesIsoOfSurjective_hom_iCycles, HomologicalComplex.toCycles_i_assoc,
      K.toCycles_i]
    rw [HomologicalComplex.restriction_d_eq_assoc K e hi hj, Iso.inv_hom_id, Category.comp_id]
  let ψ := TauCeti.ChainComplex.cocycleOfComp k Y (X := X) (X.toBoundaries i (i - 1))
    (X.d_toBoundaries _ i (i - 1)) (b ≫ β)
  have hψ1 : (X.linearYonedaObj k Y).iCycles i ψ = X.toBoundaries i (i - 1) ≫ b ≫ β :=
    TauCeti.ChainComplex.iCycles_cocycleOfComp _ _ _
  have hψ : (X.linearYonedaObj k Y).iCycles i ψ =
      Cochain.toSingleEquiv (neg_add_cancel i)
        ((linearHomComplex k K ((singleFunctor C 0).obj Y)).iCycles i φ) := by
    rw [hψ1, ← Category.assoc, hbd, hφ]
    simp only [restrictionXIso, eqToIso.hom, Category.assoc]
    -- `X.X i` is `K.X (-i)` definitionally.
    erw [eqToHom_refl, Category.id_comp]
  have hstep (c : Ext.{w'} (K.homology (1 - i)) Y 1) :
      (K.linearHomComplexSingleHomologyEquiv k Y i) (extToHomology.{w'} K k Y i c) =
        TauCeti.ChainComplex.extToHomology.{w'} k X Y i (i - 1)
          ((TauCeti.extLinearEquivOfIso k hIso.symm (Iso.refl Y) 1) c) := by
    simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, X, hIso, e]
  have hc : (TauCeti.extLinearEquivOfIso k hIso.symm (Iso.refl Y) 1)
      (hK.extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      hX.extClass.comp (Ext.mk₀ (b ≫ β)) (add_zero 1) := by
    simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id]
    rw [← Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (add_zero 1), ← hnat,
      Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 0) (add_zero 1), Ext.mk₀_comp_mk₀]
  apply (K.linearHomComplexSingleHomologyEquiv k Y i).injective
  rw [linearHomComplexSingleHomologyEquiv_homologyπ k i φ ψ hψ]
  exact (hstep _).trans <| (congrArg _ hc).trans <|
    TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ i (i - 1) (b ≫ β) ψ hψ1

/-- **Injectivity in the cochain universal coefficient sequence**: the map
`Ext¹(H¹⁻ⁱ(K), Y) →ₗ[k] Hⁱ(Hom(K, Y[0]))` is injective. -/
theorem extToHomology_injective (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Function.Injective (extToHomology.{w'} K k Y i) := by
  have hj : ComplexShape.embeddingDownIntUpInt.f (i - 1) = 1 - i :=
    (ComplexShape.embeddingDownIntUpInt_f (i - 1)).trans (neg_sub i 1)
  have := (K.projective_cycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K.isSplitMono_iCycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  exact (K.linearHomComplexSingleHomologyEquiv k Y i).symm.injective.comp
    ((TauCeti.ChainComplex.extToHomology_injective (sub_add_cancel i 1)).comp
      (TauCeti.extLinearEquivOfIso k
        (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
          surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).symm
        (Iso.refl Y) 1).injective)

/-- **Exactness in the middle of the cochain universal coefficient sequence**: the kernel of
`CochainComplex.kronecker` in degree `i` is the image of `CochainComplex.extToHomology`. -/
theorem exact_extToHomology_kronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] :
    Function.Exact (extToHomology.{w'} K k Y i) (K.kronecker k Y i) := by
  have hj : ComplexShape.embeddingDownIntUpInt.f (i - 1) = 1 - i :=
    (ComplexShape.embeddingDownIntUpInt_f (i - 1)).trans (neg_sub i 1)
  have := (K.projective_cycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K.isSplitMono_iCycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have hex := TauCeti.ChainComplex.exact_extToHomology_kronecker.{w'} (k := k)
    (X := K.restriction ComplexShape.embeddingDownIntUpInt) (Y := Y) (sub_add_cancel i 1)
  intro x
  rw [kronecker, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.map_eq_zero_iff, LinearEquiv.coe_coe, hex]
  constructor
  · rintro ⟨e, he'⟩
    refine ⟨TauCeti.extLinearEquivOfIso k
      (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj) (Iso.refl Y) 1 e, ?_⟩
    apply (K.linearHomComplexSingleHomologyEquiv k Y i).injective
    simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, TauCeti.extLinearEquivOfIso_apply, Iso.refl_hom, Iso.symm_inv,
      Ext.comp_mk₀_id, ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1),
      Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.mk₀_id_comp, he']
  · rintro ⟨e, rfl⟩
    refine ⟨TauCeti.extLinearEquivOfIso k
      (K.restrictionHomologyIsoOfSurjective ComplexShape.embeddingDownIntUpInt
        surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).symm (Iso.refl Y) 1 e, ?_⟩
    simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]

/-- `CochainComplex.kronecker` vanishes on the image of `CochainComplex.extToHomology`. -/
@[simp]
lemma kronecker_extToHomology (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    K.kronecker k Y i (extToHomology.{w'} K k Y i e) = 0 :=
  (exact_extToHomology_kronecker.{w'} (K := K) (k := k) (Y := Y) i).apply_apply_eq_zero e

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
  have hj : ComplexShape.embeddingDownIntUpInt.f (i - 1) = 1 - i :=
    (ComplexShape.embeddingDownIntUpInt_f (i - 1)).trans (neg_sub i 1)
  have := (K.projective_cycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K.isSplitMono_iCycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K'.projective_cycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K'.isSplitMono_iCycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  apply (K'.linearHomComplexSingleHomologyEquiv k Y i).injective
  rw [linearHomComplexSingleHomologyEquiv_precomp]
  simp only [extToHomology, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  rw [← TauCeti.ChainComplex.extToHomology_naturality]
  congr 1
  simp only [TauCeti.extLinearEquivOfIso_apply, Iso.symm_inv, Iso.refl_hom, Ext.comp_mk₀_id,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1), Ext.mk₀_comp_mk₀,
    homologyMap_restrictionMap_restrictionHomologyIsoOfSurjective_hom]

/-- **Coefficient naturality of `CochainComplex.extToHomology` in `Y`**. -/
lemma extToHomology_coefficient_naturality {Z : C} (g : Y ⟶ Z) (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    extToHomology.{w'} K k Z i (e.comp (Ext.mk₀ g) (add_zero 1)) =
      homologyMap (TauCeti.linearHomComplexPostcomp k K ((singleFunctor C 0).map g)) i
        (extToHomology.{w'} K k Y i e) := by
  have hj : ComplexShape.embeddingDownIntUpInt.f (i - 1) = 1 - i :=
    (ComplexShape.embeddingDownIntUpInt_f (i - 1)).trans (neg_sub i 1)
  have := (K.projective_cycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  have := (K.isSplitMono_iCycles_restriction_iff_of_surjective ComplexShape.embeddingDownIntUpInt
    surjective_embeddingDownIntUpInt_f (i - 1) (1 - i) hj).2 inferInstance
  apply (K.linearHomComplexSingleHomologyEquiv k Z i).injective
  rw [linearHomComplexSingleHomologyEquiv_postcomp]
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

/-- `CochainComplex.universalCoefficientEquiv` sends `extToHomology e` to `(e, 0)`. -/
@[simp]
lemma universalCoefficientEquiv_extToHomology (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (e : Ext.{w'} (K.homology (1 - i)) Y 1) :
    universalCoefficientEquiv.{w'} K k Y i (extToHomology.{w'} K k Y i e) = (e, 0) := by
  rw [← universalCoefficientEquiv_symm_inl i e, LinearEquiv.apply_symm_apply]

/-- `CochainComplex.universalCoefficientEquiv` sends `kroneckerSection g` to `(0, g)`. -/
@[simp]
lemma universalCoefficientEquiv_kroneckerSection (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (g : K.homology (-i) ⟶ Y) :
    universalCoefficientEquiv.{w'} K k Y i (K.kroneckerSection k Y i g) = (0, g) := by
  rw [← universalCoefficientEquiv_symm_inr i g, LinearEquiv.apply_symm_apply]

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
