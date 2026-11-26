/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Ext.ScalarAction
public import TauCeti.Algebra.Homology.LinearHomComplex.Single
import Mathlib.Algebra.Module.LinearMap.End
import TauCeti.Algebra.Category.ModuleCat.ScalarAction
import TauCeti.CategoryTheory.Preadditive.Endomorphism

/-!
# Bimodule Hom complexes and commuting scalar actions on cohomology

Let `K` be a cochain complex in `ModuleCat k` and let `M` be a `k`-module carrying a commuting
action of a semiring `S` (`[SMulCommClass k S M]`).

When `S` is a ring (over any ring `k`), the degreewise `S`-modules `K.X (-i) →ₗ[k] M` with signed
precomposition differential `f ↦ (-1) ^ (i + 1) • (f ∘ₗ K.d (-j) (-i))` assemble into the
`(k, S)`-bimodule Hom cochain complex `CochainComplex.bimoduleHomComplex` in `ModuleCat S`.

When `k` is commutative (and `S` is any semiring), scalar multiplication by `s : S` on `M` is a
`k`-linear endomorphism of `M`, so postcomposition via `TauCeti.linearHomComplexPostcomp` defines
a cochain endomorphism `CochainComplex.linearHomComplexSingleScalarHom` of
`CochainComplex.linearHomComplex k K ((singleFunctor _ 0).obj (ModuleCat.of k M))` and induces a
ring homomorphism `CochainComplex.linearHomComplexSingleHomologyAction` into the `k`-linear
endomorphism ring of its cohomology. Both arrows of the universal coefficient sequence
(`CochainComplex.linearHomComplexSingleKronecker`,
`CochainComplex.linearHomComplexSingleExtToHomology`) and the splitting induced by a `k`-linear
cycle retraction (`CochainComplex.linearHomComplexSingleKroneckerSection`,
`CochainComplex.linearHomComplexSingleUniversalCoefficientEquiv`) commute with this `S`-action and
`TauCeti.extScalarAction`.

When `S` is a ring, forgetting scalar actions identifies `linearHomComplex` into `M` placed in
degree `0` with `bimoduleHomComplex` as cochain complexes of abelian groups
(`CochainComplex.forget₂BimoduleHomComplexIso`), intertwining `linearHomComplexSingleScalarHom` with
`s • 𝟙 _` when `S` is commutative
(`CochainComplex.map_linearHomComplexSingleScalarHom_comp_forget₂BimoduleHomComplexIso_hom`).

## Main definitions

* `CochainComplex.bimoduleHomComplex` and `CochainComplex.bimoduleHomComplexXIso`: the cochain
  complex `i ↦ (K.X (-i) →ₗ[k] M)` in `ModuleCat S` and its degreewise carrier identification.
* `CochainComplex.linearHomComplexSingleScalarHom` and
  `CochainComplex.linearHomComplexSingleHomologyAction`: the cochain endomorphism and cohomology
  ring action induced by a commuting semiring scalar action on `M`, with equivariance of the
  universal coefficient sequence.
* `CochainComplex.forget₂BimoduleHomComplexIso`: comparison between `linearHomComplex` into `M[0]`
  and `bimoduleHomComplex` in `CochainComplex AddCommGrpCat ℤ`.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press (1994),
  Sections 1.2 and 2.7.
* Mathlib's `CochainComplex.linearHomComplex` and
  `CochainComplex.HomComplex.Cochain.toSingleLinearEquiv`.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian
open CochainComplex CochainComplex.HomComplex

universe v u

namespace CochainComplex

section Ring

variable {k : Type u} [Ring k] (K : CochainComplex (ModuleCat.{v} k) ℤ)
  (S : Type*) [Ring S]
  (M : Type v) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- **The `(k, S)`-bimodule Hom cochain complex** in `ModuleCat S`: in degree `i` it is the
`S`-module `K.X (-i) →ₗ[k] M`, with differential `f ↦ (-1) ^ (i + 1) • (f ∘ₗ K.d (-j) (-i))`. -/
def bimoduleHomComplex : CochainComplex (ModuleCat.{v} S) ℤ where
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
    have hdd : (K.d (-j) (-i)).hom ((K.d (-l) (-j)).hom x) = 0 := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero,
        LinearMap.zero_apply]
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.smul_apply, hdd, map_zero, smul_zero, ModuleCat.hom_zero,
      LinearMap.zero_apply]

/-- The degree-`i` carrier of `bimoduleHomComplex` is the `S`-module `K.X (-i) →ₗ[k] M`. -/
def bimoduleHomComplexXIso (i : ℤ) :
    (K.bimoduleHomComplex S M).X i ≅ ModuleCat.of S (K.X (-i) →ₗ[k] M) :=
  Iso.refl _

/-- Evaluation of the differential of `bimoduleHomComplex` under `bimoduleHomComplexXIso`. -/
@[simp]
lemma bimoduleHomComplex_d_apply (i : ℤ) (z : (K.bimoduleHomComplex S M).X i) :
    (K.bimoduleHomComplexXIso S M (i + 1)).hom.hom
      (((K.bimoduleHomComplex S M).d i (i + 1)).hom z) =
      ((i + 1).negOnePow : ℤ) •
        ((K.bimoduleHomComplexXIso S M i).hom.hom z).comp (K.d (-(i + 1)) (-i)).hom := by
  rfl

end Ring

section SemiringScalar

variable {k : Type u} [CommRing k]
  (S : Type*) [Semiring S]
  (M : Type v) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

section Receiver

variable (K : CochainComplex (ModuleCat.{v} k) ℤ)

/-- Scalar multiplication by `s : S` on `M` as a cochain endomorphism of
`linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M))`, defined via
`TauCeti.linearHomComplexPostcomp`. -/
def linearHomComplexSingleScalarHom (s : S) :
    linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) ⟶
      linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) :=
  have := SMulCommClass.symm k S M
  TauCeti.linearHomComplexPostcomp k K
    ((singleFunctor (ModuleCat.{v} k) 0).map
      (ModuleCat.ofHom (DistribSMul.toLinearMap k M s)))

/-- `CochainComplex.linearHomComplexSingleScalarHom` is postcomposition on `linearHomComplex` by
scalar multiplication on `M` placed in degree `0`. -/
lemma linearHomComplexSingleScalarHom_def (s : S) :
    have := SMulCommClass.symm k S M
    K.linearHomComplexSingleScalarHom S M s =
      TauCeti.linearHomComplexPostcomp k K
        ((singleFunctor (ModuleCat.{v} k) 0).map
          (ModuleCat.ofHom (DistribSMul.toLinearMap k M s))) := by
  rfl

@[simp]
lemma linearHomComplexSingleScalarHom_zero :
    K.linearHomComplexSingleScalarHom S M 0 = 0 := by
  have := SMulCommClass.symm k S M
  have h0 : DistribSMul.toLinearMap k M (0 : S) = 0 := map_zero (Module.toModuleEnd k M)
  rw [linearHomComplexSingleScalarHom_def, h0]
  simp

@[simp]
lemma linearHomComplexSingleScalarHom_one :
    K.linearHomComplexSingleScalarHom S M 1 = 𝟙 _ := by
  have := SMulCommClass.symm k S M
  have h1 : DistribSMul.toLinearMap k M (1 : S) = LinearMap.id := map_one (Module.toModuleEnd k M)
  rw [linearHomComplexSingleScalarHom_def, h1]
  simp

@[simp]
lemma linearHomComplexSingleScalarHom_add (r s : S) :
    K.linearHomComplexSingleScalarHom S M (r + s) =
      K.linearHomComplexSingleScalarHom S M r + K.linearHomComplexSingleScalarHom S M s := by
  have := SMulCommClass.symm k S M
  have hadd : DistribSMul.toLinearMap k M (r + s) =
      DistribSMul.toLinearMap k M r + DistribSMul.toLinearMap k M s :=
    map_add (Module.toModuleEnd k M) r s
  rw [linearHomComplexSingleScalarHom_def, hadd, ModuleCat.ofHom_add,
    Functor.map_add, TauCeti.linearHomComplexPostcomp_add,
    ← linearHomComplexSingleScalarHom_def, ← linearHomComplexSingleScalarHom_def]

@[simp]
lemma linearHomComplexSingleScalarHom_mul (r s : S) :
    K.linearHomComplexSingleScalarHom S M (r * s) =
      K.linearHomComplexSingleScalarHom S M s ≫ K.linearHomComplexSingleScalarHom S M r := by
  have := SMulCommClass.symm k S M
  have hmul : DistribSMul.toLinearMap k M (r * s) =
      (DistribSMul.toLinearMap k M r).comp (DistribSMul.toLinearMap k M s) :=
    map_mul (Module.toModuleEnd k M) r s
  rw [linearHomComplexSingleScalarHom_def, hmul, ModuleCat.ofHom_comp,
    Functor.map_comp, TauCeti.linearHomComplexPostcomp_comp,
    ← linearHomComplexSingleScalarHom_def, ← linearHomComplexSingleScalarHom_def]

/-- Under `Cochain.toSingleEquiv (neg_add_cancel i)`, `linearHomComplexSingleScalarHom` acts
pointwise as `s • f` on `K.X (-i) →ₗ[k] M`. -/
@[simp]
lemma toSingleEquiv_linearHomComplexSingleScalarHom_f_apply (s : S) (i : ℤ)
    (z : Cochain K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) i) :
    ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i)
        (dsimp% only [linearHomComplex_X]
          ((K.linearHomComplexSingleScalarHom S M s).f i).hom z)) =
      s • ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i) z) := by
  obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  rw [linearHomComplexSingleScalarHom_def]
  -- `linearHomComplexPostcomp_f_apply` is stated on the unfolded carrier `Cochain K _ i`.
  erw [TauCeti.linearHomComplexPostcomp_f_apply]
  rw [← Cochain.toSingleMk_postcomp, Cochain.toSingleEquiv_toSingleMk,
    Cochain.toSingleEquiv_toSingleMk]
  rfl

/-- **The `S`-action on the cohomology of `linearHomComplex`** into `M` placed in degree `0`,
induced by `TauCeti.linearHomComplexPostcomp` applied to scalar multiplication on `M`. -/
def linearHomComplexSingleHomologyAction (i : ℤ) :
    S →+* Module.End k
      ((linearHomComplex k K
        ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M))).homology i) :=
  have := SMulCommClass.symm k S M
  (ModuleCat.endRingEquiv _).toRingHom.comp
    ((((singleFunctor (ModuleCat.{v} k) 0 ⋙
      (TauCeti.linearHomComplexFunctor k).obj (Opposite.op K) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (ComplexShape.up ℤ) i).mapEndRingHom
        (ModuleCat.of k M))).comp
      ((ModuleCat.endRingEquiv (ModuleCat.of k M)).symm.toRingHom.comp
        (Module.toModuleEnd k M)))

@[simp]
lemma linearHomComplexSingleHomologyAction_apply (i : ℤ) (s : S)
    (x : (linearHomComplex k K
      ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M))).homology i) :
    K.linearHomComplexSingleHomologyAction S M i s x =
      homologyMap (K.linearHomComplexSingleScalarHom S M s) i x := by
  have := SMulCommClass.symm k S M
  let F := singleFunctor (ModuleCat.{v} k) 0 ⋙
    (TauCeti.linearHomComplexFunctor k).obj (Opposite.op K) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{v} k) (ComplexShape.up ℤ) i
  have h1 : (ModuleCat.endRingEquiv (F.obj (ModuleCat.of k M))
      (F.mapEndRingHom (ModuleCat.of k M)
        ((ModuleCat.endRingEquiv (ModuleCat.of k M)).symm (Module.toModuleEnd k M s)))) x =
      homologyMap (K.linearHomComplexSingleScalarHom S M s) i x := by
    simp only [ModuleCat.endRingEquiv_apply, CategoryTheory.Functor.mapEndRingHom_apply_asHom,
      Module.toModuleEnd_apply, linearHomComplexSingleScalarHom]
    simp only [F, Functor.comp_map, TauCeti.linearHomComplexFunctor_obj_map]
    simp [ModuleCat.endRingEquiv]
    rfl
  exact h1

/-- `CochainComplex.linearHomComplexSingleKronecker` commutes with the `S`-scalar actions on
cohomology and on `K.homology (-i) →ₗ[k] M`. -/
lemma hom_linearHomComplexSingleKronecker_linearHomComplexSingleHomologyAction (i : ℤ) (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    (linearHomComplexSingleKronecker k K (ModuleCat.of k M) i
        (K.linearHomComplexSingleHomologyAction S M i s x)).hom =
      s • (linearHomComplexSingleKronecker k K (ModuleCat.of k M) i x).hom := by
  have := SMulCommClass.symm k S M
  rw [linearHomComplexSingleHomologyAction_apply, linearHomComplexSingleScalarHom_def,
    linearHomComplexSingleKronecker_coefficient_naturality, ModuleCat.comp_ofHom_distribSMul,
    ModuleCat.hom_ofHom]

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`,
`CochainComplex.linearHomComplexSingleKroneckerSection` commutes with the `S`-scalar action. -/
lemma linearHomComplexSingleKroneckerSection_ofHom_smul (i : ℤ) [IsSplitMono (K.iCycles (-i))]
    (s : S) (f : K.homology (-i) →ₗ[k] M) :
    linearHomComplexSingleKroneckerSection k K (ModuleCat.of k M) i (ModuleCat.ofHom (s • f)) =
      K.linearHomComplexSingleHomologyAction S M i s
        (linearHomComplexSingleKroneckerSection k K (ModuleCat.of k M) i (ModuleCat.ofHom f)) := by
  have := SMulCommClass.symm k S M
  let g : K.homology (-i) ⟶ ModuleCat.of k M := ModuleCat.ofHom f
  rw [linearHomComplexSingleHomologyAction_apply, linearHomComplexSingleScalarHom_def]
  exact ((linearHomComplexSingleKroneckerSection_coefficient_naturality (k := k) K
    (ModuleCat.ofHom (DistribSMul.toLinearMap k M s)) i g).trans
    (congrArg (linearHomComplexSingleKroneckerSection k K (ModuleCat.of k M) i)
      (ModuleCat.comp_ofHom_distribSMul (k := k) (S := S) (M := M) g s))).symm

/-- `CochainComplex.linearHomComplexSingleExtToHomology` commutes with the `S`-scalar actions on
`Ext¹` and on the cohomology of `linearHomComplex`. -/
lemma linearHomComplexSingleExtToHomology_extScalarAction [Small.{v} k] (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))] (s : S)
    (e : Ext.{v} (K.homology (1 - i)) (ModuleCat.of k M) 1) :
    linearHomComplexSingleExtToHomology.{v} k K (ModuleCat.of k M) i
        (TauCeti.extScalarAction k S M (K.homology (1 - i)) 1 s e) =
      K.linearHomComplexSingleHomologyAction S M i s
        (linearHomComplexSingleExtToHomology.{v} k K (ModuleCat.of k M) i e) := by
  have := SMulCommClass.symm k S M
  rw [TauCeti.extScalarAction_apply, linearHomComplexSingleHomologyAction_apply,
    linearHomComplexSingleScalarHom_def]
  exact linearHomComplexSingleExtToHomology_coefficient_naturality K
    (ModuleCat.ofHom (DistribSMul.toLinearMap k M s)) i e

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`, the universal coefficient splitting
`CochainComplex.linearHomComplexSingleUniversalCoefficientEquiv` commutes with the `S`-scalar
actions on both factors. -/
lemma linearHomComplexSingleUniversalCoefficientEquiv_linearHomComplexSingleHomologyAction
    [Small.{v} k] (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    linearHomComplexSingleUniversalCoefficientEquiv.{v} k K (ModuleCat.of k M) i
        (K.linearHomComplexSingleHomologyAction S M i s x) =
      (TauCeti.extScalarAction k S M (K.homology (1 - i)) 1 s
          (linearHomComplexSingleUniversalCoefficientEquiv.{v} k K (ModuleCat.of k M) i x).1,
        ModuleCat.ofHom
          (s • (linearHomComplexSingleUniversalCoefficientEquiv.{v} k K
            (ModuleCat.of k M) i x).2.hom)) := by
  have := SMulCommClass.symm k S M
  rw [TauCeti.extScalarAction_apply, linearHomComplexSingleHomologyAction_apply,
    linearHomComplexSingleScalarHom_def,
    linearHomComplexSingleUniversalCoefficientEquiv_coefficient_naturality,
    ModuleCat.comp_ofHom_distribSMul]

end Receiver

/-- `linearHomComplexSingleScalarHom` commutes with precomposition by a cochain map `φ : K' ⟶ K`. -/
@[reassoc]
lemma linearHomComplexPrecomp_comp_linearHomComplexSingleScalarHom
    {K' K : CochainComplex (ModuleCat.{v} k) ℤ} (φ : K' ⟶ K) (s : S) :
    TauCeti.linearHomComplexPrecomp k φ
        ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) ≫
      K'.linearHomComplexSingleScalarHom S M s =
    K.linearHomComplexSingleScalarHom S M s ≫
      TauCeti.linearHomComplexPrecomp k φ
        ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) := by
  rw [linearHomComplexSingleScalarHom_def, linearHomComplexSingleScalarHom_def]
  exact TauCeti.linearHomComplexPrecomp_postcomp_comm k φ _

end SemiringScalar

section CommRing

variable {k : Type u} [CommRing k] (K : CochainComplex (ModuleCat.{v} k) ℤ)
  (S : Type*) [Ring S]
  (M : Type v) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- Forgetting scalar actions identifies `linearHomComplex k K ((singleFunctor _ 0).obj M)` with
`K.bimoduleHomComplex S M` as cochain complexes of abelian groups. -/
def forget₂BimoduleHomComplexIso :
    ((forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v}).mapHomologicalComplex _).obj
        (linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M))) ≅
      ((forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v}).mapHomologicalComplex _).obj
        (K.bimoduleHomComplex S M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ AddEquiv.toAddCommGrpIso
      ((Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i)).toAddEquiv.trans
        ModuleCat.homAddEquiv))
    fun i j hij ↦ by
      obtain rfl : j = i + 1 := hij.symm
      ext z
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply,
        Functor.mapHomologicalComplex_obj_d, AddEquiv.toAddCommGrpIso_hom,
        AddCommGrpCat.hom_ofHom, AddEquiv.coe_toAddMonoidHom, ModuleCat.forget₂_map]
      apply (K.bimoduleHomComplexXIso S M (i + 1)).toLinearEquiv.injective
      -- Unfold `Iso.toLinearEquiv` and `AddEquiv.trans` / `ModuleCat.homAddEquiv` on the carrier
      -- `(K.bimoduleHomComplex S M).X _` to rewrite with `bimoduleHomComplex_d_apply`.
      change (K.bimoduleHomComplexXIso S M (i + 1)).hom.hom
          (((K.bimoduleHomComplex S M).d i (i + 1)).hom
            ((K.bimoduleHomComplexXIso S M i).inv.hom
              (Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel i) z).hom)) =
        (Cochain.toSingleLinearEquiv (R := k) (neg_add_cancel (i + 1))
          (((linearHomComplex k K
            ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M))).d i (i + 1)).hom z)).hom
      rw [K.bimoduleHomComplex_d_apply,
        K.toSingleLinearEquiv_linearHomComplex_d_apply (ModuleCat.of k M) k i z,
        ← LinearMap.comp_apply ((K.bimoduleHomComplexXIso S M i).hom.hom), ← ModuleCat.hom_comp,
        Iso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_apply, ModuleCat.hom_zsmul,
        ModuleCat.hom_comp]

@[simp]
lemma forget₂BimoduleHomComplexIso_hom_f_apply (i : ℤ)
    (z : Cochain K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) i) :
    (dsimp% only [Functor.mapHomologicalComplex_obj_X, linearHomComplex_X, ModuleCat.forget₂_obj]
      (K.bimoduleHomComplexXIso S M i).hom.hom
        (((K.forget₂BimoduleHomComplexIso S M).hom.f i) z)) =
      ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i) z) := by
  rfl

@[simp]
lemma forget₂BimoduleHomComplexIso_inv_f_apply (i : ℤ)
    (z : (K.bimoduleHomComplex S M).X i) :
    (dsimp% only [Functor.mapHomologicalComplex_obj_X, linearHomComplex_X, ModuleCat.forget₂_obj]
      (((K.forget₂BimoduleHomComplexIso S M).inv.f i) z)) =
      Cochain.toSingleMk (ModuleCat.ofHom ((K.bimoduleHomComplexXIso S M i).hom.hom z))
        (neg_add_cancel i) := by
  rfl

end CommRing

section CommRingScalar

variable {k : Type u} [CommRing k] (K : CochainComplex (ModuleCat.{v} k) ℤ)
  (S : Type*) [CommRing S]
  (M : Type v) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- Over a commutative ring `S`, `forget₂BimoduleHomComplexIso` intertwines
`K.linearHomComplexSingleScalarHom S M s` with scalar multiplication `s • 𝟙 _` on
`K.bimoduleHomComplex S M`. -/
@[reassoc]
lemma map_linearHomComplexSingleScalarHom_comp_forget₂BimoduleHomComplexIso_hom (s : S) :
    ((forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v}).mapHomologicalComplex _).map
        (K.linearHomComplexSingleScalarHom S M s) ≫
      (K.forget₂BimoduleHomComplexIso S M).hom =
    (K.forget₂BimoduleHomComplexIso S M).hom ≫
      ((forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v}).mapHomologicalComplex _).map
        (s • 𝟙 (K.bimoduleHomComplex S M)) := by
  ext i z
  have hinj : Function.Injective (K.bimoduleHomComplexXIso S M i).hom.hom :=
    (K.bimoduleHomComplexXIso S M i).toLinearEquiv.injective
  apply hinj
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, ModuleCat.forget₂_map,
    AddCommGrpCat.hom_ofHom, HomologicalComplex.smul_f_apply, HomologicalComplex.id_f,
    ModuleCat.hom_smul, ModuleCat.hom_id]
  -- Cross the `linearHomComplex_X` / `forget₂_obj` carrier identifications to apply the
  -- component evaluation lemmas.
  erw [K.forget₂BimoduleHomComplexIso_hom_f_apply S M i,
    K.forget₂BimoduleHomComplexIso_hom_f_apply S M i]
  exact K.toSingleEquiv_linearHomComplexSingleScalarHom_f_apply S M s i z

end CommRingScalar

end CochainComplex
