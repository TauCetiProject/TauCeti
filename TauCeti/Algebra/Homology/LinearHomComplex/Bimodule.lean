/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.Single

/-!
# Bimodule Hom complexes and commuting scalar actions on cohomology

Let `K` be a cochain complex in `ModuleCat k` and let `M` be a `k`-module carrying a commuting
action of a ring `S` (`[SMulCommClass k S M]`). Over any rings `k` and `S`, the degreewise
`S`-modules `K.X (-i) →ₗ[k] M` with signed precomposition differential
`f ↦ (-1) ^ (i + 1) • (f ∘ₗ K.d (-j) (-i))` assemble into the `(k, S)`-bimodule Hom cochain
complex `CochainComplex.bimoduleHomComplex` in `ModuleCat S`.

When `k` is commutative, scalar multiplication by `s : S` on `M` is a `k`-linear endomorphism of
`M`, so postcomposition via `TauCeti.linearHomComplexPostcomp` defines a cochain endomorphism
`CochainComplex.linearHomComplexSingleScalarHom` of
`CochainComplex.linearHomComplex k K ((singleFunctor _ 0).obj (ModuleCat.of k M))` and induces a
ring homomorphism `CochainComplex.linearHomComplexSingleHomologyAction` into the `k`-linear
endomorphism ring of its cohomology. Forgetting scalar actions identifies `linearHomComplex` into
`M` placed in degree `0` with `bimoduleHomComplex` as cochain complexes of abelian groups
(`CochainComplex.forget₂BimoduleHomComplexIso`), intertwining `linearHomComplexSingleScalarHom`
with `s • 𝟙 _` when `S` is commutative
(`CochainComplex.map_linearHomComplexSingleScalarHom_comp_forget₂BimoduleHomComplexIso`).

## Main definitions

* `CochainComplex.bimoduleHomComplex` and `CochainComplex.bimoduleHomComplexXIso`: the cochain
  complex `i ↦ (K.X (-i) →ₗ[k] M)` in `ModuleCat S` and its degreewise carrier identification.
* `CochainComplex.linearHomComplexSingleScalarHom` and
  `CochainComplex.linearHomComplexSingleHomologyAction`: the cochain endomorphism and cohomology
  ring action induced by a commuting scalar action on `M`.
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

open CategoryTheory Limits HomologicalComplex
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
lemma bimoduleHomComplex_d_apply (i : ℤ) (f : K.X (-i) →ₗ[k] M) :
    (K.bimoduleHomComplexXIso S M (i + 1)).hom.hom
      (((K.bimoduleHomComplex S M).d i (i + 1)).hom
        ((K.bimoduleHomComplexXIso S M i).inv.hom f)) =
      ((i + 1).negOnePow : ℤ) • f.comp (K.d (-(i + 1)) (-i)).hom := by
  rfl

end Ring

section CommRing

variable {k : Type u} [CommRing k]

/-- Scalar multiplication by `s : S` on `M` as a `k`-linear endomorphism of `ModuleCat.of k M`. -/
private def coeffScalarHom (S : Type*) [Ring S] (M : Type v) [AddCommGroup M]
    [Module k M] [Module S M] [SMulCommClass k S M] (s : S) :
    ModuleCat.of k M ⟶ ModuleCat.of k M :=
  have := SMulCommClass.symm k S M
  ModuleCat.ofHom (DistribSMul.toLinearMap k M s)

variable (K : CochainComplex (ModuleCat.{v} k) ℤ) (S : Type*) [Ring S]
  (M : Type v) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- Scalar multiplication by `s : S` on `M` as a cochain endomorphism of
`linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M))`, defined via
`TauCeti.linearHomComplexPostcomp`. -/
def linearHomComplexSingleScalarHom (s : S) :
    linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) ⟶
      linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) :=
  TauCeti.linearHomComplexPostcomp k K
    ((singleFunctor (ModuleCat.{v} k) 0).map (coeffScalarHom S M s))

/-- `CochainComplex.linearHomComplexSingleScalarHom` is postcomposition on `linearHomComplex` by
scalar multiplication on `M` placed in degree `0`. -/
lemma linearHomComplexSingleScalarHom_def (s : S) :
    have := SMulCommClass.symm k S M
    K.linearHomComplexSingleScalarHom S M s =
      TauCeti.linearHomComplexPostcomp k K
        ((singleFunctor (ModuleCat.{v} k) 0).map
          (ModuleCat.ofHom (DistribSMul.toLinearMap k M s))) := by
  rfl

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
  rw [linearHomComplexSingleScalarHom]
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
        ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M))).homology i) where
  toFun s := (homologyMap (K.linearHomComplexSingleScalarHom S M s) i).hom
  map_one' := by
    have h1 : coeffScalarHom (k := k) S M 1 = 𝟙 _ := by ext m; exact one_smul S m
    ext x
    simp [linearHomComplexSingleScalarHom, h1]
  map_mul' r s := by
    -- In `Module.End`, `(f * g) x = f (g x)`, matching `s ≫ r` in `ModuleCat`.
    have hmul : coeffScalarHom (k := k) S M (r * s) =
        coeffScalarHom S M s ≫ coeffScalarHom S M r := by
      ext m
      exact mul_smul r s m
    ext x
    simp [linearHomComplexSingleScalarHom, hmul, TauCeti.linearHomComplexPostcomp_comp,
      homologyMap_comp]
  map_zero' := by
    have h0 : K.linearHomComplexSingleScalarHom S M 0 = 0 := by
      have hc : coeffScalarHom (k := k) S M 0 = 0 := by ext m; exact zero_smul S m
      ext j z
      obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-j) (neg_add_cancel j)
      rw [linearHomComplexSingleScalarHom, HomologicalComplex.zero_f_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply]
      -- `linearHomComplexPostcomp_f_apply` is stated on the unfolded carrier `Cochain K _ j`.
      erw [TauCeti.linearHomComplexPostcomp_f_apply]
      rw [← Cochain.toSingleMk_postcomp, hc, comp_zero, Cochain.toSingleMk_zero]
    ext x
    simp [h0]
  map_add' r s := by
    have hadd : K.linearHomComplexSingleScalarHom S M (r + s) =
        K.linearHomComplexSingleScalarHom S M r + K.linearHomComplexSingleScalarHom S M s := by
      have hc : coeffScalarHom (k := k) S M (r + s) =
          coeffScalarHom S M r + coeffScalarHom S M s := by
        ext m
        exact add_smul r s m
      ext j z
      obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective z (-j) (neg_add_cancel j)
      simp only [linearHomComplexSingleScalarHom, HomologicalComplex.add_f_apply,
        ModuleCat.hom_add, LinearMap.add_apply]
      -- `linearHomComplexPostcomp_f_apply` is stated on the unfolded carrier `Cochain K _ j`.
      erw [TauCeti.linearHomComplexPostcomp_f_apply, TauCeti.linearHomComplexPostcomp_f_apply,
        TauCeti.linearHomComplexPostcomp_f_apply]
      rw [← Cochain.toSingleMk_postcomp, ← Cochain.toSingleMk_postcomp,
        ← Cochain.toSingleMk_postcomp, hc, Preadditive.comp_add, Cochain.toSingleMk_add]
    ext x
    simp [hadd, homologyMap_add]

@[simp]
lemma linearHomComplexSingleHomologyAction_apply (i : ℤ) (s : S)
    (x : (linearHomComplex k K
      ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M))).homology i) :
    K.linearHomComplexSingleHomologyAction S M i s x =
      homologyMap (K.linearHomComplexSingleScalarHom S M s) i x := by
  simp [linearHomComplexSingleHomologyAction]

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
      apply LinearMap.ext
      intro x
      have h := congrArg (fun φ ↦ ModuleCat.Hom.hom φ x)
        (K.toSingleLinearEquiv_linearHomComplex_d_apply k (ModuleCat.of k M) i z).symm
      rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
        Cochain.toSingleLinearEquiv_apply, Cochain.toSingleLinearEquiv_apply] at h
      exact h

@[simp]
lemma forget₂BimoduleHomComplexIso_hom_f_apply (i : ℤ)
    (z : Cochain K ((singleFunctor (ModuleCat.{v} k) 0).obj (ModuleCat.of k M)) i) :
    (dsimp% only [Functor.mapHomologicalComplex_obj_X, linearHomComplex_X, ModuleCat.forget₂_obj]
      (K.bimoduleHomComplexXIso S M i).hom.hom
        (((K.forget₂BimoduleHomComplexIso S M).hom.f i) z)) =
      ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i) z) := by
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
lemma map_linearHomComplexSingleScalarHom_comp_forget₂BimoduleHomComplexIso (s : S) :
    ((forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v}).mapHomologicalComplex _).map
        (K.linearHomComplexSingleScalarHom S M s) ≫
      (K.forget₂BimoduleHomComplexIso S M).hom =
    (K.forget₂BimoduleHomComplexIso S M).hom ≫
      ((forget₂ (ModuleCat.{v} S) AddCommGrpCat.{v}).mapHomologicalComplex _).map
        (s • 𝟙 (K.bimoduleHomComplex S M)) := by
  ext i z
  exact K.toSingleEquiv_linearHomComplexSingleScalarHom_f_apply S M s i z

end CommRingScalar

end CochainComplex
