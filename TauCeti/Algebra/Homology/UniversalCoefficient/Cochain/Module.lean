/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.Algebra.Category.ModuleCat.Ext.ScalarAction
public import TauCeti.Algebra.Homology.PrincipalIdealRing
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import TauCeti.Algebra.Category.ModuleCat.Ext.PID
import TauCeti.LinearAlgebra.Dual.PID

/-!
# Bimodule coefficients and PID specializations for the cochain universal coefficient sequence

For a cochain complex `K` in `ModuleCat k` and a module `M` carrying a ring action of `S` commuting
with `k`, scalar multiplication on `M` acts on `CochainComplex.linearHomComplex` via
`TauCeti.linearHomComplexPostcomp` (`CochainComplex.linearHomComplexSingleScalarHom`,
`CochainComplex.linearHomComplexSingleHomologyAction`) and on `Ext` via
`CategoryTheory.Abelian.Ext.postcompOfLinear` (`TauCeti.extScalarAction`), lifting `Hom_k(K, M)` to
a cochain complex `CochainComplex.bimoduleHomComplex` in `ModuleCat S`. Both maps in the cochain
universal coefficient sequence and the splitting induced by `k`-linear cycle retractions preserve
the `S`-action.

Over a principal ideal domain `R` with coefficients in `R`, `Ext¹(H¹⁻ⁱ(K), R)` is torsion whenever
`H¹⁻ⁱ(K)` is finitely generated (`ModuleCat.isTorsion_ext_succ_of_finite`) while
`Module.Dual R (H⁻ⁱ(K))` is torsion-free. When `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)`
splits, and `H¹⁻ⁱ(K)` is finitely generated, the cochain universal coefficient sequence canonically
identifies `Ext¹(H¹⁻ⁱ(K), R)` with the torsion submodule of `Hⁱ(Hom(K, R[0]))`
(`CochainComplex.extEquivTorsion`). When `K.iCycles (-i)` also splits, it canonically identifies
`Module.Dual R (H⁻ⁱ(K))` with the torsion-free quotient (`CochainComplex.modTorsionEquivDual`), and
equates `Module.finrank` when `H⁻ⁱ(K)` is also finitely generated
(`CochainComplex.finrank_homology_linearHomComplex_single₀`).
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian
open CochainComplex CochainComplex.HomComplex
open scoped nonZeroDivisors

universe u

namespace CochainComplex

section BimoduleCoefficients

section Ring

variable {k : Type u} [Ring k] (K : CochainComplex (ModuleCat.{u} k) ℤ)
  (S : Type*) [Ring S]
  (M : Type u) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- **The `(k, S)`-bimodule Hom cochain complex** in `ModuleCat S`: in degree `i` it is the
`S`-module `K.X (-i) →ₗ[k] M`, with differential `f ↦ (-1) ^ (i + 1) • (f ∘ₗ K.d (-j) (-i))`. -/
def bimoduleHomComplex : CochainComplex (ModuleCat.{u} S) ℤ where
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
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.smul_apply, HomologicalComplex.d_comp_d_apply, map_zero, smul_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply]

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
private def coeffScalarHom (S : Type*) [Ring S] (M : Type u) [AddCommGroup M]
    [Module k M] [Module S M] [SMulCommClass k S M] (s : S) :
    ModuleCat.of k M ⟶ ModuleCat.of k M :=
  have := SMulCommClass.symm k S M
  ModuleCat.ofHom (DistribSMul.toLinearMap k M s)

variable (K : CochainComplex (ModuleCat.{u} k) ℤ) (S : Type*) [Ring S]
  (M : Type u) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- Scalar multiplication by `s : S` on `M` as a cochain endomorphism of
`linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M))`, defined via
`TauCeti.linearHomComplexPostcomp`. -/
def linearHomComplexSingleScalarHom (s : S) :
    linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M)) ⟶
      linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M)) :=
  TauCeti.linearHomComplexPostcomp k K
    ((singleFunctor (ModuleCat.{u} k) 0).map (coeffScalarHom S M s))

/-- Under `Cochain.toSingleEquiv (neg_add_cancel i)`, `linearHomComplexSingleScalarHom` acts
pointwise as `s • f` on `K.X (-i) →ₗ[k] M`. -/
@[simp]
lemma toSingleEquiv_linearHomComplexSingleScalarHom_f_apply (s : S) (i : ℤ)
    (z : Cochain K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M)) i) :
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
        ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M))).homology i) where
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
      ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M))).homology i) :
    K.linearHomComplexSingleHomologyAction S M i s x =
      homologyMap (K.linearHomComplexSingleScalarHom S M s) i x := by
  simp [linearHomComplexSingleHomologyAction]

/-- Forgetting scalar actions identifies `linearHomComplex k K ((singleFunctor _ 0).obj M)` with
`K.bimoduleHomComplex S M` as cochain complexes of abelian groups. -/
def forget₂BimoduleHomComplexIso :
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
        (linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M))) ≅
      ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex _).obj
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
    (z : Cochain K ((singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k M)) i) :
    (dsimp% only [Functor.mapHomologicalComplex_obj_X, linearHomComplex_X, ModuleCat.forget₂_obj]
      (K.bimoduleHomComplexXIso S M i).hom.hom
        (((K.forget₂BimoduleHomComplexIso S M).hom.f i) z)) =
      ModuleCat.Hom.hom (Cochain.toSingleEquiv (neg_add_cancel i) z) := by
  rfl

/-- `CochainComplex.kronecker` commutes with the `S`-scalar actions on cohomology and on
`K.homology (-i) →ₗ[k] M`. -/
lemma kronecker_scalar (i : ℤ) (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    (K.kronecker k (ModuleCat.of k M) i
        (K.linearHomComplexSingleHomologyAction S M i s x)).hom =
      s • (K.kronecker k (ModuleCat.of k M) i x).hom := by
  rw [linearHomComplexSingleHomologyAction_apply, linearHomComplexSingleScalarHom,
    kronecker_coefficient_naturality]
  rfl

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`, `CochainComplex.kroneckerSection`
commutes with the `S`-scalar action. -/
lemma kroneckerSection_scalar (i : ℤ) [IsSplitMono (K.iCycles (-i))] (s : S)
    (f : K.homology (-i) →ₗ[k] M) :
    K.kroneckerSection k (ModuleCat.of k M) i (ModuleCat.ofHom (s • f)) =
      K.linearHomComplexSingleHomologyAction S M i s
        (K.kroneckerSection k (ModuleCat.of k M) i (ModuleCat.ofHom f)) :=
  (kroneckerSection_coefficient_naturality (coeffScalarHom S M s) i (ModuleCat.ofHom f)).symm

/-- `CochainComplex.extToHomology` commutes with the `S`-scalar actions on `Ext¹` and on the
cohomology of `linearHomComplex`. -/
lemma extToHomology_scalar (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] (s : S)
    (e : Ext.{u} (K.homology (1 - i)) (ModuleCat.of k M) 1) :
    extToHomology.{u} K k (ModuleCat.of k M) i
        (TauCeti.extScalarAction k S M (K.homology (1 - i)) 1 s e) =
      K.linearHomComplexSingleHomologyAction S M i s
        (extToHomology.{u} K k (ModuleCat.of k M) i e) := by
  have := SMulCommClass.symm k S M
  rw [TauCeti.extScalarAction_apply]
  exact extToHomology_coefficient_naturality (coeffScalarHom S M s) i e

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`, the universal coefficient splitting
`CochainComplex.universalCoefficientEquiv` commutes with the `S`-scalar actions on both factors. -/
lemma universalCoefficientEquiv_scalar (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{u} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    universalCoefficientEquiv.{u} K k (ModuleCat.of k M) i
        (K.linearHomComplexSingleHomologyAction S M i s x) =
      (TauCeti.extScalarAction k S M (K.homology (1 - i)) 1 s
          (universalCoefficientEquiv.{u} K k (ModuleCat.of k M) i x).1,
        ModuleCat.ofHom
          (s • (universalCoefficientEquiv.{u} K k (ModuleCat.of k M) i x).2.hom)) := by
  have := SMulCommClass.symm k S M
  rw [TauCeti.extScalarAction_apply]
  exact universalCoefficientEquiv_coefficient_naturality (coeffScalarHom S M s) i x

end CommRing

section CommRingScalar

variable {k : Type u} [CommRing k] (K : CochainComplex (ModuleCat.{u} k) ℤ)
  (S : Type*) [CommRing S]
  (M : Type u) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- Over a commutative ring `S`, `forget₂BimoduleHomComplexIso` intertwines
`K.linearHomComplexSingleScalarHom S M s` with scalar multiplication `s • 𝟙 _` on
`K.bimoduleHomComplex S M`. -/
@[reassoc]
lemma map_linearHomComplexSingleScalarHom_comp_forget₂BimoduleHomComplexIso (s : S) :
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (K.linearHomComplexSingleScalarHom S M s) ≫
      (K.forget₂BimoduleHomComplexIso S M).hom =
    (K.forget₂BimoduleHomComplexIso S M).hom ≫
      ((forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}).mapHomologicalComplex _).map
        (s • 𝟙 (K.bimoduleHomComplex S M)) := by
  ext i z
  exact K.toSingleEquiv_linearHomComplexSingleScalarHom_f_apply S M s i z

end CommRingScalar

end BimoduleCoefficients

section PrincipalIdealDomain

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Over a principal ideal domain, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)`
splits, and `H¹⁻ⁱ(K)` is finitely generated, the image of `extToHomology` in `Hⁱ(Hom(K, R[0]))` is
its torsion submodule. -/
theorem range_extToHomology_eq_torsion (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    LinearMap.range (extToHomology.{u} K R (ModuleCat.of R R) i) =
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) := by
  have htor := ModuleCat.isTorsion_ext_succ_of_finite (K.homology (1 - i)) (ModuleCat.of R R) 0
  have hex := exact_extToHomology_kronecker.{u} (K := K) (k := R) (Y := ModuleCat.of R R) i
  refine le_antisymm ?_ ?_
  · rintro _ ⟨e, rfl⟩
    obtain ⟨r, hr⟩ := @htor e
    exact ⟨r, by rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, hr, map_zero]⟩
  · intro x ⟨r, hr⟩
    refine (hex x).1 ?_
    ext y
    have h0 : (r : R) • (K.kronecker R (ModuleCat.of R R) i x).hom y = 0 := by
      rw [← LinearMap.smul_apply, ← ModuleCat.hom_smul, ← map_smul, ← Submonoid.smul_def, hr,
        map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact (smul_eq_zero.1 h0).resolve_left (nonZeroDivisors.coe_ne_zero r)

/-- **Canonical torsion identification for the dual cochain complex over a PID**: `extToHomology`
restricts to a canonical `R`-linear equivalence
`Ext¹(H¹⁻ⁱ(K), R) ≃ₗ[R] torsion R (Hⁱ(Hom(K, R[0])))`. -/
def extEquivTorsion (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    Ext.{u} (K.homology (1 - i)) (ModuleCat.of R R) 1 ≃ₗ[R]
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) :=
  (LinearEquiv.ofInjective (extToHomology.{u} K R (ModuleCat.of R R) i)
    (extToHomology_injective i)).trans
    (LinearEquiv.ofEq _ _ (K.range_extToHomology_eq_torsion i))

@[simp]
lemma coe_extEquivTorsion_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))]
    (e : Ext.{u} (K.homology (1 - i)) (ModuleCat.of R R) 1) :
    (K.extEquivTorsion i e :
      (linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).homology i) =
      extToHomology.{u} K R (ModuleCat.of R R) i e := by
  simp [extEquivTorsion]

private lemma ker_homLinearEquiv_comp_kronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    LinearMap.ker ((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
        K.kronecker R (ModuleCat.of R R) i) =
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) := by
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
    (exact_extToHomology_kronecker.{u} (K := K) (k := R)
      (Y := ModuleCat.of R R) i).linearMap_ker_eq,
    range_extToHomology_eq_torsion]

/-- **Canonical torsion-free quotient identification for the dual cochain complex over a PID**:
the Kronecker map descends to a canonical `R`-linear equivalence
`Hⁱ(Hom(K, R[0])) ⧸ torsion ≃ₗ[R] Module.Dual R (H⁻ⁱ(K))`. -/
def modTorsionEquivDual (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] [Module.Finite R (K.homology (1 - i))] :
    ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R R))).homology i ⧸
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i)) ≃ₗ[R]
      Module.Dual R (K.homology (-i)) :=
  (Submodule.quotEquivOfEq _ _ (K.ker_homLinearEquiv_comp_kronecker i).symm).trans
    (((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
        K.kronecker R (ModuleCat.of R R) i).quotKerEquivOfSurjective
      ((ModuleCat.homLinearEquiv (R := R) (S := R)).surjective.comp
        (kronecker_surjective_of_isSplitMono i)))

@[simp]
lemma modTorsionEquivDual_mk (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] [Module.Finite R (K.homology (1 - i))]
    (x : (linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))).homology i) :
    K.modTorsionEquivDual i (Submodule.Quotient.mk x) =
      (K.kronecker R (ModuleCat.of R R) i x).hom := by
  simp [modTorsionEquivDual]
  rfl

/-- Over a principal ideal domain, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` and
`K.iCycles (-i)` split, and `H¹⁻ⁱ(K)` and `H⁻ⁱ(K)` are finitely generated, `Hⁱ(Hom(K, R[0]))` and
`H⁻ⁱ(K)` have the same `finrank`. -/
theorem finrank_homology_linearHomComplex_single₀ (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    [Module.Finite R (K.homology (1 - i))] [Module.Finite R (K.homology (-i))] :
    Module.finrank R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) =
      Module.finrank R (K.homology (-i)) :=
  (finrank_quotient_eq_of_le_torsion le_rfl).symm.trans
    ((K.modTorsionEquivDual i).finrank_eq.trans
      (TauCeti.Module.dual_finrank_eq_of_isPrincipalIdealRing R (K.homology (-i))))

end PrincipalIdealDomain

end CochainComplex
