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
public import TauCeti.Algebra.Homology.LinearHomComplex.Bimodule
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import TauCeti.Algebra.Category.ModuleCat.Ext.PID
import TauCeti.LinearAlgebra.Dual.PID

/-!
# Bimodule equivariance and PID specializations for the cochain universal coefficient sequence

For a cochain complex `K` in `ModuleCat k` over a commutative ring `k` and a `k`-module `M`
carrying a commuting action of a ring `S`, `TauCeti.Algebra.Homology.LinearHomComplex.Bimodule`
equips the cohomology of `CochainComplex.linearHomComplex k K ((singleFunctor _ 0).obj M)` with an
`S`-action (`CochainComplex.linearHomComplexSingleHomologyAction`), while
`TauCeti.Algebra.Category.ModuleCat.Ext.ScalarAction` equips `Ext` into `M` with an `S`-action
(`TauCeti.extScalarAction`). Both maps in the cochain universal coefficient sequence
(`CochainComplex.kronecker`, `CochainComplex.extToHomology`) and the splitting induced by a
`k`-linear cycle retraction (`CochainComplex.kroneckerSection`,
`CochainComplex.universalCoefficientEquiv`) commute with these `S`-actions.

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

universe v u

namespace CochainComplex

section BimoduleCoefficients

variable {k : Type u} [CommRing k] (K : CochainComplex (ModuleCat.{v} k) ℤ)
  (S : Type*) [Ring S]
  (M : Type v) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- `CochainComplex.kronecker` commutes with the `S`-scalar actions on cohomology and on
`K.homology (-i) →ₗ[k] M`. -/
lemma kronecker_scalar (i : ℤ) (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    (K.kronecker k (ModuleCat.of k M) i
        (K.linearHomComplexSingleHomologyAction S M i s x)).hom =
      s • (K.kronecker k (ModuleCat.of k M) i x).hom := by
  have := SMulCommClass.symm k S M
  rw [linearHomComplexSingleHomologyAction_apply, linearHomComplexSingleScalarHom_def,
    kronecker_coefficient_naturality]
  rfl

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`, `CochainComplex.kroneckerSection`
commutes with the `S`-scalar action. -/
lemma kroneckerSection_scalar (i : ℤ) [IsSplitMono (K.iCycles (-i))] (s : S)
    (f : K.homology (-i) →ₗ[k] M) :
    K.kroneckerSection k (ModuleCat.of k M) i (ModuleCat.ofHom (s • f)) =
      K.linearHomComplexSingleHomologyAction S M i s
        (K.kroneckerSection k (ModuleCat.of k M) i (ModuleCat.ofHom f)) := by
  have := SMulCommClass.symm k S M
  have hf : (ModuleCat.ofHom (s • f) : K.homology (-i) ⟶ ModuleCat.of k M) =
      ModuleCat.ofHom f ≫ ModuleCat.ofHom (DistribSMul.toLinearMap k M s) := by
    ext x
    rfl
  rw [hf, linearHomComplexSingleHomologyAction_apply, linearHomComplexSingleScalarHom_def]
  exact (kroneckerSection_coefficient_naturality
    (ModuleCat.ofHom (DistribSMul.toLinearMap k M s)) i (ModuleCat.ofHom f)).symm

/-- `CochainComplex.extToHomology` commutes with the `S`-scalar actions on `Ext¹` and on the
cohomology of `linearHomComplex`. -/
lemma extToHomology_scalar [Small.{v} k] (i : ℤ) [Projective (K.cycles (1 - i))]
    [IsSplitMono (K.iCycles (1 - i))] (s : S)
    (e : Ext.{v} (K.homology (1 - i)) (ModuleCat.of k M) 1) :
    extToHomology.{v} K k (ModuleCat.of k M) i
        (TauCeti.extScalarAction k S M (K.homology (1 - i)) 1 s e) =
      K.linearHomComplexSingleHomologyAction S M i s
        (extToHomology.{v} K k (ModuleCat.of k M) i e) := by
  have := SMulCommClass.symm k S M
  rw [TauCeti.extScalarAction_apply, linearHomComplexSingleHomologyAction_apply,
    linearHomComplexSingleScalarHom_def]
  exact extToHomology_coefficient_naturality
    (ModuleCat.ofHom (DistribSMul.toLinearMap k M s)) i e

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`, the universal coefficient splitting
`CochainComplex.universalCoefficientEquiv` commutes with the `S`-scalar actions on both factors. -/
lemma universalCoefficientEquiv_scalar [Small.{v} k] (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    universalCoefficientEquiv.{v} K k (ModuleCat.of k M) i
        (K.linearHomComplexSingleHomologyAction S M i s x) =
      (TauCeti.extScalarAction k S M (K.homology (1 - i)) 1 s
          (universalCoefficientEquiv.{v} K k (ModuleCat.of k M) i x).1,
        ModuleCat.ofHom
          (s • (universalCoefficientEquiv.{v} K k (ModuleCat.of k M) i x).2.hom)) := by
  have := SMulCommClass.symm k S M
  rw [TauCeti.extScalarAction_apply, linearHomComplexSingleHomologyAction_apply,
    linearHomComplexSingleScalarHom_def]
  exact universalCoefficientEquiv_coefficient_naturality
    (ModuleCat.ofHom (DistribSMul.toLinearMap k M s)) i x

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

/-- **Canonical torsion identification for the dual cochain complex over a PID**: when
`K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` splits, and `H¹⁻ⁱ(K)` is finitely generated,
`extToHomology` restricts to a canonical `R`-linear equivalence
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
when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` and `K.iCycles (-i)` split, and
`H¹⁻ⁱ(K)` is finitely generated, the Kronecker map descends to a canonical `R`-linear equivalence
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
