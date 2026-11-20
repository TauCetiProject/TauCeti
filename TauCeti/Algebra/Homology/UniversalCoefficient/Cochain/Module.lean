/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.ModuleCat.Ext.ScalarAction
public import TauCeti.Algebra.Homology.LinearHomComplex.Bimodule
public import TauCeti.Algebra.Homology.UniversalCoefficient.Cochain.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import TauCeti.Algebra.Category.ModuleCat.Ext.PID
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.LinearAlgebra.Dual.PID

/-!
# Bimodule equivariance and PID specializations for the cochain universal coefficient sequence

For a cochain complex `K` in `ModuleCat k` over a commutative ring `k` and a `k`-module `M`
carrying a commuting action of a semiring `S`, `TauCeti.Algebra.Homology.LinearHomComplex.Bimodule`
equips the cohomology of `CochainComplex.linearHomComplex k K ((singleFunctor _ 0).obj M)` with an
`S`-action (`CochainComplex.linearHomComplexSingleHomologyAction`), while
`TauCeti.Algebra.Category.ModuleCat.Ext.ScalarAction` equips `Ext` into `M` with an `S`-action
(`TauCeti.extScalarAction`). Both maps in the cochain universal coefficient sequence
(`CochainComplex.kronecker`, `CochainComplex.extToHomology`) and the splitting induced by a
`k`-linear cycle retraction (`CochainComplex.kroneckerSection`,
`CochainComplex.universalCoefficientEquiv`) commute with these `S`-actions
(`CochainComplex.hom_kronecker_linearHomComplexSingleHomologyAction`,
`CochainComplex.kroneckerSection_ofHom_smul`, `CochainComplex.extToHomology_extScalarAction`,
`CochainComplex.universalCoefficientEquiv_linearHomComplexSingleHomologyAction`).

Over a principal ideal domain `R` with coefficients in any torsion-free `R`-module `Y`,
`Ext¹(H¹⁻ⁱ(K), Y)` is torsion whenever `H¹⁻ⁱ(K)` is finitely generated
(`ModuleCat.isTorsion_ext_succ_of_finite`) while `H⁻ⁱ(K) →ₗ[R] Y` is torsion-free. When
`K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` splits, and `H¹⁻ⁱ(K)` is finitely generated,
the cochain universal coefficient sequence canonically identifies `Ext¹(H¹⁻ⁱ(K), Y)` with the
torsion submodule of `Hⁱ(Hom(K, Y[0]))` (`CochainComplex.range_extToHomology_eq_torsion`,
`CochainComplex.extEquivTorsion`). When `K.iCycles (-i)` also splits, it canonically identifies
`H⁻ⁱ(K) →ₗ[R] Y` with the torsion-free quotient (`CochainComplex.modTorsionEquivHom`), and for
`Y = R` equates `Module.finrank` when `H⁻ⁱ(K)` is also finitely generated
(`CochainComplex.finrank_homology_linearHomComplex_singleFunctor_obj`).
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
  (S : Type*) [Semiring S]
  (M : Type v) [AddCommGroup M] [Module k M] [Module S M] [SMulCommClass k S M]

/-- Postcomposition with scalar multiplication by `s : S` multiplies a `k`-linear map into `M`
by `s`. -/
private lemma comp_ofHom_distribSMul [SMulCommClass S k M] {A : ModuleCat.{v} k}
    (f : A ⟶ ModuleCat.of k M) (s : S) :
    f ≫ ModuleCat.ofHom (DistribSMul.toLinearMap k M s) = ModuleCat.ofHom (s • f.hom) := by
  ext x
  simp [ModuleCat.hom_comp, DistribSMul.toLinearMap]

/-- `CochainComplex.kronecker` commutes with the `S`-scalar actions on cohomology and on
`K.homology (-i) →ₗ[k] M`. -/
lemma hom_kronecker_linearHomComplexSingleHomologyAction (i : ℤ) (s : S)
    (x : (linearHomComplex k K ((singleFunctor (ModuleCat.{v} k) 0).obj
      (ModuleCat.of k M))).homology i) :
    (K.kronecker k (ModuleCat.of k M) i
        (K.linearHomComplexSingleHomologyAction S M i s x)).hom =
      s • (K.kronecker k (ModuleCat.of k M) i x).hom := by
  have := SMulCommClass.symm k S M
  rw [linearHomComplexSingleHomologyAction_apply, linearHomComplexSingleScalarHom_def,
    kronecker_coefficient_naturality, comp_ofHom_distribSMul, ModuleCat.hom_ofHom]

/-- For a fixed `k`-linear retraction of `K.iCycles (-i)`, `CochainComplex.kroneckerSection`
commutes with the `S`-scalar action. -/
lemma kroneckerSection_ofHom_smul (i : ℤ) [IsSplitMono (K.iCycles (-i))] (s : S)
    (f : K.homology (-i) →ₗ[k] M) :
    K.kroneckerSection k (ModuleCat.of k M) i (ModuleCat.ofHom (s • f)) =
      K.linearHomComplexSingleHomologyAction S M i s
        (K.kroneckerSection k (ModuleCat.of k M) i (ModuleCat.ofHom f)) := by
  have := SMulCommClass.symm k S M
  let g : K.homology (-i) ⟶ ModuleCat.of k M := ModuleCat.ofHom f
  rw [linearHomComplexSingleHomologyAction_apply, linearHomComplexSingleScalarHom_def]
  exact ((kroneckerSection_coefficient_naturality (K := K) (k := k)
    (ModuleCat.ofHom (DistribSMul.toLinearMap k M s)) i g).trans
    (congrArg (K.kroneckerSection k (ModuleCat.of k M) i)
      (comp_ofHom_distribSMul (k := k) (S := S) (M := M) g s))).symm

/-- `CochainComplex.extToHomology` commutes with the `S`-scalar actions on `Ext¹` and on the
cohomology of `linearHomComplex`. -/
lemma extToHomology_extScalarAction [Small.{v} k] (i : ℤ) [Projective (K.cycles (1 - i))]
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
lemma universalCoefficientEquiv_linearHomComplexSingleHomologyAction [Small.{v} k] (i : ℤ)
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
    linearHomComplexSingleScalarHom_def, universalCoefficientEquiv_coefficient_naturality,
    comp_ofHom_distribSMul]

end BimoduleCoefficients

section PrincipalIdealDomain

section TorsionFree

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Small.{v} R]
  (K : CochainComplex (ModuleCat.{v} R) ℤ) (Y : ModuleCat.{v} R) [Module.IsTorsionFree R Y]

/-- Over a principal ideal domain, for any torsion-free coefficient module `Y`, when
`K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` splits, and `H¹⁻ⁱ(K)` is finitely generated,
the image of `extToHomology` in `Hⁱ(Hom(K, Y[0]))` is its torsion submodule. -/
@[simp]
theorem range_extToHomology_eq_torsion (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    LinearMap.range (extToHomology.{v} K R Y i) =
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) := by
  have htor := ModuleCat.isTorsion_ext_succ_of_finite (K.homology (1 - i)) Y 0
  have hex := exact_extToHomology_kronecker.{v} (K := K) (k := R) (Y := Y) i
  refine le_antisymm ?_ ?_
  · rw [LinearMap.range_eq_map, Submodule.map_le_iff_le_comap,
      ← (Submodule.isTorsion'_iff_torsion'_eq_top R⁰).mp htor]
    exact (extToHomology.{v} K R Y i).le_comap_torsion
  · have hbot : Submodule.torsion R (K.homology (-i) →ₗ[R] Y) = ⊥ :=
      Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
    have hle := ((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
      K.kronecker R Y i).le_comap_torsion
    rw [hbot, ← LinearMap.ker, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
      hex.linearMap_ker_eq] at hle
    exact hle

/-- **Canonical torsion identification for the cochain complex over a PID**: for any torsion-free
coefficient module `Y`, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` splits, and
`H¹⁻ⁱ(K)` is finitely generated, `extToHomology` restricts to a canonical `R`-linear equivalence
`Ext¹(H¹⁻ⁱ(K), Y) ≃ₗ[R] torsion R (Hⁱ(Hom(K, Y[0])))`. -/
def extEquivTorsion (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    Ext.{v} (K.homology (1 - i)) Y 1 ≃ₗ[R]
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) :=
  (LinearEquiv.ofInjective (extToHomology.{v} K R Y i)
    (extToHomology_injective i)).trans
    (LinearEquiv.ofEq _ _ (K.range_extToHomology_eq_torsion Y i))

@[simp]
lemma coe_extEquivTorsion_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))]
    (e : Ext.{v} (K.homology (1 - i)) Y 1) :
    (K.extEquivTorsion Y i e :
      (linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) =
      extToHomology.{v} K R Y i e := by
  simp [extEquivTorsion]

private lemma ker_homLinearEquiv_comp_kronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    LinearMap.ker ((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
        K.kronecker R Y i) =
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) := by
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
    (exact_extToHomology_kronecker.{v} (K := K) (k := R) (Y := Y) i).linearMap_ker_eq,
    range_extToHomology_eq_torsion]

/-- **Canonical torsion-free quotient identification over a PID**: for any torsion-free
coefficient module `Y`, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` and
`K.iCycles (-i)` split, and `H¹⁻ⁱ(K)` is finitely generated, the Kronecker map descends to a
canonical `R`-linear equivalence `Hⁱ(Hom(K, Y[0])) ⧸ torsion ≃ₗ[R] (H⁻ⁱ(K) →ₗ[R] Y)`. -/
def modTorsionEquivHom (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] [Module.Finite R (K.homology (1 - i))] :
    ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i ⧸
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i)) ≃ₗ[R]
      (K.homology (-i) →ₗ[R] Y) :=
  (Submodule.quotEquivOfEq _ _ (K.ker_homLinearEquiv_comp_kronecker Y i).symm).trans
    (((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
        K.kronecker R Y i).quotKerEquivOfSurjective
      ((ModuleCat.homLinearEquiv (R := R) (S := R)).surjective.comp
        (kronecker_surjective_of_isSplitMono i)))

@[simp]
lemma modTorsionEquivHom_mk (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] [Module.Finite R (K.homology (1 - i))]
    (x : (linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) :
    K.modTorsionEquivHom Y i (Submodule.Quotient.mk x) = (K.kronecker R Y i x).hom := by
  simp [modTorsionEquivHom]
  rfl

end TorsionFree

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Over a principal ideal domain, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` and
`K.iCycles (-i)` split, and `H¹⁻ⁱ(K)` and `H⁻ⁱ(K)` are finitely generated, `Hⁱ(Hom(K, R[0]))` and
`H⁻ⁱ(K)` have the same `finrank`. -/
theorem finrank_homology_linearHomComplex_singleFunctor_obj (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    [Module.Finite R (K.homology (1 - i))] [Module.Finite R (K.homology (-i))] :
    Module.finrank R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) =
      Module.finrank R (K.homology (-i)) :=
  (finrank_quotient_eq_of_le_torsion le_rfl).symm.trans
    ((K.modTorsionEquivHom (ModuleCat.of R R) i).finrank_eq.trans
      (TauCeti.Module.dual_finrank_eq_of_isPrincipalIdealRing R (K.homology (-i))))

end PrincipalIdealDomain

end CochainComplex
