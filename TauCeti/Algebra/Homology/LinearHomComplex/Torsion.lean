/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Homology.LinearHomComplex.Single
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import TauCeti.Algebra.Category.ModuleCat.Ext.PID
import TauCeti.Algebra.Module.Torsion.Basic
import TauCeti.LinearAlgebra.Dual.PID

/-!
# Torsion and free rank of Hom complexes over principal ideal domains

Let `R` be a principal ideal domain, `K` a cochain complex of `R`-modules indexed by `ℤ`, and `Y` a
torsion-free `R`-module. Whenever `H¹⁻ⁱ(K)` is finitely generated, `Ext¹(H¹⁻ⁱ(K), Y)` is a torsion
`R`-module (`ModuleCat.isTorsion_ext_succ_of_finite`), while `H⁻ⁱ(K) →ₗ[R] Y` is torsion-free.

When `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` splits, and `H¹⁻ⁱ(K)` is finitely
generated, the universal coefficient sequence of `Hom(K, Y[0])`
(`TauCeti.Algebra.Homology.LinearHomComplex.Single`) canonically identifies `Ext¹(H¹⁻ⁱ(K), Y)` with
the torsion submodule of `Hⁱ(Hom(K, Y[0]))`
(`CochainComplex.range_linearHomComplexSingleExtToHomology_eq_torsion`,
`CochainComplex.linearHomComplexSingleExtEquivTorsion`). When `K.iCycles (-i)` also splits, the
Kronecker map descends to a canonical `R`-linear equivalence between the torsion-free quotient of
`Hⁱ(Hom(K, Y[0]))` and `H⁻ⁱ(K) →ₗ[R] Y` (`CochainComplex.linearHomComplexSingleModTorsionEquivHom`).
For `Y = R`, when `H⁻ⁱ(K)` is also finitely generated, `Hⁱ(Hom(K, R[0]))` and `H⁻ⁱ(K)` have the same
`Module.finrank` (`CochainComplex.finrank_homology_linearHomComplex_single`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2 and Corollary 3.3.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press (1994),
  Theorem 3.6.5.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex Abelian
open scoped nonZeroDivisors

universe v u

namespace CochainComplex

section TorsionFree

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Small.{v} R]
  (K : CochainComplex (ModuleCat.{v} R) ℤ) (Y : ModuleCat.{v} R) [Module.IsTorsionFree R Y]

/-- Over a principal ideal domain, for any torsion-free coefficient module `Y`, when
`K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` splits, and `H¹⁻ⁱ(K)` is finitely generated,
the image of `linearHomComplexSingleExtToHomology` in `Hⁱ(Hom(K, Y[0]))` is its torsion
submodule. -/
@[simp]
theorem range_linearHomComplexSingleExtToHomology_eq_torsion (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    LinearMap.range (linearHomComplexSingleExtToHomology.{v} R K Y i) =
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) := by
  have htor := ModuleCat.isTorsion_ext_succ_of_finite (K.homology (1 - i)) Y 0
  have hex := exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker.{v}
    (k := R) K Y i
  refine le_antisymm ?_ ?_
  · rw [LinearMap.range_eq_map, Submodule.map_le_iff_le_comap,
      ← (Submodule.isTorsion'_iff_torsion'_eq_top R⁰).mp htor]
    exact (linearHomComplexSingleExtToHomology.{v} R K Y i).le_comap_torsion
  · have hbot : Submodule.torsion R (K.homology (-i) →ₗ[R] Y) = ⊥ :=
      Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
    have hle := ((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
      linearHomComplexSingleKronecker R K Y i).le_comap_torsion
    rw [hbot, ← LinearMap.ker, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
      hex.linearMap_ker_eq] at hle
    exact hle

/-- **Canonical torsion identification for the Hom complex over a PID**: for any torsion-free
coefficient module `Y`, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` splits, and
`H¹⁻ⁱ(K)` is finitely generated, `linearHomComplexSingleExtToHomology` restricts to a canonical
`R`-linear equivalence `Ext¹(H¹⁻ⁱ(K), Y) ≃ₗ[R] torsion R (Hⁱ(Hom(K, Y[0])))`. -/
def linearHomComplexSingleExtEquivTorsion (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    Ext.{v} (K.homology (1 - i)) Y 1 ≃ₗ[R]
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) :=
  (LinearEquiv.ofInjective (linearHomComplexSingleExtToHomology.{v} R K Y i)
    (linearHomComplexSingleExtToHomology_injective K Y i)).trans
    (LinearEquiv.ofEq _ _ (K.range_linearHomComplexSingleExtToHomology_eq_torsion Y i))

@[simp]
lemma coe_linearHomComplexSingleExtEquivTorsion_apply (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))]
    (e : Ext.{v} (K.homology (1 - i)) Y 1) :
    (K.linearHomComplexSingleExtEquivTorsion Y i e :
      (linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) =
      linearHomComplexSingleExtToHomology.{v} R K Y i e := by
  simp [linearHomComplexSingleExtEquivTorsion]

private lemma ker_homLinearEquiv_comp_linearHomComplexSingleKronecker (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [Module.Finite R (K.homology (1 - i))] :
    LinearMap.ker ((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
        linearHomComplexSingleKronecker R K Y i) =
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) := by
  rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot,
    (exact_linearHomComplexSingleExtToHomology_linearHomComplexSingleKronecker.{v}
      (k := R) K Y i).linearMap_ker_eq,
    range_linearHomComplexSingleExtToHomology_eq_torsion]

/-- **Canonical torsion-free quotient identification over a PID**: for any torsion-free
coefficient module `Y`, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` and
`K.iCycles (-i)` split, and `H¹⁻ⁱ(K)` is finitely generated, the Kronecker map descends to a
canonical `R`-linear equivalence `Hⁱ(Hom(K, Y[0])) ⧸ torsion ≃ₗ[R] (H⁻ⁱ(K) →ₗ[R] Y)`. -/
def linearHomComplexSingleModTorsionEquivHom (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] [Module.Finite R (K.homology (1 - i))] :
    ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i ⧸
      Submodule.torsion R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i)) ≃ₗ[R]
      (K.homology (-i) →ₗ[R] Y) :=
  (Submodule.quotEquivOfEq _ _
    (K.ker_homLinearEquiv_comp_linearHomComplexSingleKronecker Y i).symm).trans
    (((ModuleCat.homLinearEquiv (R := R) (S := R)).toLinearMap ∘ₗ
        linearHomComplexSingleKronecker R K Y i).quotKerEquivOfSurjective
      ((ModuleCat.homLinearEquiv (R := R) (S := R)).surjective.comp
        (linearHomComplexSingleKronecker_surjective K Y i)))

@[simp]
lemma linearHomComplexSingleModTorsionEquivHom_mk (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))] [Module.Finite R (K.homology (1 - i))]
    (x : (linearHomComplex R K ((singleFunctor (ModuleCat.{v} R) 0).obj Y)).homology i) :
    K.linearHomComplexSingleModTorsionEquivHom Y i (Submodule.Quotient.mk x) =
      (linearHomComplexSingleKronecker R K Y i x).hom := by
  simp [linearHomComplexSingleModTorsionEquivHom]
  rfl

end TorsionFree

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Over a principal ideal domain, when `K.cycles (1 - i)` is projective, `K.iCycles (1 - i)` and
`K.iCycles (-i)` split, and `H¹⁻ⁱ(K)` and `H⁻ⁱ(K)` are finitely generated, `Hⁱ(Hom(K, R[0]))` and
`H⁻ⁱ(K)` have the same `finrank`. -/
theorem finrank_homology_linearHomComplex_single (i : ℤ)
    [Projective (K.cycles (1 - i))] [IsSplitMono (K.iCycles (1 - i))]
    [IsSplitMono (K.iCycles (-i))]
    [Module.Finite R (K.homology (1 - i))] [Module.Finite R (K.homology (-i))] :
    Module.finrank R
        ((linearHomComplex R K ((singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))).homology i) =
      Module.finrank R (K.homology (-i)) :=
  (finrank_quotient_eq_of_le_torsion le_rfl).symm.trans
    ((K.linearHomComplexSingleModTorsionEquivHom (ModuleCat.of R R) i).finrank_eq.trans
      (TauCeti.Module.dual_finrank_eq_of_isPrincipalIdealRing R (K.homology (-i))))

end CochainComplex
