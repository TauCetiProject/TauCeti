/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Rank
public import TauCeti.Algebra.Lie.HighestWeight.Isotypic
public import TauCeti.Algebra.Lie.Multiplicity
public import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.LeftRegular
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector

import TauCeti.Algebra.Lie.CartanExists
import TauCeti.Algebra.Lie.HighestWeight.Weyl.Dimension
import TauCeti.Algebra.Lie.UniversalEnveloping.Multiplicity
import TauCeti.Algebra.Lie.Weights.Dimension
import TauCeti.Algebra.Lie.Weights.Rank
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.Casimir
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.HighestWeight
import TauCeti.LinearAlgebra.CliffordAlgebra.Quadratic.Lie.KostantWeights

/-!
# Kostant's isotypy theorem

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form `κ` over an
algebraically closed field of characteristic zero, of dimension `d` and rank `l`. The Clifford
algebra of `κ`, acted on by left multiplication by the quadratic lift of the adjoint representation,
is a direct sum of `2 ^ ((d + l) / 2)` copies of the irreducible module `L(ρ)` of highest weight the
half-sum `ρ` of the positive roots, and `L(ρ)` has dimension `2 ^ ((d - l) / 2)`.

The Casimir element acts on this module by the scalar `d / 8`, so all highest weights share one
Casimir scalar. Every highest weight is also a dominant integral weight lying below `ρ`, and `ρ` is
itself a highest weight, so `ρ` is the only one. The multiplicity is then read off from the
dimensions `2 ^ d` of the Clifford algebra and `2 ^ ((d - l) / 2)` of `L(ρ)`, the second coming from
the Weyl dimension formula. The two divisions by two are exact, since `d = l + 2 * #Δ⁺`.

## Main results

* `CliffordAlgebra.eq_weylVector_of_isHighestWeightVector_kostant`: every highest weight vector of
  Kostant's module has weight `ρ`.
* `CliffordAlgebra.isIsotypicOfType_irreducibleQuotient_weylVector_kostant`: Kostant's module is
  isotypic of type `L(ρ)`.
* `CliffordAlgebra.isotypicMultiplicity_irreducibleQuotient_weylVector_kostant`: the multiplicity of
  `L(ρ)` is `2 ^ ((d + l) / 2)`.
* `CliffordAlgebra.nonempty_lieModuleEquiv_directSum_irreducibleQuotient_weylVector_kostant`: the
  decomposition of Kostant's module into copies of `L(ρ)`.
* `CliffordAlgebra.kostant_isotypic`: any two irreducible submodules are isomorphic.
* `CliffordAlgebra.kostant_multiplicity`: the decomposition into copies of an irreducible submodule,
  with no choice of Cartan subalgebra or base in the statement.

## References

* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem, the ρ-decomposition
  `C(𝔤) = End V_ρ ⊗ C(P)`, and the `𝔤`-module structure of `⋀𝔤`*, Adv. Math. 125 (1997), 275--350.
* E. Meinrenken, *Clifford Algebras and Lie Theory*, Springer Ergebnisse 58 (2013).
-/

public section

universe u v

open TauCeti TauCeti.LieAlgebra LieAlgebra LieModule Module
open scoped CliffordAlgebra DirectSum

namespace CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] [CharZero K] {L : Type v} [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [Invertible (2 : K)] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-- **The only highest weight of Kostant's module is `ρ`.** -/
theorem eq_weylVector_of_isHighestWeightVector_kostant [IsTriangularizable K H L]
    {base : (IsKilling.rootSystem H).Base} {lam : Dual K H}
    {c : CliffordAlgebra (killingQuadraticForm K L)} (hc : IsHighestWeightVector base lam c) :
    lam = weylVector (IsKilling.rootSystem H) base := by
  -- All highest weights share one Casimir scalar, and `ρ` is itself a highest weight.
  obtain ⟨c₀, hc₀⟩ := exists_isHighestWeightVector_weylVector_kostant base
  exact eq_weylVector_of_isHighestWeightVector_kostant_of_casimirScalar_eq base hc
    ((casimirScalar_eq_of_isHighestWeightVector_kostant hc).trans
      (casimirScalar_eq_of_isHighestWeightVector_kostant hc₀).symm)

variable [IsAlgClosed K]

section Base

variable (base : (IsKilling.rootSystem H).Base)

attribute [local instance] complementedLattice_lieSubmodule_of_isKilling

/-- **Kostant's module is isotypic of type `L(ρ)`.** Every irreducible Lie submodule of the Clifford
algebra of the Killing form is a copy of `L(ρ)`. -/
theorem isIsotypicOfType_irreducibleQuotient_weylVector_kostant :
    IsIsotypicOfType K L (CliffordAlgebra (killingQuadraticForm K L))
      (irreducibleQuotient base (weylVector (IsKilling.rootSystem H) base)) :=
  isIsotypicOfType_of_forall_isHighestWeightVector
    (isHighestWeightVector_irreducibleQuotientGenerator base _)
    fun _ _ hu ↦ eq_weylVector_of_isHighestWeightVector_kostant hu

/-- **The multiplicity of `L(ρ)` in Kostant's module** is `2 ^ ((d + l) / 2)`, for `L` of dimension
`d` and rank `l`. -/
@[simp]
theorem isotypicMultiplicity_irreducibleQuotient_weylVector_kostant :
    isotypicMultiplicity K L (CliffordAlgebra (killingQuadraticForm K L))
      (irreducibleQuotient base (weylVector (IsKilling.rootSystem H) base)) =
      2 ^ ((finrank K L + LieAlgebra.rank K L) / 2) := by
  have _ := finiteDimensional_irreducibleQuotient_weylVector base
  have hdim := finrank_of_isIsotypicOfType (M := CliffordAlgebra (killingQuadraticForm K L)) _
    (isIsotypicOfType_irreducibleQuotient_weylVector_kostant base)
  rw [finrank_eq_two_pow, finrank_irreducibleQuotient_weylVector] at hdim
  have hd := finrank_eq_finrank_cartan_add_two_mul_ncard_posRoots H base
  rw [H.rank_eq_finrank_cartan]
  refine (Nat.eq_of_mul_eq_mul_right (pow_pos two_pos ((finrank K L - finrank K H) / 2))
    (hdim.symm.trans ?_))
  rw [← pow_add]
  congr 1
  omega

/-- **Kostant's decomposition.** The Clifford algebra of the Killing form, under left multiplication
by the quadratic lift of the adjoint representation, is a direct sum of `2 ^ ((d + l) / 2)` copies
of `L(ρ)`, for `L` of dimension `d` and rank `l`. -/
theorem nonempty_lieModuleEquiv_directSum_irreducibleQuotient_weylVector_kostant :
    Nonempty (CliffordAlgebra (killingQuadraticForm K L) ≃ₗ⁅K,L⁆
      ⨁ _ : Fin (2 ^ ((finrank K L + LieAlgebra.rank K L) / 2)),
        irreducibleQuotient base (weylVector (IsKilling.rootSystem H) base)) := by
  have _ := finiteDimensional_irreducibleQuotient_weylVector base
  rw [← isotypicMultiplicity_irreducibleQuotient_weylVector_kostant base]
  exact nonempty_lieModuleEquiv_of_isIsotypicOfType _
    (isIsotypicOfType_irreducibleQuotient_weylVector_kostant base)

end Base

/-- **Kostant's isotypy theorem.** Any two irreducible Lie submodules of the Clifford algebra of the
Killing form, under left multiplication by the quadratic lift of the adjoint representation, are
isomorphic. -/
theorem kostant_isotypic : IsIsotypic K L (CliffordAlgebra (killingQuadraticForm K L)) := by
  obtain ⟨_, _, ⟨b⟩⟩ := exists_isCartanSubalgebra_base K L
  exact (isIsotypicOfType_irreducibleQuotient_weylVector_kostant b).isIsotypic

/-- **Kostant's multiplicity theorem.** The Clifford algebra of the Killing form, under left
multiplication by the quadratic lift of the adjoint representation, is a direct sum of
`2 ^ ((d + l) / 2)` copies of an irreducible Lie submodule of dimension `2 ^ ((d - l) / 2)`, for `L`
of dimension `d` and rank `l`. -/
theorem kostant_multiplicity :
    ∃ S : LieSubmodule K L (CliffordAlgebra (killingQuadraticForm K L)),
      IsIrreducible K L S ∧
      finrank K S = 2 ^ ((finrank K L - LieAlgebra.rank K L) / 2) ∧
      Nonempty (CliffordAlgebra (killingQuadraticForm K L) ≃ₗ⁅K,L⁆
        ⨁ _ : Fin (2 ^ ((finrank K L + LieAlgebra.rank K L) / 2)), S) := by
  obtain ⟨H, _, ⟨b⟩⟩ := exists_isCartanSubalgebra_base K L
  obtain ⟨c, hc⟩ := exists_isHighestWeightVector_weylVector_kostant b
  obtain ⟨e⟩ := lieSpan_equiv_irreducibleQuotient_of_isHighestWeightVector hc
  obtain ⟨E⟩ := nonempty_lieModuleEquiv_directSum_irreducibleQuotient_weylVector_kostant b
  refine ⟨LieSubmodule.lieSpan K L {c}, isIrreducible_lieSpan_of_isHighestWeightVector hc, ?_,
    ⟨E.trans (DirectSum.lieModuleEquivCongrRight fun _ ↦ e.symm)⟩⟩
  rw [e.toLinearEquiv.finrank_eq, finrank_irreducibleQuotient_weylVector,
    H.rank_eq_finrank_cartan]

end CliffordAlgebra
