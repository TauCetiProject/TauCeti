/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Irreducible
public import TauCeti.Algebra.Lie.HighestWeight.Verma
public import TauCeti.Algebra.Lie.Multiplicity
public import TauCeti.Algebra.Lie.Sl2.DiagonalCartan
public import TauCeti.Algebra.Lie.Sl2.Standard
public import TauCeti.Algebra.Lie.Weights.FormalCharacter
import TauCeti.Algebra.Lie.Weights.Basis

/-!
# The standard `sl₂`-modules as highest weight modules

The standard irreducible module `V(n) = TauCeti.Sl2Std K n` of `L = sl (Fin 2) K` is built by hand
from its coordinate basis `v₀, …, vₙ`, while the general highest-weight theory works with a Cartan
subalgebra `H`, a base of its root system and the irreducible quotient `L(λ)` of the Verma module.
This file matches the two for the diagonal Cartan `H = TauCeti.slTwoDiagonalCartan K` and the
positive base `TauCeti.slTwoPositiveBase K`, which selects `e = E₀₁` as positive. Weights of `H` are
read in the coordinate `t = λ(h)` through `TauCeti.slTwoWeight`.

* The coordinate vector `vᵢ` is a weight vector of weight `n - 2i`, so the formal character of
  `V(n)` is `e^{n} + e^{n-2} + ⋯ + e^{-n}`.
* `v₀` is a highest weight vector of weight `n`, so `V(n)` is the irreducible module `L(n)`, which
  therefore has dimension `n + 1`.
* By Schur's lemma, `L(λ)` occurs in `V(n)` with multiplicity one when `λ = n` and zero otherwise.

These are the inputs that let the general toolkit of characters and isotypic multiplicities be
evaluated on concrete `sl₂`-modules built from `V(n)`.

## Main results

* `TauCeti.Sl2Std.lie_basis_of_slTwoDiagonalCartan`: `vᵢ` has weight `n - 2i`.
* `TauCeti.Sl2Std.isTriangularizable_slTwoDiagonalCartan`: `V(n)` is triangularizable for the
  diagonal Cartan.
* `TauCeti.Sl2Std.formalCharacter_eq_sum`: the formal character of `V(n)`.
* `TauCeti.Sl2Std.isHighestWeightVector_basis_zero`: `v₀` is a highest weight vector of weight `n`.
* `TauCeti.Sl2Std.nonempty_lieModuleEquiv_irreducibleQuotient`: `V(n) ≅ L(n)`.
* `TauCeti.finiteDimensional_irreducibleQuotient_slTwoWeight` and
  `TauCeti.finrank_irreducibleQuotient_slTwoWeight`: `L(n)` is finite-dimensional, of dimension
  `n + 1`.
* `TauCeti.Sl2Std.isotypicMultiplicity_irreducibleQuotient`: the multiplicity of `L(λ)` in `V(n)`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §7.2 and §20.
-/

public section

open LieAlgebra LieModule Module

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Sl2Std

/-! ### The weights of `V(n)` -/

section Weights

variable {K : Type*} [Field K] {n : ℕ}

/-- **The coordinate vector `vᵢ` of `V(n)` is a weight vector of weight `n - 2i`** for the
diagonal Cartan. -/
theorem lie_basis_of_slTwoDiagonalCartan (x : slTwoDiagonalCartan K) (i : Fin (n + 1)) :
    ⁅(x : SpecialLinear.sl (Fin 2) K), basis K n i⁆ =
      slTwoWeight ((n : K) - 2 * (i : ℕ)) x • basis K n i := by
  have hx : (x : SpecialLinear.sl (Fin 2) K) = x.val.val 0 0 • slFinTwoBasis K 2 := by
    conv_lhs => rw [eq_smul_slTwoCartanGenerator x]
    rw [SetLike.val_smul, coe_slTwoCartanGenerator, slFinTwoBasis_two]
  have hw : slTwoWeight ((n : K) - 2 * (i : ℕ)) x = x.val.val 0 0 * ((n : K) - 2 * (i : ℕ)) := by
    conv_lhs => rw [eq_smul_slTwoCartanGenerator x]
    rw [map_smul, slTwoWeight_slTwoCartanGenerator, smul_eq_mul]
  rw [hx, smul_lie, lie_slFinTwoBasis_two, diag_basis, smul_smul, hw]

/-- `V(n)` is triangularizable for the diagonal Cartan, its coordinate basis consisting of weight
vectors. -/
instance isTriangularizable_slTwoDiagonalCartan :
    IsTriangularizable K (slTwoDiagonalCartan K) (Sl2Std K n) :=
  (basis K n).isTriangularizable_of_weight_basis fun i x ↦ lie_basis_of_slTwoDiagonalCartan x i

variable (K n) in
/-- **The formal character of `V(n)`** for the diagonal Cartan is
`e^{n} + e^{n-2} + ⋯ + e^{-n}`, one term for each coordinate vector. -/
theorem formalCharacter_eq_sum :
    formalCharacter K (slTwoDiagonalCartan K) (Sl2Std K n) =
      ∑ i : Fin (n + 1), AddMonoidAlgebra.single (slTwoWeight ((n : K) - 2 * (i : ℕ))) 1 :=
  (basis K n).formalCharacter_eq_sum_single_of_weight_basis fun i x ↦
    lie_basis_of_slTwoDiagonalCartan x i

end Weights

/-! ### `V(n)` is the irreducible highest weight module `L(n)` -/

section HighestWeight

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The weights of `V(n)` are the `n - 2i`: every other linear form on the diagonal Cartan has a
zero generalized weight space. -/
private theorem genWeightSpace_eq_bot {χ : Dual K (slTwoDiagonalCartan K)}
    (hχ : ∀ i : Fin (n + 1), χ (slTwoCartanGenerator K) ≠ (n : K) - 2 * (i : ℕ)) :
    genWeightSpace (Sl2Std K n) (χ : slTwoDiagonalCartan K → K) = ⊥ := by
  by_contra hne
  obtain ⟨i, hi⟩ := ((basis K n).genWeightSpace_ne_bot_iff_of_weight_basis
    (fun i x ↦ lie_basis_of_slTwoDiagonalCartan x i) _).mp hne
  refine hχ i ?_
  rw [← congrFun hi (slTwoCartanGenerator K), slTwoWeight_slTwoCartanGenerator]

/-- **`v₀` is a highest weight vector of weight `n`** for the diagonal Cartan and the positive
base: a positive root vector would raise it to the weight `n + 2`, which `V(n)` does not have. -/
theorem isHighestWeightVector_basis_zero :
    IsHighestWeightVector (slTwoPositiveBase K) (slTwoWeight (n : K)) (basis K n 0) := by
  refine isHighestWeightVector_of_forall_rootSpace ((basis K n).ne_zero 0) (fun x ↦ ?_) ?_
  · simpa using lie_basis_of_slTwoDiagonalCartan x 0
  intro α hα x hx
  have hα' : α = slTwoRootIndex K := by
    rw [← mem_posRootsFinset, posRootsFinset_slTwoPositiveBase] at hα
    exact Finset.mem_singleton.mp hα
  subst hα'
  have hv : basis K n 0 ∈ genWeightSpace (Sl2Std K n)
      ((slTwoWeight (n : K) : Dual K (slTwoDiagonalCartan K)) : slTwoDiagonalCartan K → K) :=
    weightSpace_le_genWeightSpace _ _ <| (mem_weightSpace _ _).mpr fun x ↦ by
      simpa using lie_basis_of_slTwoDiagonalCartan x 0
  have hmem := lie_mem_genWeightSpace_of_mem_genWeightSpace hx hv
  have hsum : ⇑(slTwoRootIndex K : Weight K (slTwoDiagonalCartan K)
      (SpecialLinear.sl (Fin 2) K)).toLinear + ⇑(slTwoWeight (n : K)) =
      ⇑(slTwoWeight ((n : K) + 2)) := by
    rw [coe_slTwoRootIndex, toLinear_slTwoRoot, ← LinearMap.coe_add]
    congr 1
    exact dual_ext_slTwoCartanGenerator <| by simp [add_comm]
  rw [hsum, genWeightSpace_eq_bot fun i h ↦ ?_] at hmem
  · exact (LieSubmodule.mem_bot _).mp hmem
  · rw [slTwoWeight_slTwoCartanGenerator] at h
    have : ((2 * ((i : ℕ) + 1) : ℕ) : K) = 0 := by push_cast; linear_combination h
    exact absurd (Nat.cast_eq_zero.mp this) (by omega)

/-- **`V(n)` is the irreducible highest weight module `L(n)`**: both are irreducible and carry
highest weight vectors of weight `n`. -/
theorem nonempty_lieModuleEquiv_irreducibleQuotient :
    Nonempty (Sl2Std K n ≃ₗ⁅K, SpecialLinear.sl (Fin 2) K⁆
      irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (n : K))) :=
  nonempty_lieModuleEquiv_of_isHighestWeightVector isHighestWeightVector_basis_zero
    (isHighestWeightVector_irreducibleQuotientGenerator _ _)

open scoped Classical in
/-- **`L(λ)` occurs in `V(n)` exactly when `λ = n`, and then once.** This is Schur's lemma: `V(n)`
and `L(λ)` are irreducible, and they are equivalent exactly when their highest weights agree. -/
theorem isotypicMultiplicity_irreducibleQuotient [IsAlgClosed K]
    (lam : Dual K (slTwoDiagonalCartan K)) :
    LieModule.isotypicMultiplicity K (SpecialLinear.sl (Fin 2) K) (Sl2Std K n)
        (irreducibleQuotient (slTwoPositiveBase K) lam) =
      if lam = slTwoWeight (n : K) then 1 else 0 := by
  split_ifs with h
  · subst h
    obtain ⟨e⟩ := nonempty_lieModuleEquiv_irreducibleQuotient (K := K) (n := n)
    rw [← LieModule.isotypicMultiplicity_eq_of_lieModuleEquiv_type e,
      LieModule.isotypicMultiplicity_self]
  · rw [LieModule.isotypicMultiplicity_def]
    refine LieModule.finrank_lieModuleHom_eq_zero_of_isEmpty_lieModuleEquiv
      (not_nonempty_iff.mp fun he ↦ h ?_)
    exact ((nonempty_lieModuleEquiv_iff_eq_of_isHighestWeightVector
      (isHighestWeightVector_irreducibleQuotientGenerator _ _)
      isHighestWeightVector_basis_zero).mp he)

end HighestWeight

end Sl2Std

section IrreducibleQuotient

variable {K : Type*} [Field K] [CharZero K] (n : ℕ)

/-- `L(n)` is finite-dimensional for the diagonal Cartan of `sl₂`, being equivalent to `V(n)`. -/
instance finiteDimensional_irreducibleQuotient_slTwoWeight :
    FiniteDimensional K (irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (n : K))) :=
  Module.Finite.equiv
    (Sl2Std.nonempty_lieModuleEquiv_irreducibleQuotient (K := K) (n := n)).some.toLinearEquiv

/-- **`dim L(n) = n + 1`** for the diagonal Cartan of `sl₂`, `L(n)` being equivalent to `V(n)`. -/
theorem finrank_irreducibleQuotient_slTwoWeight :
    finrank K (irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (n : K))) = n + 1 := by
  obtain ⟨e⟩ := Sl2Std.nonempty_lieModuleEquiv_irreducibleQuotient (K := K) (n := n)
  rw [← e.toLinearEquiv.finrank_eq, Sl2Std.finrank_eq]

end IrreducibleQuotient

end TauCeti
