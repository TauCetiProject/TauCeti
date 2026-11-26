/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.HighestWeight
public import TauCeti.QuantumGroups.UqSl2.ClassicalSpecialization.Basic

/-!
# The classical specialization of `L_m^+` as the irreducible highest weight module `L(m)`

The classical specialization `ClassicalLadder K m` of the positive ladder module `L_m^+` of
`U_q(sl₂)` is the `sl₂`-module on `K^(m+1)` whose ladder basis satisfies
`E v_j = (m - j + 1) v_(j - 1)`, `F v_j = (j + 1) v_(j + 1)` and `H v_j = (m - 2j) v_j`. The general
highest weight theory has its own irreducible module of highest weight `m`: the irreducible
quotient `L(m)` of the Verma module for the diagonal Cartan subalgebra and the positive base in
which `e = E₀₁` is positive, with its canonical generator `v⁺`.

This file gives the explicit isomorphism between the two over a field of characteristic zero. It
sends `v₀` to `v⁺`, and because the ladder basis is normalized by `F^j v₀ = j! v_j`, it sends the
ladder vector `v_j` to `(j!)⁻¹ F^j v⁺`. That formula is forced on every module map out of the
classical specialization, so the isomorphism is the only module map sending `v₀` to `v⁺`.

## Main definitions

* `TauCeti.UqSl2.ClassicalLadder.equivIrreducibleQuotient`: the isomorphism of
  `sl (Fin 2) K`-modules from the classical specialization of `L_m^+` to `L(m)`.

## Main results

* `TauCeti.UqSl2.ClassicalLadder.map_basis`: a module map `φ` out of the classical specialization
  sends `v_j` to `(j!)⁻¹ F^j φ(v₀)`.
* `TauCeti.UqSl2.ClassicalLadder.lieModuleHom_ext`: a module map out of the classical
  specialization is determined by its value on `v₀`.
* `TauCeti.UqSl2.ClassicalLadder.equivIrreducibleQuotient_basis_zero` and
  `equivIrreducibleQuotient_basis`: the isomorphism sends `v₀` to `v⁺` and `v_j` to
  `(j!)⁻¹ F^j v⁺`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Graduate Texts in
  Mathematics 9, Sections 7.2 and 20.3.
-/

public section

open LieAlgebra LieModule Module

namespace TauCeti

namespace UqSl2

namespace ClassicalLadder

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [CharZero K] {m : ℕ}

/-- **A module map out of the classical specialization is determined by the image of `v₀`**: it
sends the ladder vector `v_j` to `(j!)⁻¹ F^j φ(v₀)`, since `F^j v₀ = j! v_j`. -/
theorem map_basis {M : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule (SpecialLinear.sl (Fin 2) K) M] [LieModule K (SpecialLinear.sl (Fin 2) K) M]
    (φ : ClassicalLadder K m →ₗ⁅K,SpecialLinear.sl (Fin 2) K⁆ M) (j : Fin (m + 1)) :
    φ (basis K m j) = ((j : ℕ).factorial : K)⁻¹ •
      (toEnd K (SpecialLinear.sl (Fin 2) K) M (slFinTwoBasis K 1) ^ (j : ℕ)) (φ (basis K m 0)) := by
  rw [toEnd_pow_apply_map, toEnd_slFinTwoBasis_one, lower_pow_basis_zero, map_smul,
    inv_smul_smul₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]

/-- **Two module maps out of the classical specialization that agree on `v₀` are equal**: by
`TauCeti.UqSl2.ClassicalLadder.map_basis` both are determined on the ladder basis by their value
on `v₀`. -/
@[ext]
theorem lieModuleHom_ext {M : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule (SpecialLinear.sl (Fin 2) K) M] [LieModule K (SpecialLinear.sl (Fin 2) K) M]
    {φ ψ : ClassicalLadder K m →ₗ⁅K,SpecialLinear.sl (Fin 2) K⁆ M}
    (h : φ (basis K m 0) = ψ (basis K m 0)) : φ = ψ := by
  have hlin : (φ : ClassicalLadder K m →ₗ[K] M) = ψ := (basis K m).ext fun j => by
    simp only [LieModuleHom.coe_toLinearMap, map_basis φ j, map_basis ψ j, h]
  exact LieModuleHom.ext fun v => LinearMap.congr_fun hlin v

variable (K m) in
/-- **The classical specialization of `L_m^+` is the irreducible highest weight module `L(m)`**
of the general highest weight theory, for the diagonal Cartan subalgebra and the positive base of
`sl (Fin 2) K`: the isomorphism sending `v₀` to the canonical generator `v⁺` of `L(m)`, and hence
the ladder vector `v_j` to `(j!)⁻¹ F^j v⁺` (`equivIrreducibleQuotient_basis`). -/
noncomputable def equivIrreducibleQuotient :
    ClassicalLadder K m ≃ₗ⁅K, SpecialLinear.sl (Fin 2) K⁆
      irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (m : K)) :=
  (equivSl2Std K m).trans <| lieModuleEquivOfIsHighestWeightVector
    Sl2Std.isHighestWeightVector_basis_zero (isHighestWeightVector_irreducibleQuotientGenerator _ _)

variable (K m) in
/-- The isomorphism with `L(m)` sends `v₀` to the canonical generator `v⁺`. -/
@[simp]
theorem equivIrreducibleQuotient_basis_zero :
    equivIrreducibleQuotient K m (basis K m 0) =
      irreducibleQuotientGenerator (slTwoPositiveBase K) (slTwoWeight (m : K)) := by
  simp [equivIrreducibleQuotient, equivSl2Std_basis]

variable (K m) in
/-- The inverse of the isomorphism with `L(m)` sends the canonical generator `v⁺` to `v₀`. -/
@[simp]
theorem equivIrreducibleQuotient_symm_irreducibleQuotientGenerator :
    (equivIrreducibleQuotient K m).symm
        (irreducibleQuotientGenerator (slTwoPositiveBase K) (slTwoWeight (m : K))) =
      basis K m 0 :=
  (LieModuleEquiv.symm_apply_eq _).mpr (equivIrreducibleQuotient_basis_zero K m).symm

/-- **The isomorphism with `L(m)` retains the ladder normalization**: it sends the ladder vector
`v_j` to `(j!)⁻¹ F^j v⁺`, where `F` is the element `f` of the standard `sl₂` triple and `v⁺` the
canonical generator of `L(m)`. -/
theorem equivIrreducibleQuotient_basis (j : Fin (m + 1)) :
    equivIrreducibleQuotient K m (basis K m j) = ((j : ℕ).factorial : K)⁻¹ •
      (toEnd K (SpecialLinear.sl (Fin 2) K)
          (irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (m : K)))
          (slFinTwoBasis K 1) ^ (j : ℕ))
        (irreducibleQuotientGenerator (slTwoPositiveBase K) (slTwoWeight (m : K))) := by
  rw [← equivIrreducibleQuotient_basis_zero K m]
  exact map_basis (equivIrreducibleQuotient K m).toLieModuleHom j

/-- **The isomorphism with `L(m)` is the only module map sending `v₀` to `v⁺`.** -/
theorem eq_equivIrreducibleQuotient_iff
    (φ : ClassicalLadder K m →ₗ⁅K,SpecialLinear.sl (Fin 2) K⁆
      irreducibleQuotient (slTwoPositiveBase K) (slTwoWeight (m : K))) :
    φ = (equivIrreducibleQuotient K m).toLieModuleHom ↔
      φ (basis K m 0) = irreducibleQuotientGenerator (slTwoPositiveBase K) (slTwoWeight (m : K)) :=
  ⟨fun h => h ▸ equivIrreducibleQuotient_basis_zero K m,
    fun h => lieModuleHom_ext (h.trans (equivIrreducibleQuotient_basis_zero K m).symm)⟩

end ClassicalLadder

end UqSl2

end TauCeti
