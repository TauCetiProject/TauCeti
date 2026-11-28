/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Dirichlet characters on congruence subgroups

A Dirichlet character modulo `N` with values in a normed field has norm `1` on the lower-right
entry of any matrix in `Γ₀(N)`, since that entry is a unit modulo `N`. This makes the absolute
value of a function automorphic with nebentypus invariant under `Γ₀(N)`.

A quadratic Dirichlet character modulo `N` takes equal values on the two diagonal entries of
any matrix in `Γ₀(N)`: their product is one modulo `N`, and a quadratic character is its own
inverse. This identifies the upper-left and lower-right character factors in theta slash laws.
-/

public section

open scoped MatrixGroups

namespace DirichletCharacter

/-- A Dirichlet character with values in a normed field has norm `1` on the lower-right entry of
a matrix in `Γ₀(N)`, which is a unit modulo `N`. -/
theorem norm_apply_one_one_of_mem_Gamma0 {F : Type*} [NormedField F] {N : ℕ}
    (χ : DirichletCharacter F N) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ‖χ ((γ 1 1 : ℤ) : ZMod N)‖ = 1 :=
  χ.unit_norm_eq_one (CongruenceSubgroup.isUnit_intCast_apply_one_one_of_mem_Gamma0 hγ).unit

end DirichletCharacter

namespace MulChar.IsQuadratic

/-- A quadratic Dirichlet character takes equal values on the diagonal entries of a matrix
in `Γ₀(N)`. -/
theorem apply_one_one_eq_apply_zero_zero_of_mem_Gamma0 {R : Type*} [CommRing R]
    {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {A : SL(2, ℤ)}
    (hA : A ∈ CongruenceSubgroup.Gamma0 N) : χ (A 1 1 : ℤ) = χ (A 0 0 : ℤ) := by
  have hprod : χ (A 0 0 : ℤ) * χ (A 1 1 : ℤ) = 1 := by
    rw [← map_mul, CongruenceSubgroup.intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hA,
      map_one]
  have hsq : χ (A 0 0 : ℤ) * χ (A 0 0 : ℤ) = 1 := by
    simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply
      (CongruenceSubgroup.isUnit_intCast_apply_zero_zero_of_mem_Gamma0 hA)] using
      congrArg (fun ψ : DirichletCharacter R N ↦ ψ (A 0 0 : ℤ)) hχ.sq_eq_one
  calc
    χ (A 1 1 : ℤ) = (χ (A 0 0 : ℤ) * χ (A 0 0 : ℤ)) * χ (A 1 1 : ℤ) := by rw [hsq, one_mul]
    _ = χ (A 0 0 : ℤ) := by rw [mul_assoc, hprod, mul_one]

end MulChar.IsQuadratic
