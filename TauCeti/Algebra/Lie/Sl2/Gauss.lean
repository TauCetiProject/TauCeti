/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.SquareZero
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-!
# Gauss factorization for square-zero root pairs

For opposite square-zero root operators, the rank-one open cell has a Gauss factorization
whenever `1 + a * b` is a unit. The middle factor scales the two root-string endpoints by that
unit and its inverse. The calculation uses only the integral identities `EFE = E`, `FEF = F`,
so remains valid after specialization to rings with torsion or nilpotents.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.Sl2

/-- Opposite square-zero exponentials admit Gauss factorization on the open set where
`1 + a * b` is a unit. The middle factor is the coroot's action on the two root-string
endpoints. No root parameter itself is required to be a unit. -/
theorem gauss_of_mul_self_eq_zero {R A : Type*} [CommRing R] [Ring A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {E F : A}
    (hEE : E * E = 0) (hFF : F * F = 0)
    (hEFE : E * F * E = E) (hFEF : F * E * F = F)
    (a b : R) (u : Rˣ) (hu : (u : R) = 1 + a * b) :
    (1 + a • E) * (1 + b • F) =
      (1 + (b * (↑(u⁻¹) : R)) • F) *
        (1 + ((u : R) - 1) • (E * F) + ((↑(u⁻¹) : R) - 1) • (F * E)) *
        (1 + (a * (↑(u⁻¹) : R)) • E) := by
  have hv : (u : R) * (↑(u⁻¹) : R) = 1 := u.mul_inv
  have hFEE : F * E * E = 0 := by rw [mul_assoc, hEE, mul_zero]
  -- Collect coefficients of the four surviving monomials `E`, `F`, `EF`, and `FE`.
  simp only [add_mul, mul_add, smul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, ← mul_assoc, hEFE, hFEF, hFEE, hFF,
    smul_zero, add_zero]
  match_scalars <;> simp only [hu] at hv ⊢
  · linear_combination -a * hv
  · linear_combination -b * hv
  · ring
  · linear_combination -(1 + a * b * (↑(u⁻¹) : R)) * hv

end TauCeti.Sl2
