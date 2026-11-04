/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.Module

/-!
# Integrating a square-zero root pair

Suppose `E² = F² = 0`, `EFE = E` and `FEF = F` in an algebra `A` over a commutative ring `R`.
The elements `EF`, `E`, `F`, `FE` satisfy the matrix-unit relations. The complementary
idempotent `1 - EF - FE` is fixed by the action, so a matrix `g` acts by

`1 + (g₀₀ - 1) EF + g₀₁ E + g₁₀ F + (g₁₁ - 1) FE`.

This formula is multiplicative even on the full matrix monoid. Restriction gives an explicit
homomorphism `SL₂(R) → Aˣ`, with the prescribed positive and negative root elements and diagonal
torus. In particular it constructs rank-one group maps from integral square-zero root operators
without dividing by two, and remains valid in bad characteristic and over nonreduced rings.
The halved relations needed for a square-zero `sl₂` triple in characteristic zero are supplied by
`TauCeti.Sl2.e_mul_f_mul_e_of_mul_self_eq_zero` and its lowering counterpart.

## Main declarations

* `TauCeti.Sl2.squareZeroMatrixHom`: the action of the full two-by-two matrix monoid.
* `TauCeti.Sl2.squareZeroSL2Hom`: its restriction to the special linear group, valued in units.
* `TauCeti.Sl2.mul_root_eq_lower_mul_torus_mul_upper`: the rank-one Gauss factorization.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3, rank-one root groups.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.Sl2

open scoped MatrixGroups

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable (E F : A) (hEE : E * E = 0) (hFF : F * F = 0)
  (hEFE : E * F * E = E) (hFEF : F * E * F = F)

/-- The standard two-dimensional matrix action on the support of a square-zero root pair,
extended by the trivial action on the complementary idempotent. This preserves multiplication
and one, but in general does not preserve addition or zero. -/
def squareZeroMatrixHom : Matrix (Fin 2) (Fin 2) R →* A where
  toFun g := 1 + (g 0 0 - 1) • (E * F) + g 0 1 • E + g 1 0 • F +
    (g 1 1 - 1) • (F * E)
  map_one' := by simp
  map_mul' g k := by
    have hEFF : E * F * F = 0 := by rw [mul_assoc, hFF, mul_zero]
    have hFEE : F * E * E = 0 := by rw [mul_assoc, hEE, mul_zero]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, one_mul, mul_one,
      smul_mul_assoc, mul_smul_comm, hEFE, hFEF, hEFF, hFEE, hEE, hFF,
      smul_zero, add_zero, ← mul_assoc]
    module

-- Keep entry expansions as named rewrites: expanding before `map_mul` hides the homomorphism.
/-- The matrix action is given by its four entries and the two root operators. -/
theorem squareZeroMatrixHom_apply (g : Matrix (Fin 2) (Fin 2) R) :
    squareZeroMatrixHom E F hEE hFF hEFE hFEF g =
      1 + (g 0 0 - 1) • (E * F) + g 0 1 • E + g 1 0 • F +
        (g 1 1 - 1) • (F * E) := (rfl)

/-- Integration of a square-zero root pair to `SL₂`, with a trivial action outside its support.
No injectivity of this homomorphism is asserted. -/
def squareZeroSL2Hom : SL(2, R) →* Aˣ :=
  ((squareZeroMatrixHom E F hEE hFF hEFE hFEF).comp
    Matrix.SpecialLinearGroup.coeMonoidHom).toHomUnits

/-- The integrated `SL₂` action has the same four-entry formula as the matrix-monoid action. -/
theorem coe_squareZeroSL2Hom (g : SL(2, R)) :
    (squareZeroSL2Hom E F hEE hFF hEFE hFEF g : A) =
      1 + (g 0 0 - 1) • (E * F) + g 0 1 • E + g 1 0 • F +
        (g 1 1 - 1) • (F * E) := (rfl)

/-- The positive elementary matrix integrates to the raising root element. -/
@[simp]
theorem coe_squareZeroSL2Hom_upper (t : R) :
    (squareZeroSL2Hom E F hEE hFF hEFE hFEF
      (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t) : A) =
      1 + t • E := by
  simp [coe_squareZeroSL2Hom, Matrix.SpecialLinearGroup.transvection_coe]

/-- The negative elementary matrix integrates to the lowering root element. -/
@[simp]
theorem coe_squareZeroSL2Hom_lower (t : R) :
    (squareZeroSL2Hom E F hEE hFF hEFE hFEF
      (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t) : A) =
      1 + t • F := by
  simp [coe_squareZeroSL2Hom, Matrix.SpecialLinearGroup.transvection_coe]

/-- The diagonal torus scales the two idempotent summands by a unit and its inverse. -/
@[simp]
theorem coe_squareZeroSL2Hom_diagonal (u : Rˣ) :
    (squareZeroSL2Hom E F hEE hFF hEFE hFEF
      (Matrix.SpecialLinearGroup.diag2nUnit (by decide : (0 : Fin 2) ≠ 1) u) : A) =
      1 + ((u : R) - 1) • (E * F) + (((u⁻¹ : Rˣ) : R) - 1) • (F * E) := by
  simp [coe_squareZeroSL2Hom, Matrix.SpecialLinearGroup.diag2nUnit_coe]

/-- Over a field, containment of the upper and lower root families suffices for containment of
the integrated rank-one group in a subgroup of the units. -/
theorem squareZeroSL2Hom_mem_of_upper_lower_mem {K : Type*} [Field K] [Algebra K A]
    (E F : A) (hEE : E * E = 0) (hFF : F * F = 0)
    (hEFE : E * F * E = E) (hFEF : F * E * F = F) {H : Subgroup Aˣ}
    (hupper : ∀ t : K, squareZeroSL2Hom E F hEE hFF hEFE hFEF
      (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t) ∈ H)
    (hlower : ∀ t : K, squareZeroSL2Hom E F hEE hFF hEFE hFEF
      (Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t) ∈ H)
    (g : SL(2, K)) : squareZeroSL2Hom E F hEE hFF hEFE hFEF g ∈ H := by
  induction g using Matrix.SL2.transvection_induction with
  | htransvec a b hab t =>
    fin_cases a <;> fin_cases b
    · exact (hab rfl).elim
    · exact hupper t
    · exact hlower t
    · exact (hab rfl).elim
  | hmul g h hg hh => simpa only [map_mul] using H.mul_mem hg hh

include hEE hFF hEFE hFEF in
/-- The rank-one Gauss factorization on the open set where `1 + a * b` is a unit.
The middle factor is the coroot value, written using the two idempotents. -/
theorem mul_root_eq_lower_mul_torus_mul_upper (a b : R) (u : Rˣ)
    (hu : (u : R) = 1 + a * b) :
    (1 + a • E) * (1 + b • F) =
      (1 + (b * ((u⁻¹ : Rˣ) : R)) • F) *
        (1 + ((u : R) - 1) • (E * F) + (((u⁻¹ : Rˣ) : R) - 1) • (F * E)) *
        (1 + (a * ((u⁻¹ : Rˣ) : R)) • E) := by
  have hunit : (1 + a * b) * ((u⁻¹ : Rˣ) : R) = 1 := by
    rw [← hu]
    exact Units.mul_inv u
  have hmatrix :
      (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, 0; b, 1] =
        !![1, 0; b * ((u⁻¹ : Rˣ) : R), 1] * !![(u : R), 0; 0, ((u⁻¹ : Rˣ) : R)] *
          !![1, a * ((u⁻¹ : Rˣ) : R); 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_fin_two, Matrix.of_apply, hu] <;>
      grind
  have h := congrArg (squareZeroMatrixHom E F hEE hFF hEFE hFEF) hmatrix
  simp only [map_mul] at h
  simpa [squareZeroMatrixHom_apply] using h

end TauCeti.Sl2
