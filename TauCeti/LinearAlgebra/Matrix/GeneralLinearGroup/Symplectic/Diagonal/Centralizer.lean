/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic

/-!
# The centralizer of the symplectic diagonal torus

The diagonal symplectic matrices are exactly the image of the paired diagonal homomorphism.
Over a domain with a unit different from its inverse, this image is its own centralizer, hence
maximal among commutative subgroups. In particular these conclusions hold over every infinite
field, in all characteristics and in every rank.

This pointwise centralizer calculation supplies the matrix comparison used to prove maximality
of the diagonal torus as a closed subgroup scheme. The unit hypothesis distinguishes the two
weights on each symplectic plane; it cannot simply be omitted over small finite fields.

The proof uses `TauCeti.apply_eq_zero_of_commute_diagonal` and follows the centralizer argument
for general linear groups in `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §16.1 and §26.3.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin

variable {m : ℕ} {R : Type*}

/-- A unit different from its inverse lets paired diagonal coordinates separate any two
positions. -/
theorem exists_diagonalCoordinates_ne [Monoid R] (u : Rˣ) (hu : u ≠ u⁻¹)
    {i j : Fin (m + m)} (hij : i ≠ j) :
    ∃ t : Fin m → Rˣ, diagonalCoordinates t i ≠ diagonalCoordinates t j := by
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hu (inv_one.symm)
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
  · have h : i ≠ j := fun h => hij (by simp [h])
    exact ⟨fun k => if k = i then u else 1, by simp [Ne.symm h, hu1]⟩
  · refine ⟨fun k => if k = i then u else 1, ?_⟩
    by_cases h : j = i <;> simp [Fin.natAdd_eq_addNat, h, hu, hu1]
  · refine ⟨fun k => if k = j then u else 1, ?_⟩
    by_cases h : i = j <;> simp [Fin.natAdd_eq_addNat, h, Ne.symm hu, Ne.symm hu1]
  · have h : i ≠ j := fun h => hij (by simp [h])
    exact ⟨fun k => if k = i then u else 1, by
      simp [Fin.natAdd_eq_addNat, Ne.symm h, hu1]⟩

section Domain

variable [CommRing R] [IsCancelMulZero R]

/-- The paired diagonal torus is its own centralizer whenever the domain has a unit different
from its inverse. -/
theorem centralizer_range_diagonal (u : Rˣ) (hu : u ≠ u⁻¹) :
    Subgroup.centralizer ((diagonal (m := m) (R := R)).range : Set (GLSymplecticFin m R)) =
      (diagonal (m := m) (R := R)).range := by
  refine le_antisymm (fun g hg => MonoidHom.mem_range.mpr <|
    exists_diagonal_eq_iff.mpr fun i j hij => ?_)
    (Subgroup.le_centralizer _)
  obtain ⟨t, ht⟩ := exists_diagonalCoordinates_ne u hu hij
  have hcomm := Subgroup.mem_centralizer_iff.mp hg (diagonal t) ⟨t, rfl⟩
  have hmatrix := congrArg
    (fun g : GLSymplecticFin m R =>
      ((g : GL (Fin (m + m)) R) : Matrix (Fin (m + m)) (Fin (m + m)) R)) hcomm
  simp only [Subgroup.coe_mul, Units.val_mul, coe_diagonal, diagGL_coe] at hmatrix
  exact apply_eq_zero_of_commute_diagonal hmatrix (fun h => ht (Units.ext h))

end Domain

section InfiniteField

variable [Field R] [Infinite R]

/-- Over an infinite field, the paired diagonal torus in the symplectic group is its own
centralizer. -/
theorem centralizer_range_diagonal_of_infinite :
    Subgroup.centralizer ((diagonal (m := m) (R := R)).range : Set (GLSymplecticFin m R)) =
      (diagonal (m := m) (R := R)).range := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset R)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  apply centralizer_range_diagonal (Units.mk0 a ha.1)
  intro h
  have heq : a = a⁻¹ := congrArg Units.val h
  have hsq : a ^ 2 = 1 := by
    calc
      a ^ 2 = a * a⁻¹ := by rw [pow_two, ← heq]
      _ = 1 := mul_inv_cancel₀ ha.1
  exact (sq_eq_one_iff.mp hsq).elim ha.2.1 ha.2.2

/-- Over an infinite field, every commutative subgroup containing the paired diagonal torus
is that torus. -/
theorem eq_range_diagonal_of_le_of_isMulCommutative
    (H : Subgroup (GLSymplecticFin m R)) [IsMulCommutative H]
    (hH : (diagonal (m := m) (R := R)).range ≤ H) :
    H = (diagonal (m := m) (R := R)).range :=
  Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative
    centralizer_range_diagonal_of_infinite hH

end InfiniteField

end TauCeti.GLSymplecticFin
