/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Mul
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Square-zero rank-two commutator calculations

Integral square-zero Serre matrices satisfy sandwich identities that can be transported to
any coefficient ring, including characteristic two. The cancellation by two is performed
only on integer entries. The resulting ring identities compute group commutators of units
whose matrices are one plus a square-zero operator.
-/

public section

open scoped commutatorElement

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem sandwich_eq_zero_of_lie_lie_eq_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℤ) (hA : A * A = 0)
    (hAB : ⁅A, ⁅A, B⁆⁆ = 0) : A * B * A = 0 := by
  have hpoly : ⁅A, ⁅A, B⁆⁆ = A * A * B + B * (A * A) - (A * B * A + A * B * A) := by
    simp only [Ring.lie_def]
    noncomm_ring
  rw [hpoly, hA, zero_mul, mul_zero, zero_add, zero_sub, neg_eq_zero] at hAB
  ext a b
  have hentry := congrFun (congrFun hAB a) b
  simp only [Matrix.add_apply, Matrix.zero_apply] at hentry ⊢
  omega

/-- The integral rank-two relations give the square and sandwich identities needed for
nested unipotent commutators. Cancellation by two is confined to integer matrices. -/
private theorem matrix_rankTwo_squareZero_relations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℤ) (hA : A * A = 0) (hB : B * B = 0) (hC : C * C = 0)
    (hAC : ⁅A, C⁆ = 0) (hABC : ⁅⁅A, B⁆, C⁆ = A)
    (hAAB : ⁅A, ⁅A, B⁆⁆ = 0) (hBBA : ⁅B, ⁅B, A⁆⁆ = 0) :
    A * B * A = 0 ∧ B * A * B = 0 ∧ ⁅A, B⁆ * ⁅A, B⁆ = 0 ∧
      ⁅A, B⁆ * C * ⁅A, B⁆ = 0 ∧ C * ⁅A, B⁆ * C = 0 := by
  have hABA := sandwich_eq_zero_of_lie_lie_eq_zero A B hA hAAB
  have hBAB := sandwich_eq_zero_of_lie_lie_eq_zero B A hB hBBA
  have hD : ⁅A, B⁆ * ⁅A, B⁆ = 0 := by
    calc
      ⁅A, B⁆ * ⁅A, B⁆ = (A * B * A) * B - A * (B * B) * A -
          B * (A * A) * B + (B * A * B) * A := by
        simp only [Ring.lie_def]
        noncomm_ring
      _ = 0 := by rw [hABA, hBAB, hA, hB]; simp
  have hDDC : ⁅⁅A, B⁆, ⁅⁅A, B⁆, C⁆⁆ = 0 := by
    rw [hABC, ← lie_skew, hAAB, neg_zero]
  have hCCD : ⁅C, ⁅C, ⁅A, B⁆⁆⁆ = 0 := by
    rw [← lie_skew C ⁅A, B⁆, hABC, lie_neg, ← lie_skew C A, hAC, neg_zero, neg_zero]
  exact ⟨hABA, hBAB, hD,
    sandwich_eq_zero_of_lie_lie_eq_zero ⁅A, B⁆ C hD hDDC,
    sandwich_eq_zero_of_lie_lie_eq_zero C ⁅A, B⁆ hC hCCD⟩

private theorem coe_inv_eq_one_sub {S : Type*} [Ring S] (u : Sˣ) (A : S)
    (hu : (u : S) = 1 + A) (hA : A * A = 0) : (↑u⁻¹ : S) = 1 - A := by
  have hmul : (u : S) * (1 - A) = 1 := by
    rw [hu]
    calc
      (1 + A) * (1 - A) = 1 - A * A := by noncomm_ring
      _ = 1 := by rw [hA, sub_zero]
  calc
    (↑u⁻¹ : S) = (↑u⁻¹ : S) * ((u : S) * (1 - A)) := by rw [hmul, mul_one]
    _ = 1 - A := by simp [← mul_assoc]

/-- For square-zero operators with vanishing sandwiches, the group commutator of `1+A`
and `1+B` is `1+[A,B]`. This formula is valid in every ring. -/
theorem coe_commutator_eq_one_add_lie {S : Type*} [Ring S] (u v : Sˣ) (A B : S)
    (hu : (u : S) = 1 + A) (hv : (v : S) = 1 + B)
    (hA : A * A = 0) (hB : B * B = 0) (hABA : A * B * A = 0)
    (hBAB : B * A * B = 0) : (↑⁅u, v⁆ : S) = 1 + ⁅A, B⁆ := by
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul,
    coe_inv_eq_one_sub u A hu hA, coe_inv_eq_one_sub v B hv hB, hu, hv, Ring.lie_def]
  calc
    (1 + A) * (1 + B) * (1 - A) * (1 - B) =
        1 + A * B - B * A - A * A - B * B - A * (B * B) + (A * A) * B -
          A * B * A + B * A * B + (A * B * A) * B := by noncomm_ring
    _ = 1 + (A * B - B * A) := by rw [hA, hB, hABA, hBAB]; simp [sub_eq_add_neg, add_assoc]

/-- An integral rank-two configuration gives a nested unipotent commutator over every
commutative ring. All torsion cancellation occurs before the matrices are mapped out of `ℤ`. -/
theorem coe_nested_commutator_eq_one_add_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B C : Matrix ι ι ℤ) (hA : A * A = 0) (hB : B * B = 0) (hC : C * C = 0)
    (hAC : ⁅A, C⁆ = 0) (hABC : ⁅⁅A, B⁆, C⁆ = A)
    (hAAB : ⁅A, ⁅A, B⁆⁆ = 0) (hBBA : ⁅B, ⁅B, A⁆⁆ = 0)
    {R : Type*} [CommRing R] (u : R) (x y z : (Matrix ι ι R)ˣ)
    (hx : (x : Matrix ι ι R) = 1 + u • A.map (Int.cast : ℤ → R))
    (hy : (y : Matrix ι ι R) = 1 + B.map (Int.cast : ℤ → R))
    (hz : (z : Matrix ι ι R) = 1 + C.map (Int.cast : ℤ → R)) :
    (↑⁅⁅x, y⁆, z⁆ : Matrix ι ι R) = 1 + u • A.map (Int.cast : ℤ → R) := by
  let f : Matrix ι ι ℤ →+* Matrix ι ι R := (Int.castRingHom R).mapMatrix
  have hlie (X Y : Matrix ι ι ℤ) : f ⁅X, Y⁆ = ⁅f X, f Y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  obtain ⟨hABA, hBAB, hD, hDCD, hCDC⟩ :=
    matrix_rankTwo_squareZero_relations A B C hA hB hC hAC hABC hAAB hBBA
  have hAA : f A * f A = 0 := by rw [← map_mul, hA, map_zero]
  have hBB : f B * f B = 0 := by rw [← map_mul, hB, map_zero]
  have hCC : f C * f C = 0 := by rw [← map_mul, hC, map_zero]
  have hABA' : f A * f B * f A = 0 := by rw [← map_mul, ← map_mul, hABA, map_zero]
  have hBAB' : f B * f A * f B = 0 := by rw [← map_mul, ← map_mul, hBAB, map_zero]
  have hDD : f ⁅A, B⁆ * f ⁅A, B⁆ = 0 := by rw [← map_mul, hD, map_zero]
  have hDCD' : f ⁅A, B⁆ * f C * f ⁅A, B⁆ = 0 := by
    rw [← map_mul, ← map_mul, hDCD, map_zero]
  have hCDC' : f C * f ⁅A, B⁆ * f C = 0 := by
    rw [← map_mul, ← map_mul, hCDC, map_zero]
  have hDC : ⁅f ⁅A, B⁆, f C⁆ = f A := by rw [← hlie, hABC]
  have hcomm : (↑⁅x, y⁆ : Matrix ι ι R) = 1 + u • f ⁅A, B⁆ := by
    rw [coe_commutator_eq_one_add_lie x y (u • f A) (f B) hx hy]
    · rw [smul_lie, ← hlie]
    · simp only [smul_mul_assoc, mul_smul_comm, hAA, smul_zero]
    · exact hBB
    · simp only [smul_mul_assoc, mul_smul_comm, hABA', smul_zero]
    · simp only [smul_mul_assoc, mul_smul_comm, hBAB', smul_zero]
  rw [coe_commutator_eq_one_add_lie ⁅x, y⁆ z (u • f ⁅A, B⁆) (f C) hcomm hz]
  · rw [smul_lie, hDC]
    rfl
  · simp only [smul_mul_assoc, mul_smul_comm, hDD, smul_zero]
  · exact hCC
  · simp only [smul_mul_assoc, mul_smul_comm, hDCD', smul_zero]
  · simp only [smul_mul_assoc, mul_smul_comm, hCDC', smul_zero]

end TauCeti
