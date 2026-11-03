/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Joseph
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Mul
public import TauCeti.Algebra.Ring.Commutator
import Mathlib.Tactic.NoncommRing

/-!
# Nested commutators of square-zero unipotents

Let `A`, `B` and `C` be square-zero integral matrices with `⁅A, C⁆ = 0`, `⁅⁅A, B⁆, C⁆ = A`,
`⁅A, ⁅A, B⁆⁆ = 0` and `⁅B, ⁅B, A⁆⁆ = 0`, the relations between the root vectors `e_α`, `e_β` and
`e_{-β}` of two adjacent simple roots acting on a minuscule weight basis. Over every commutative
ring `R`, the unipotent units `x = 1 + u • A`, `y = 1 + v • B` and `z = 1 + w • C` then satisfy
`↑⁅⁅x, y⁆, z⁆ = 1 + (u * v * w) • A`. In particular, taking `v = w = 1` gives `⁅⁅x, y⁆, z⁆ = x`.

The hypotheses are stated over `ℤ`, where the identity `⁅A, ⁅A, B⁆⁆ = -2 (A * B * A)` for a
square-zero `A` can be divided by two, so the conclusion also holds in characteristic two.

## Main results

* `Matrix.mul_mul_eq_zero_of_mul_self_eq_zero_of_lie_lie_eq_zero`: for integral matrices,
  `A * A = 0` and `⁅A, ⁅A, B⁆⁆ = 0` give `A * B * A = 0`.
* `Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul`: the nested commutator
  identity `↑⁅⁅x, y⁆, z⁆ = 1 + (u * v * w) • A` for the unipotent units above.
-/

public section

open scoped commutatorElement

namespace Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For integral matrices, `A * A = 0` and `⁅A, ⁅A, B⁆⁆ = 0` force `A * B * A = 0`: the nested
bracket equals `-2 (A * B * A)`, and integer entries have no two-torsion. -/
theorem mul_mul_eq_zero_of_mul_self_eq_zero_of_lie_lie_eq_zero (A B : Matrix ι ι ℤ)
    (hA : A * A = 0) (hAB : ⁅A, ⁅A, B⁆⁆ = 0) : A * B * A = 0 := by
  have hpoly : ⁅A, ⁅A, B⁆⁆ = A * A * B + B * (A * A) - (A * B * A + A * B * A) := by
    simp only [Ring.lie_def]
    noncomm_ring
  rw [hpoly, hA, zero_mul, mul_zero, zero_add, zero_sub, neg_eq_zero] at hAB
  ext a b
  have hentry := congrFun (congrFun hAB a) b
  simp only [Matrix.add_apply, Matrix.zero_apply] at hentry ⊢
  omega

/-- The products of `A`, `B`, `C` and `⁅A, B⁆` that vanish under the adjacent-root relations. -/
private theorem mul_eq_zero_relations_of_lie_lie_eq_zero (A B C : Matrix ι ι ℤ)
    (hA : A * A = 0) (hB : B * B = 0) (hC : C * C = 0)
    (hAC : ⁅A, C⁆ = 0) (hABC : ⁅⁅A, B⁆, C⁆ = A)
    (hAAB : ⁅A, ⁅A, B⁆⁆ = 0) (hBBA : ⁅B, ⁅B, A⁆⁆ = 0) :
    A * B * A = 0 ∧ B * A * B = 0 ∧ ⁅A, B⁆ * ⁅A, B⁆ = 0 ∧
      ⁅A, B⁆ * C * ⁅A, B⁆ = 0 ∧ C * ⁅A, B⁆ * C = 0 := by
  have hABA := mul_mul_eq_zero_of_mul_self_eq_zero_of_lie_lie_eq_zero A B hA hAAB
  have hBAB := mul_mul_eq_zero_of_mul_self_eq_zero_of_lie_lie_eq_zero B A hB hBBA
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
    mul_mul_eq_zero_of_mul_self_eq_zero_of_lie_lie_eq_zero ⁅A, B⁆ C hD hDDC,
    mul_mul_eq_zero_of_mul_self_eq_zero_of_lie_lie_eq_zero C ⁅A, B⁆ hC hCCD⟩

/-- **Nested commutator of square-zero unipotents.** Let `A`, `B` and `C` be square-zero integral
matrices with `⁅A, C⁆ = 0`, `⁅⁅A, B⁆, C⁆ = A`, `⁅A, ⁅A, B⁆⁆ = 0` and `⁅B, ⁅B, A⁆⁆ = 0`. Over any
commutative ring, the units `x = 1 + u • A`, `y = 1 + v • B` and `z = 1 + w • C` satisfy
`↑⁅⁅x, y⁆, z⁆ = 1 + (u * v * w) • A`. -/
theorem coe_commutatorElement_commutatorElement_eq_one_add_smul (A B C : Matrix ι ι ℤ)
    (hA : A * A = 0) (hB : B * B = 0) (hC : C * C = 0)
    (hAC : ⁅A, C⁆ = 0) (hABC : ⁅⁅A, B⁆, C⁆ = A)
    (hAAB : ⁅A, ⁅A, B⁆⁆ = 0) (hBBA : ⁅B, ⁅B, A⁆⁆ = 0)
    {R : Type*} [CommRing R] (u v w : R) (x y z : (Matrix ι ι R)ˣ)
    (hx : (x : Matrix ι ι R) = 1 + u • A.map (Int.cast : ℤ → R))
    (hy : (y : Matrix ι ι R) = 1 + v • B.map (Int.cast : ℤ → R))
    (hz : (z : Matrix ι ι R) = 1 + w • C.map (Int.cast : ℤ → R)) :
    (↑⁅⁅x, y⁆, z⁆ : Matrix ι ι R) = 1 + (u * v * w) • A.map (Int.cast : ℤ → R) := by
  let f : Matrix ι ι ℤ →+* Matrix ι ι R := (Int.castRingHom R).mapMatrix
  have hf (X : Matrix ι ι ℤ) : f X = X.map (Int.cast : ℤ → R) := by
    ext a b
    simp only [f, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  have hlie (X Y : Matrix ι ι ℤ) : f ⁅X, Y⁆ = ⁅f X, f Y⁆ := by
    simp only [Ring.lie_def, map_sub, map_mul]
  obtain ⟨hABA, hBAB, hD, hDCD, hCDC⟩ :=
    mul_eq_zero_relations_of_lie_lie_eq_zero A B C hA hB hC hAC hABC hAAB hBBA
  rw [← hf] at hx hy hz
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
  have hcomm : (↑⁅x, y⁆ : Matrix ι ι R) = 1 + (u * v) • f ⁅A, B⁆ := by
    rw [Units.val_commutatorElement_eq_one_add_lie x y (u • f A) (v • f B) hx hy]
    · rw [smul_lie, lie_smul, smul_smul, ← hlie]
    · simp only [smul_mul_assoc, mul_smul_comm, hAA, smul_zero]
    · simp only [smul_mul_assoc, mul_smul_comm, hBB, smul_zero]
    · simp only [smul_mul_assoc, mul_smul_comm, hABA', smul_zero]
    · simp only [smul_mul_assoc, mul_smul_comm, hBAB', smul_zero]
  rw [Units.val_commutatorElement_eq_one_add_lie ⁅x, y⁆ z
    ((u * v) • f ⁅A, B⁆) (w • f C) hcomm hz]
  · rw [smul_lie, lie_smul, smul_smul, hDC, hf]
  · simp only [smul_mul_assoc, mul_smul_comm, hDD, smul_zero]
  · simp only [smul_mul_assoc, mul_smul_comm, hCC, smul_zero]
  · simp only [smul_mul_assoc, mul_smul_comm, hDCD', smul_zero]
  · simp only [smul_mul_assoc, mul_smul_comm, hCDC', smul_zero]

end Matrix
