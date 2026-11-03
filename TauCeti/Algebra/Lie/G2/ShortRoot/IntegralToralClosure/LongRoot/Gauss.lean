/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# Opposite long-root factorization in the seven-dimensional G₂ carrier

The numbered long simple root is Bourbaki node `1`. Its positive and negative root
subgroups satisfy the rank-one Gauss relation, with simple-coroot factor the existing
weight-torus point at `![1, u]`. Both multiplication orders are given, requiring only
that `1 + a * b` is a unit. Neither root parameter need be invertible, and the coefficient
ring may be nonreduced.

The proofs use the explicit matrices in `IntegralToralClosure.Basic`: the long-root
operators act on two two-dimensional blocks, with the other three coordinates fixed.
No identification of the toral closure with an independently pinned simply connected
G₂ group scheme is asserted; transfer to such a group requires that identification.

## Main results

* `TauCeti.G2ShortRoot.IntegralToralClosure.rootSubgroupPoints_long_mul_opposite`:
  positive times negative, collected in negative–torus–positive order.
* `TauCeti.G2ShortRoot.IntegralToralClosure.rootSubgroupPoints_opposite_mul_long`:
  the reverse order, collected in positive–torus–negative order.

## References

R. W. Carter, *Simple Groups of Lie Type*, §6.1, for the rank-one relations.
The carrier and matrix conventions are those of
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot.IntegralToralClosure

universe v

variable {A : Type v} [CommRing A]

private theorem coe_longCoroot (u : Aˣ) :
    ((weightTorusPoints A ![1, u] : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      Matrix.diagonal ![1, (u : A), (↑u⁻¹ : A), 1, (u : A), (↑u⁻¹ : A), 1] := by
  rw [coe_weightTorusPoints_eq_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [torusCharacter_def, Fin.prod_univ_two, weight_apply]

/-- Gauss factorization for the positive and negative long simple-root points.
The unit `u` represents `1 + a * b`; the torus factor is the long simple coroot at `u`.
Only `1 + a * b`, not either root parameter, must be invertible. -/
theorem rootSubgroupPoints_long_mul_opposite (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        weightTorusPoints A ![1, u] *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  have hinv : (u : A) * (↑u⁻¹ : A) = 1 := u.mul_inv
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_inl_one,
    coe_rootSubgroupPoints_inr_one, coe_longCoroot]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ] <;> grind

/-- Gauss factorization in the reverse order at the long simple root.
The middle factor is the long simple coroot at `u⁻¹`, where `u = 1 + a * b`. -/
theorem rootSubgroupPoints_opposite_mul_long (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        weightTorusPoints A ![1, u⁻¹] *
        rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  have hinv : (u : A) * (↑u⁻¹ : A) = 1 := u.mul_inv
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_inl_one,
    coe_rootSubgroupPoints_inr_one, coe_longCoroot, inv_inv]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ] <;> grind

end TauCeti.G2ShortRoot.IntegralToralClosure
