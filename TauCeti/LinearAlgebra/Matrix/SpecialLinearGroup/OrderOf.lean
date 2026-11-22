/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Finite-order elements and involutions in `SL(2, R)`

By the two-by-two Cayley–Hamilton identity (`Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two`),
every matrix `g ∈ SL(2, R)` satisfies `g ^ 2 = (trace g) • g - 1`. Over a commutative ring without
zero divisors in which `2 ≠ 0`, `g ^ 2 = 1` forces `g = ±1`
(`Matrix.SpecialLinearGroup.sq_eq_one_iff`), so `-1` is the unique involution of `SL(2, R)`
(`Matrix.SpecialLinearGroup.orderOf_eq_two_iff`). By Cauchy's theorem (and `-1 = 1` when
`2 = 0`), every finite subgroup of `SL(2, R)` of even order over a ring without zero divisors
contains `-1` and hence the center `{±1}`
(`Matrix.SpecialLinearGroup.neg_one_mem_of_two_dvd_card`,
`Matrix.SpecialLinearGroup.center_le_of_two_dvd_card`).

## Main results

* `Matrix.SpecialLinearGroup.sq_eq_one_iff`: `g ^ 2 = 1 ↔ g = 1 ∨ g = -1`.
* `Matrix.SpecialLinearGroup.orderOf_eq_two_iff`: `orderOf g = 2 ↔ g = -1`.
* `Matrix.SpecialLinearGroup.neg_one_mem_of_two_dvd_card`,
  `Matrix.SpecialLinearGroup.center_le_of_two_dvd_card`: every finite subgroup of `SL(2, R)` of
  even order contains `-1` and the center.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- **Square roots of `1` in `SL(2, R)` are `±1`**, over a commutative ring without zero divisors
and `(2 : R) ≠ 0`. Both hypotheses are needed: over `ZMod 2`, `!![1, 1; 0, 1]` squares to `1`,
and over `ZMod 15`, `!![4, 0; 0, 4]` squares to `1`. -/
@[simp]
theorem sq_eq_one_iff [NoZeroDivisors R] [NeZero (2 : R)] (g : SL(2, R)) :
    g ^ 2 = 1 ↔ g = 1 ∨ g = -1 := by
  refine ⟨fun hsq ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  set A : Matrix (Fin 2) (Fin 2) R := g.val
  have hch : A ^ 2 = A.trace • A - 1 := by
    simpa [A, g.det_coe] using Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two A
  have hmat : A ^ 2 = 1 := by simpa [A, coe_pow] using congrArg Subtype.val hsq
  have htrA : A.trace • A = (2 : R) • (1 : Matrix (Fin 2) (Fin 2) R) := by
    rw [hmat] at hch
    have h1 : A.trace • A = (1 : Matrix (Fin 2) (Fin 2) R) + 1 := eq_add_of_sub_eq hch.symm
    rw [h1, two_smul]
  have hdet : A.trace ^ 2 = (2 : R) ^ 2 := by
    have hd := congrArg Matrix.det htrA
    simpa [Matrix.det_smul, g.det_coe, A] using hd
  have hreg : IsSMulRegular (Matrix (Fin 2) (Fin 2) R) (2 : R) :=
    (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (NeZero.ne (2 : R))).matrix
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdet with htr | htr
  · exact Or.inl (Subtype.ext (hreg (by simpa [htr] using htrA)))
  · exact Or.inr (Subtype.ext (hreg
      (by simpa [htr, neg_smul, ← smul_neg, coe_neg, coe_one] using congrArg Neg.neg htrA)))

/-- **`-1` is the unique element of order `2` in `SL(2, R)`** over a commutative ring without zero
divisors and `(2 : R) ≠ 0`. -/
@[simp]
theorem orderOf_eq_two_iff [NoZeroDivisors R] [NeZero (2 : R)] (g : SL(2, R)) :
    orderOf g = 2 ↔ g = -1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, sq_eq_one_iff]
  simp +contextual [or_and_right, NeZero.ne]

/-- **Every finite subgroup of `SL(2, R)` of even order contains `-1`** over any commutative ring
without zero divisors: if `(2 : R) = 0` then `-1 = 1 ∈ H`, and otherwise Cauchy's theorem produces
an element of order `2`, which must be `-1`.

The finiteness hypothesis is needed: for an infinite subgroup such as the upper unitriangular
matrices in `SL(2, ℤ)`, `Nat.card H = 0` is divisible by `2` while `-1 ∉ H`. -/
theorem neg_one_mem_of_two_dvd_card [NoZeroDivisors R]
    {H : Subgroup SL(2, R)} [Finite H] (h : 2 ∣ Nat.card H) :
    (-1 : SL(2, R)) ∈ H := by
  by_cases h2 : (2 : R) = 0
  · rw [neg_one_eq_one_iff.mpr h2]
    exact H.one_mem
  · have : NeZero (2 : R) := ⟨h2⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h
    have hcoe : orderOf (x : SL(2, R)) = 2 := (Subgroup.orderOf_coe x).trans hx
    rw [orderOf_eq_two_iff] at hcoe
    exact hcoe ▸ x.property

/-- **Every finite subgroup of `SL(2, R)` of even order contains the center `{±1}`** over any
commutative ring without zero divisors. -/
theorem center_le_of_two_dvd_card [NoZeroDivisors R]
    {H : Subgroup SL(2, R)} [Finite H] (h : 2 ∣ Nat.card H) :
    Subgroup.center SL(2, R) ≤ H :=
  center_le_iff_neg_one_mem.mpr (neg_one_mem_of_two_dvd_card h)

end Matrix.SpecialLinearGroup
