/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Stabilizers of nonzero vectors in `SL(2, R)` are commutative

Over a commutative ring `R` without zero divisors, an element `A ∈ SL(2, R)` fixing a nonzero
column vector `v` has trace `2`: `1 - A` kills `v`, so `det (1 - A) = 2 - tr A` vanishes. Two
such elements `A = 1 + N` and `B = 1 + M` fixing the same `v` commute: the `2 × 2` minors
comparing the entries of `N` and `M` vanish after multiplication by either coordinate of `v`,
hence vanish, and together with `tr N = tr M = 0` they force `N M = M N`.

Over `ℤ` the stabilizer of a nonzero vector is therefore a commutative, hence amenable, subgroup
of `SL(2, ℤ)`. This is what makes every orbit of a nonamenable subgroup on `ℤ² \ {0}` infinite.

## Main statements

* `Matrix.SpecialLinearGroup.trace_eq_two_of_smul_eq_self`: an element of `SL(2, R)` fixing a
  nonzero vector has trace `2`.
* `Matrix.SpecialLinearGroup.commute_of_smul_eq_self`: two elements of `SL(2, R)` fixing the
  same nonzero vector commute.
* `Matrix.SpecialLinearGroup.isMulCommutative_stabilizer`: the stabilizer of a nonzero vector in
  `SL(2, R)` is commutative.
-/

public section

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R] [NoZeroDivisors R]

/-- An element of `R` whose products with both coordinates of a nonzero vector vanish is zero. -/
private theorem eq_zero_of_mul_eq_zero_of_ne_zero {v : Fin 2 → R} (hv : v ≠ 0) {e : R}
    (h0 : v 0 * e = 0) (h1 : v 1 * e = 0) : e = 0 :=
  (smul_eq_zero.1 (funext fun i => by fin_cases i <;> simp [mul_comm e, h0, h1])).resolve_right hv

/-- An element of `SL(2, R)` fixing a nonzero vector has trace `2`. -/
theorem trace_eq_two_of_smul_eq_self {v : Fin 2 → R} (hv : v ≠ 0) {A : SL(2, R)}
    (hA : A • v = v) : (A : Matrix (Fin 2) (Fin 2) R).trace = 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv
  have : Nontrivial R := nontrivial_of_ne _ _ hi
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  have hdet : (1 - (A : Matrix (Fin 2) (Fin 2) R)).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.smul_eq_mulVec,
      ← SpecialLinearGroup.smul_def, hA, sub_self]
  rw [Matrix.det_one_sub_eq_two_sub_trace_of_det_eq_one A.det_coe] at hdet
  exact (sub_eq_zero.1 hdet).symm

/-- Two elements of `SL(2, R)` fixing the same nonzero vector commute. -/
theorem commute_of_smul_eq_self {v : Fin 2 → R} (hv : v ≠ 0) {A B : SL(2, R)}
    (hA : A • v = v) (hB : B • v = v) : Commute A B := by
  have tA := trace_eq_two_of_smul_eq_self hv hA
  have tB := trace_eq_two_of_smul_eq_self hv hB
  rw [Matrix.trace_fin_two] at tA tB
  have hA0 := congrFun hA 0
  have hA1 := congrFun hA 1
  have hB0 := congrFun hB 0
  have hB1 := congrFun hB 1
  simp only [SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] at hA0 hA1 hB0 hB1
  have hE1 : (A 0 0 - 1) * B 0 1 - (B 0 0 - 1) * A 0 1 = 0 :=
    eq_zero_of_mul_eq_zero_of_ne_zero hv
      (by linear_combination B 0 1 * hA0 - A 0 1 * hB0)
      (by linear_combination (A 0 0 - 1) * hB0 - (B 0 0 - 1) * hA0)
  have hE2 : A 1 0 * (B 0 0 - 1) - (A 0 0 - 1) * B 1 0 = 0 :=
    eq_zero_of_mul_eq_zero_of_ne_zero hv
      (by linear_combination (B 0 0 - 1) * (hA1 - v 1 * tA) - (A 0 0 - 1) * (hB1 - v 1 * tB))
      (by linear_combination -A 1 0 * (hB1 - v 1 * tB) + B 1 0 * (hA1 - v 1 * tA))
  have hE3 : A 0 1 * B 1 0 - B 0 1 * A 1 0 = 0 :=
    eq_zero_of_mul_eq_zero_of_ne_zero hv
      (by linear_combination A 0 1 * (hB1 - v 1 * tB) - B 0 1 * (hA1 - v 1 * tA) - v 1 * hE1)
      (by linear_combination B 1 0 * hA0 - A 1 0 * hB0 + v 0 * hE2)
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;>
    simp only [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one]
  · linear_combination hE3
  · linear_combination 2 * hE1 + A 0 1 * tB - B 0 1 * tA
  · linear_combination 2 * hE2 - A 1 0 * tB + B 1 0 * tA
  · linear_combination -hE3

/-- The stabilizer of a nonzero vector in `SL(2, R)` is commutative. -/
theorem isMulCommutative_stabilizer {v : Fin 2 → R} (hv : v ≠ 0) :
    IsMulCommutative (MulAction.stabilizer SL(2, R) v) :=
  ⟨⟨fun A B => Subtype.ext (commute_of_smul_eq_self hv A.property B.property).eq⟩⟩

end Matrix.SpecialLinearGroup
