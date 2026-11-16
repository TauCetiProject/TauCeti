/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Finite-order elements, involutions, and trace rigidity in `SL(2, R)`

By the two-by-two Cayley–Hamilton identity (`Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two`),
every matrix `g ∈ SL(2, R)` satisfies `g ^ 2 = (trace g) • g - 1`. This characterizes both
square roots of `-1` and elements of order two:

* `g ^ 2 = -1` holds over any commutative ring if and only if `trace g = 0`
  (`Matrix.SpecialLinearGroup.sq_eq_neg_one_iff_trace_eq_zero`).
* Over a commutative ring without zero divisors in which `2 ≠ 0`, `g ^ 2 = 1` forces `g = ±1`
  (`Matrix.SpecialLinearGroup.sq_eq_one_iff`), so `-1` is the unique involution of `SL(2, R)`
  (`Matrix.SpecialLinearGroup.orderOf_eq_two_iff`). By Cauchy's theorem (and `-1 = 1` when
  `2 = 0`), every finite subgroup of `SL(2, R)` of even order over a ring without zero divisors
  contains `-1` and hence the center `{±1}`
  (`Matrix.SpecialLinearGroup.neg_one_mem_of_two_dvd_card`,
  `Matrix.SpecialLinearGroup.center_le_of_two_dvd_card`).
* Over a reduced commutative ring of exponential characteristic `p`, any element `g ∈ SL(2, R)`
  with `g ^ (p ^ k) = 1` has `trace g = 2`
  (`Matrix.SpecialLinearGroup.trace_eq_two_of_pow_expChar_pow_eq_one`).
* Over a reduced commutative ring in which `2` is left-regular, no nontrivial matrix of trace `2`
  in `SL(2, R)` commutes with a traceless matrix in `SL(2, R)`
  (`Matrix.SpecialLinearGroup.eq_one_of_commute_of_trace_eq_two_of_trace_eq_zero`).

## Main results

* `Matrix.SpecialLinearGroup.neg_one_eq_one_iff`, `Matrix.SpecialLinearGroup.neg_one_ne_one`:
  for nonempty even `n`, `-1 = 1` in `SL(n, R)` holds if and only if `(2 : R) = 0`.
* `Matrix.SpecialLinearGroup.sq_eq_neg_one_iff_trace_eq_zero`: `g ^ 2 = -1 ↔ trace g = 0`.
* `Matrix.SpecialLinearGroup.sq_eq_one_iff`: `g ^ 2 = 1 ↔ g = 1 ∨ g = -1`.
* `Matrix.SpecialLinearGroup.orderOf_eq_two_iff`: `orderOf g = 2 ↔ g = -1`.
* `Matrix.SpecialLinearGroup.neg_one_mem_of_two_dvd_card`,
  `Matrix.SpecialLinearGroup.center_le_of_two_dvd_card`: every finite subgroup of `SL(2, R)` of
  even order contains `-1` and the center.
* `Matrix.SpecialLinearGroup.trace_eq_two_of_pow_expChar_pow_eq_one`: an element of `SL(2, R)`
  killed by a power of the exponential characteristic has trace `2`.
* `Matrix.SpecialLinearGroup.eq_one_of_commute_of_trace_eq_two_of_trace_eq_zero`: an element of
  `SL(2, R)` of trace `2` commuting with a traceless element of `SL(2, R)` is `1`.
-/

public section

open Matrix
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

variable {R : Type*} [CommRing R]

/-- In `SL(n, R)` for nonempty even `n`, `-1 = 1` holds if and only if `(2 : R) = 0`. -/
@[simp]
theorem neg_one_eq_one_iff {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fact (Even (Fintype.card n))] :
    (-1 : SpecialLinearGroup n R) = 1 ↔ (2 : R) = 0 := by
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty n›
    have hi := congrArg (fun g : SpecialLinearGroup n R ↦ (g : Matrix n n R) i i) h
    simp only [coe_neg, coe_one, Matrix.neg_apply, Matrix.one_apply_eq] at hi
    linear_combination -hi
  · intro h2
    apply Subtype.ext
    ext i j
    simp only [coe_neg, coe_one, Matrix.neg_apply]
    linear_combination -((1 : Matrix n n R) i j) * h2

/-- In `SL(n, R)` for nonempty even `n`, `-1 ≠ 1` whenever `(2 : R) ≠ 0`. -/
theorem neg_one_ne_one {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    [Fact (Even (Fintype.card n))] [NeZero (2 : R)] :
    (-1 : SpecialLinearGroup n R) ≠ 1 :=
  neg_one_eq_one_iff.not.mpr (NeZero.ne 2)

/-- **Square roots of `-1` in `SL(2, R)` are the traceless matrices**: over any commutative ring,
`g ^ 2 = -1` holds if and only if `trace g = 0`, by the `2 × 2` Cayley–Hamilton identity
`g ^ 2 = (trace g) • g - 1`. -/
theorem sq_eq_neg_one_iff_trace_eq_zero (g : SL(2, R)) :
    g ^ 2 = -1 ↔ (g : Matrix (Fin 2) (Fin 2) R).trace = 0 := by
  set A : Matrix (Fin 2) (Fin 2) R := g.1
  have hch : A ^ 2 = A.trace • A - 1 := by
    simpa [A, g.det_coe] using Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two A
  constructor
  · intro hsq
    have hmat : A ^ 2 = -1 := by simpa [A, coe_pow] using congrArg Subtype.val hsq
    have hsmul : A.trace • A = 0 := by
      rw [hmat, eq_sub_iff_add_eq, neg_add_cancel] at hch
      exact hch.symm
    have hone : A.trace • (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
      calc A.trace • (1 : Matrix (Fin 2) (Fin 2) R)
          = (A.trace • A) * ((g⁻¹ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) := by
            rw [Matrix.smul_mul, ← coe_mul, mul_inv_cancel, coe_one]
        _ = 0 := by rw [hsmul, Matrix.zero_mul]
    simpa [A] using congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 0 0) hone
  · intro htr
    apply Subtype.ext
    rw [coe_pow, coe_neg, coe_one, hch, htr, zero_smul, zero_sub]

/-- **Square roots of `1` in `SL(2, R)` are `±1`**, over a commutative ring without zero divisors
and `(2 : R) ≠ 0`. Both hypotheses are needed: over `ZMod 2`, `!![1, 1; 0, 1]` squares to `1`,
and over `ZMod 15`, `!![4, 0; 0, 4]` squares to `1`. -/
@[simp]
theorem sq_eq_one_iff [NoZeroDivisors R] [NeZero (2 : R)] (g : SL(2, R)) :
    g ^ 2 = 1 ↔ g = 1 ∨ g = -1 := by
  refine ⟨fun hsq ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  set A : Matrix (Fin 2) (Fin 2) R := g.1
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
  have h2ne : (2 : R) ≠ 0 := NeZero.ne 2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hdet with htr | htr
  · left
    apply Subtype.ext
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M i j) htrA
    simp only [htr, Matrix.smul_apply, smul_eq_mul] at hij
    exact mul_left_cancel₀ h2ne hij
  · right
    apply Subtype.ext
    ext i j
    have hij := congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M i j) htrA
    simp only [htr, Matrix.smul_apply, smul_eq_mul, neg_mul] at hij
    have hneg : (2 : R) * A i j = (2 : R) * (-(1 : Matrix (Fin 2) (Fin 2) R)) i j := by
      simpa [Matrix.neg_apply] using congrArg Neg.neg hij
    simpa [coe_neg, coe_one] using mul_left_cancel₀ h2ne hneg

/-- **`-1` is the unique element of order `2` in `SL(2, R)`** over a commutative ring without zero
divisors and `(2 : R) ≠ 0`. -/
@[simp]
theorem orderOf_eq_two_iff [NoZeroDivisors R] [NeZero (2 : R)] (g : SL(2, R)) :
    orderOf g = 2 ↔ g = -1 := by
  constructor
  · intro hg
    have hsq : g ^ 2 = 1 := (congrArg (g ^ ·) hg.symm).trans (pow_orderOf_eq_one g)
    have hne : g ≠ 1 := fun h1 ↦ by simp [h1] at hg
    exact (sq_eq_one_iff g).mp hsq |>.resolve_left hne
  · rintro rfl
    exact orderOf_eq_prime (by simp) neg_one_ne_one

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
    exact hcoe ▸ x.2

/-- **Every finite subgroup of `SL(2, R)` of even order contains the center `{±1}`** over any
commutative ring without zero divisors. -/
theorem center_le_of_two_dvd_card [NoZeroDivisors R]
    {H : Subgroup SL(2, R)} [Finite H] (h : 2 ∣ Nat.card H) :
    Subgroup.center SL(2, R) ≤ H :=
  center_le_iff_neg_one_mem.mpr (neg_one_mem_of_two_dvd_card h)

/-- Over a reduced commutative ring of exponential characteristic `p`, every element `g ∈ SL(2, R)`
satisfying `g ^ (p ^ k) = 1` has `trace g = 2`.

Reducedness is needed: over `(ZMod 3)[ε]/(ε³)`, the diagonal matrix `diag(1 + ε, 1 - ε + ε²)` lies
in `SL(2, R)` and has cube `1`, but its trace is `2 + ε² ≠ 2`. -/
theorem trace_eq_two_of_pow_expChar_pow_eq_one [IsReduced R] {p : ℕ} [ExpChar R p] {k : ℕ}
    {g : SL(2, R)} (hg : g ^ p ^ k = 1) :
    (g : Matrix (Fin 2) (Fin 2) R).trace = 2 := by
  set A : Matrix (Fin 2) (Fin 2) R := g.1
  have hApow : A ^ p ^ k = 1 := by simpa [A, coe_pow] using congrArg Subtype.val hg
  have hsub : (1 - A) ^ p ^ k = 0 := by
    rw [sub_pow_expChar_pow_of_commute p k (Commute.one_left A), one_pow, hApow, sub_self]
  have hdetpow : (1 - A).det ^ p ^ k = 0 := by
    rw [← Matrix.det_pow, hsub, Matrix.det_zero]
  have hdet : (1 - A).det = 0 := eq_zero_of_pow_eq_zero hdetpow
  rw [Matrix.det_one_sub_eq_two_sub_trace_of_det_eq_one g.det_coe] at hdet
  exact (sub_eq_zero.mp hdet).symm

/-- **Trace rigidity for commuting matrices in `SL(2, R)`**: over a reduced commutative ring in
which `2` is left-regular, an element of `SL(2, R)` of trace `2` that commutes with a traceless
element of `SL(2, R)` must be `1`.

Both ring hypotheses are needed: over the dual numbers `ℚ[ε]/(ε²)` (not reduced), `1 + ε • B` has
trace `2` and commutes with the traceless matrix `B = !![0, -1; 1, 0]`; over `ZMod 6` (reduced,
but `2` is not left-regular), `(!![1, 1; 0, 1], 1)` and `(!![1, 1; 0, 1], !![0, -1; 1, 0])` in
`SL(2, ZMod 2) × SL(2, ZMod 3)` commute with traces `2` and `0`. -/
theorem eq_one_of_commute_of_trace_eq_two_of_trace_eq_zero [IsReduced R]
    (h2 : IsLeftRegular (2 : R)) {a b : SL(2, R)} (hcomm : Commute a b)
    (ha : (a : Matrix (Fin 2) (Fin 2) R).trace = 2)
    (hb : (b : Matrix (Fin 2) (Fin 2) R).trace = 0) : a = 1 := by
  set A : Matrix (Fin 2) (Fin 2) R := a.1
  set B : Matrix (Fin 2) (Fin 2) R := b.1
  set N : Matrix (Fin 2) (Fin 2) R := A - 1
  have hNtr : N.trace = 0 := by simp [N, A, ha]
  have hNdet : N.det = 0 := by
    have hneg : N = -(1 - A) := (neg_sub 1 A).symm
    rw [hneg, Matrix.det_neg, Fintype.card_fin, neg_one_sq, one_mul,
      Matrix.det_one_sub_eq_two_sub_trace_of_det_eq_one a.det_coe, ha, sub_self]
  have hNsq : N ^ 2 = 0 := by
    rw [Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two, hNtr, hNdet, zero_smul, zero_smul,
      sub_zero]
  have hcommNB : Commute N B := by
    refine Commute.sub_left ?_ (Commute.one_left B)
    simpa [Commute, SemiconjBy, A, B, coe_mul] using congrArg Subtype.val hcomm.eq
  -- Any two traceless `2 × 2` matrices satisfy `N * B + B * N = trace (N * B) • 1`.
  have hanti : N * B + B * N = (N * B).trace • (1 : Matrix (Fin 2) (Fin 2) R) := by
    have hN11 : N 1 1 = -N 0 0 :=
      eq_neg_of_add_eq_zero_right (by rwa [Matrix.trace_fin_two] at hNtr)
    have hB11 : B 1 1 = -B 0 0 :=
      eq_neg_of_add_eq_zero_right (by rwa [Matrix.trace_fin_two] at hb)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.trace_fin_two, Fin.sum_univ_two, hN11, hB11] <;> ring
  have htwoNB : (2 : R) • (N * B) = (N * B).trace • (1 : Matrix (Fin 2) (Fin 2) R) := by
    rw [two_smul, ← hanti, hcommNB.eq]
  have hNBtr : (N * B).trace = 0 := by
    have hsq : ((N * B).trace • (1 : Matrix (Fin 2) (Fin 2) R)) ^ 2 = 0 := by
      rw [← htwoNB, smul_pow, hcommNB.mul_pow, hNsq, Matrix.zero_mul, smul_zero]
    rw [smul_pow, one_pow] at hsq
    simpa using congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M 0 0) hsq
  rw [hNBtr, zero_smul] at htwoNB
  have htwoN : (2 : R) • N = 0 := by
    calc (2 : R) • N
        = ((2 : R) • (N * B)) * ((b⁻¹ : SL(2, R)) : Matrix (Fin 2) (Fin 2) R) := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, ← coe_mul, mul_inv_cancel, coe_one, Matrix.mul_one]
      _ = 0 := by rw [htwoNB, Matrix.zero_mul]
  exact Subtype.ext (sub_eq_zero.mp (Matrix.ext fun i j ↦ h2
    (by simpa [N, A] using congrArg (fun M : Matrix (Fin 2) (Fin 2) R ↦ M i j) htwoN)))

end Matrix.SpecialLinearGroup
