/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.VertexOperator
public import TauCeti.RingTheory.LaurentSeries.HahnModuleDerivative
public import Mathlib.Algebra.Lie.OfAssociative
import TauCeti.Data.Nat.Choose.Sum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Formal derivatives of vertex operators

The formal derivative of a field is again a field: differentiating a Laurent series lowers
its lower bound by at most one. In normalized mode indexing its coefficients are
`(∂A)[[n]] = -n • A[[n - 1]]`, and iterated differentiation scales negative modes by ascending
factorials (`VertexOperator.ncoeff_iterate_derivative_neg`, so `((∂ᵏ A)[[-1]]) = k! • A[[-k - 1]]`)
and nonnegative modes by signed descending factorials
(`VertexOperator.ncoeff_iterate_derivative_natCast`).
This construction is linear over the coefficient ring and requires no characteristic-zero
assumption.

Differentiation preserves mutual locality, increasing a locality bound by one. More generally,
iterated derivatives in the two variables increase the bound by the sum of their orders.
Differentiation also preserves translation covariance `[T, A[[m]]] = (∂A)[[m]]` and annihilation of
a vector by nonnegative modes. For a field `B` covariant with `T` satisfying `T vac = 0`, its
negative modes on `vac` satisfy `k! • (B[[-k - 1]]) vac = (T ^ k) ((B[[-1]]) vac)`, and when `V`
has unique additive divisibility its nonnegative modes annihilate `vac` so its action on `vac` is
determined by mode `-1` (`VertexOperator.ncoeff_apply_eq_of_lie_eq_derivative`).

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §2.1 and §2.3.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §1.2.
-/

public section

noncomputable section

open Finset

namespace VertexOperator

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Formal differentiation of fields, defined on Laurent coefficients by
`(∂A).coeff n = (n + 1) • A.coeff (n + 1)`. -/
def derivative : VertexOperator R V →ₗ[R] VertexOperator R V :=
  LinearMap.compRight R (HahnModule.derivative R)

/-- Applying the derivative of a field differentiates its value as a Laurent series. -/
@[simp]
theorem derivative_apply (A : VertexOperator R V) (v : V) :
    derivative A v = HahnModule.derivative R (A v) := (rfl)

/-- The formal derivative of the identity field is zero. -/
@[simp]
theorem derivative_id : derivative (VertexOperator.id : VertexOperator R V) = 0 := by
  ext v
  simp

-- As with Mathlib's coefficient API, this is not a simp lemma: the simp normal form
-- uses normalized coefficients instead.
/-- Differentiation shifts the unnormalized Laurent coefficients down by one. -/
theorem coeff_derivative (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (derivative A) n = (n + 1) • HVertexOperator.coeff A (n + 1) := by
  ext v
  simpa only [derivative, LinearMap.compRight_apply, LinearMap.comp_apply,
    HVertexOperator.coeff_apply_apply, LinearMap.smul_apply] using
    HahnModule.coeff_derivative (A v) n

/-- The normalized modes of the derivative are `(∂A)₍ₙ₎ = -n A₍ₙ₋₁₎`. -/
@[simp]
theorem ncoeff_derivative (A : VertexOperator R V) (n : ℤ) :
    (derivative A)[[n]] = (-n) • A[[n - 1]] := by
  simp only [ncoeff_apply, coeff_derivative]
  have h₁ : -n - 1 + 1 = -n := by omega
  have h₂ : -(n - 1) - 1 = -n := by omega
  rw [h₁, h₂]

/-- Iterated differentiation scales negative normalized modes by an ascending factorial:
`(∂ᵏ A)₍₋ᵣ₋₁₎ = (r + 1)(r + 2)⋯(r + k) A₍₋ᵣ₋ₖ₋₁₎`. -/
theorem ncoeff_iterate_derivative_neg (A : VertexOperator R V) (k r : ℕ) :
    ((derivative (R := R) (V := V))^[k] A)[[-r - 1]] =
      (r + 1).ascFactorial k • A[[-(r + k : ℕ) - 1]] := by
  induction k generalizing A with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (derivative A), ncoeff_derivative]
    have h₁ : -((r + k : ℕ) : ℤ) - 1 - 1 = -((r + (k + 1) : ℕ) : ℤ) - 1 := by omega
    have h₂ : -(-((r + k : ℕ) : ℤ) - 1) = ((r + 1 + k : ℕ) : ℤ) := by omega
    rw [h₁, h₂, natCast_zsmul, smul_smul, mul_comm, ← Nat.ascFactorial_succ]

/-- Iterated differentiation scales nonnegative normalized modes by a signed descending factorial:
`(∂ᵏ A)₍ᵣ₎ = (-1)ᵏ r(r - 1)⋯(r - k + 1) A₍ᵣ₋ₖ₎` (vanishing when `r < k`). -/
theorem ncoeff_iterate_derivative_natCast (A : VertexOperator R V) (k r : ℕ) :
    ((derivative (R := R) (V := V))^[k] A)[[(r : ℤ)]] =
      (-1 : ℤ) ^ k • r.descFactorial k • A[[(r : ℤ) - k]] := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ncoeff_derivative]
    cases r with
    | zero => simp
    | succ s =>
      have hs : ((s + 1 : ℕ) : ℤ) - 1 = s := by omega
      have hsub : (s : ℤ) - k = ((s + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) := by omega
      rw [hs, ih s, hsub, neg_zsmul, natCast_zsmul, pow_succ', mul_zsmul, neg_one_zsmul,
        Nat.succ_descFactorial_succ, mul_nsmul, smul_comm (s + 1) ((-1 : ℤ) ^ k),
        smul_comm (s + 1) (s.descFactorial k)]

/-- The mode `(-1)` of the `k`-th derivative is `k! • A₍₋ₖ₋₁₎`. -/
@[simp]
theorem ncoeff_neg_one_iterate_derivative (A : VertexOperator R V) (k : ℕ) :
    ((derivative (R := R) (V := V))^[k] A)[[-1]] = k.factorial • A[[-k - 1]] := by
  simpa using ncoeff_iterate_derivative_neg A k 0

namespace IsLocalOfOrder

variable {A B : VertexOperator R V} {N : ℕ}

/-- Differentiating the first field increases a locality bound by one. -/
theorem derivative_left (h : A.IsLocalOfOrder B N) :
    (derivative A).IsLocalOfOrder B (N + 1) := by
  rw [isLocalOfOrder_iff]
  intro m n
  -- The derivative sum is -m times the shifted order-(N+1) sum, minus the
  -- binomially weighted sum. The latter is (N+1) times the order-N sum.
  have hweighted : ∑ ij ∈ antidiagonal (N + 1), (N + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
      (ij.1 : ℤ) • (A[[m + ij.1 - 1]] * B[[n + ij.2]] -
        B[[n + ij.2]] * A[[m + ij.1 - 1]]) = 0 := by
    simp_rw [natCast_zsmul, smul_comm ((-1 : ℤ) ^ _) (_ : ℕ)]
    rw [sum_antidiagonal_choose_succ_nsmul_nsmul (fun i j ↦ (-1 : ℤ) ^ j •
      (A[[m + i - 1]] * B[[n + j]] - B[[n + j]] * A[[m + i - 1]])) N]
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc, add_sub_cancel_right, smul_zero] using
      congrArg (fun x ↦ (N + 1) • x) (isLocalOfOrder_iff.mp h m n)
  have e : ∀ ij ∈ antidiagonal (N + 1),
      (N + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        ((derivative A)[[m + ij.1]] * B[[n + ij.2]] -
          B[[n + ij.2]] * (derivative A)[[m + ij.1]]) =
      (-m) • ((N + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 •
        (A[[(m - 1) + ij.1]] * B[[n + ij.2]] -
          B[[n + ij.2]] * A[[(m - 1) + ij.1]])) -
      (N + 1).choose ij.1 • (-1 : ℤ) ^ ij.2 • (ij.1 : ℤ) •
        (A[[m + ij.1 - 1]] * B[[n + ij.2]] -
          B[[n + ij.2]] * A[[m + ij.1 - 1]]) := by
    intro ij _
    have hi : m - 1 + ↑ij.1 = m + ↑ij.1 - 1 := by omega
    rw [ncoeff_derivative, hi]
    simp only [smul_mul_assoc, mul_smul_comm]
    module
  rw [sum_congr rfl e, sum_sub_distrib, ← smul_sum,
    isLocalOfOrder_iff.mp h.succ (m - 1) n, hweighted, smul_zero, sub_zero]

/-- Differentiating the second field increases a locality bound by one. -/
theorem derivative_right (h : A.IsLocalOfOrder B N) :
    A.IsLocalOfOrder (derivative B) (N + 1) :=
  h.symm.derivative_left.symm

/-- Iterated differentiation in the first variable preserves locality. -/
theorem iterate_derivative_left (h : A.IsLocalOfOrder B N) (k : ℕ) :
    ((derivative (R := R) (V := V))^[k] A).IsLocalOfOrder B (N + k) := by
  induction k with
  | zero => simpa using h
  | succ k ih => simpa [Function.iterate_succ_apply', Nat.add_assoc] using ih.derivative_left

/-- Derivatives of orders `k` and `l` of local fields are local of order at most `N + k + l`. -/
theorem iterate_derivative (h : A.IsLocalOfOrder B N) (k l : ℕ) :
    ((derivative (R := R) (V := V))^[k] A).IsLocalOfOrder
      ((derivative (R := R) (V := V))^[l] B) (N + k + l) := by
  exact ((h.iterate_derivative_left k).symm.iterate_derivative_left l).symm

end IsLocalOfOrder

/-! ### Translation covariance and vacuum modes -/

/-- The zero field is translation-covariant with every endomorphism `T`. -/
theorem lie_ncoeff_zero (T : Module.End R V) (m : ℤ) :
    ⁅T, (0 : VertexOperator R V)[[m]]⁆ = (derivative (0 : VertexOperator R V))[[m]] := by
  simp [Ring.lie_def]

/-- The identity field is translation-covariant with every endomorphism `T`. -/
theorem lie_ncoeff_id (T : Module.End R V) (m : ℤ) :
    ⁅T, (VertexOperator.id : VertexOperator R V)[[m]]⁆ =
      (derivative (VertexOperator.id : VertexOperator R V))[[m]] := by
  rw [derivative_id, ncoeff_id]
  split_ifs <;> simp [Ring.lie_def]

/-- Addition of fields preserves translation covariance `[T, A[[m]]] = (∂A)[[m]]`. -/
theorem lie_ncoeff_add {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    ⁅T, (A + B)[[m]]⁆ = (derivative (A + B))[[m]] := by
  simp only [map_add, Pi.add_apply, ← hA m, ← hB m, Ring.lie_def, mul_add, add_mul]
  abel

/-- Scalar multiplication preserves translation covariance `[T, A[[m]]] = (∂A)[[m]]`. -/
theorem lie_ncoeff_smul {T : Module.End R V} {A : VertexOperator R V} (r : R)
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (m : ℤ) :
    ⁅T, (r • A)[[m]]⁆ = (derivative (r • A))[[m]] := by
  simp [← hA m, Ring.lie_def, smul_sub]

/-- Subtraction of fields preserves translation covariance `[T, A[[m]]] = (∂A)[[m]]`. -/
theorem lie_ncoeff_sub {T : Module.End R V} {A B : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]])
    (hB : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (m : ℤ) :
    ⁅T, (A - B)[[m]]⁆ = (derivative (A - B))[[m]] := by
  simp only [map_sub, Pi.sub_apply, ← hA m, ← hB m, Ring.lie_def, mul_sub, sub_mul]
  abel

/-- Differentiation preserves translation covariance `[T, A[[m]]] = (∂A)[[m]]`. -/
theorem lie_ncoeff_derivative {T : Module.End R V} {A : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (m : ℤ) :
    ⁅T, (derivative A)[[m]]⁆ = (derivative (derivative A))[[m]] := by
  ext v
  simp only [ncoeff_derivative, ← hA (m - 1), Ring.lie_def, LinearMap.sub_apply,
    mul_apply_eq_comp, LinearMap.smul_apply, map_zsmul, smul_sub]

/-- Iterated differentiation preserves translation covariance. -/
theorem lie_ncoeff_iterate_derivative {T : Module.End R V} {A : VertexOperator R V}
    (hA : ∀ m : ℤ, ⁅T, A[[m]]⁆ = (derivative A)[[m]]) (k : ℕ) (m : ℤ) :
    ⁅T, ((derivative (R := R) (V := V))^[k] A)[[m]]⁆ =
      (derivative ((derivative (R := R) (V := V))^[k] A))[[m]] := by
  induction k generalizing m with
  | zero => exact hA m
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using lie_ncoeff_derivative ih m

/-- Pointwise evaluation of translation covariance `[T, B[[n]]] = (∂B)[[n]]` on a vector `v`. -/
theorem apply_ncoeff_apply_sub_ncoeff_apply {T : Module.End R V} {B : VertexOperator R V}
    (hcov : ∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]]) (n : ℤ) (v : V) :
    T ((B[[n]]) v) - (B[[n]]) (T v) = ((derivative B)[[n]]) v := by
  simpa [Ring.lie_def] using LinearMap.congr_fun (hcov n) v

/-- On a vector `vac` killed by `T`, translation covariance gives
`T ((B[[n]]) vac) = ((derivative B)[[n]]) vac`. -/
theorem apply_ncoeff_apply_of_lie_eq_derivative {T : Module.End R V} {B : VertexOperator R V}
    {vac : V} (hT : T vac = 0) (hcov : ∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]]) (n : ℤ) :
    T ((B[[n]]) vac) = ((derivative B)[[n]]) vac := by
  simpa [hT] using apply_ncoeff_apply_sub_ncoeff_apply hcov n vac

/-- Creation recursion without division for any field `B` covariant with an operator `T`
satisfying `T vac = 0`: `k! • (B[[-k - 1]]) vac = (T ^ k) ((B[[-1]]) vac)`. -/
theorem factorial_smul_ncoeff_apply_of_lie_eq_derivative
    {T : Module.End R V} {B : VertexOperator R V} {vac : V}
    (hT : T vac = 0) (hcov : ∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]]) (k : ℕ) :
    k.factorial • (B[[-k - 1]]) vac = (T ^ k) ((B[[-1]]) vac) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := apply_ncoeff_apply_of_lie_eq_derivative hT hcov (-(k : ℤ) - 1)
    have h₁ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
    have h₂ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by omega
    rw [ncoeff_derivative, LinearMap.smul_apply, h₁, h₂, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul,
      smul_comm]

/-- When `V` has unique additive divisibility (`HasUniqueDiv V`), any field `B` covariant with an
operator `T` satisfying `T vac = 0` annihilates `vac` in all nonnegative modes
(`B(z) vac ∈ V[[z]]`). -/
theorem ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative [HasUniqueDiv V]
    {T : Module.End R V} {B : VertexOperator R V} {vac : V}
    (hT : T vac = 0) (hcov : ∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]])
    {m : ℤ} (hm : 0 ≤ m) :
    (B[[m]]) vac = 0 := by
  -- Descending induction from lower truncation via `-(k + 1) • B[[k]] vac = T (B[[k + 1]] vac)`.
  lift m to ℕ using hm
  have hstep (k : ℕ) (hk : (B[[((k + 1 : ℕ) : ℤ)]]) vac = 0) : (B[[(k : ℤ)]]) vac = 0 := by
    have h := apply_ncoeff_apply_of_lie_eq_derivative hT hcov (k + 1 : ℕ)
    have hsub : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
    rw [hk, map_zero, ncoeff_derivative, LinearMap.smul_apply, hsub, neg_zsmul, natCast_zsmul,
      eq_neg_iff_add_eq_zero, zero_add] at h
    exact (smul_eq_zero.mp h).resolve_left (Nat.succ_ne_zero k)
  obtain ⟨N, hN⟩ := B.exists_forall_ncoeff_apply_eq_zero vac
  exact Nat.decreasingInduction' (motive := fun k : ℕ ↦ (B[[(k : ℤ)]]) vac = 0)
    (fun k _ _ ↦ hstep k) (Nat.le_add_right m N) (hN (m + N : ℕ) (by omega))

/-- Under `HasUniqueDiv V` and `T vac = 0`, two `T`-covariant fields agreeing on `vac` at mode `-1`
agree on `vac` in every mode `m : ℤ`. -/
theorem ncoeff_apply_eq_of_lie_eq_derivative [HasUniqueDiv V]
    {T : Module.End R V} {A B : VertexOperator R V} {vac : V}
    (hT : T vac = 0) (hA : ∀ n : ℤ, ⁅T, A[[n]]⁆ = (derivative A)[[n]])
    (hB : ∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]])
    (h : (A[[-1]]) vac = (B[[-1]]) vac) (m : ℤ) :
    (A[[m]]) vac = (B[[m]]) vac := by
  rcases lt_or_ge m 0 with hm | hm
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -k - 1 := ⟨(-m - 1).toNat, by omega⟩
    refine nsmul_right_injective k.factorial_ne_zero ?_
    dsimp only
    rw [factorial_smul_ncoeff_apply_of_lie_eq_derivative hT hA k,
      factorial_smul_ncoeff_apply_of_lie_eq_derivative hT hB k, h]
  · rw [ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT hA hm,
      ncoeff_apply_eq_zero_of_nonneg_of_lie_eq_derivative hT hB hm]

/-- Under `HasUniqueDiv V` and `T vac = 0`, a `T`-covariant field killing `vac` at mode `-1` kills
`vac` in every mode `m : ℤ`. -/
theorem ncoeff_apply_eq_zero_of_lie_eq_derivative [HasUniqueDiv V]
    {T : Module.End R V} {B : VertexOperator R V} {vac : V}
    (hT : T vac = 0) (hB : ∀ n : ℤ, ⁅T, B[[n]]⁆ = (derivative B)[[n]])
    (h : (B[[-1]]) vac = 0) (m : ℤ) :
    (B[[m]]) vac = 0 := by
  simpa using ncoeff_apply_eq_of_lie_eq_derivative hT hB (lie_ncoeff_zero T) (by simpa using h) m

/-! ### Action on vectors killed by nonnegative modes -/

/-- Differentiation preserves annihilation of a vector by all nonnegative modes. -/
theorem ncoeff_derivative_apply_of_nonneg {A : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0) {m : ℤ} (hm : 0 ≤ m) :
    ((derivative A)[[m]]) v = 0 := by
  rcases hm.eq_or_lt with rfl | hpos
  · simp
  · rw [ncoeff_derivative, LinearMap.smul_apply, hA (m - 1) (by omega), smul_zero]

/-- Iterated differentiation preserves annihilation of a vector by all nonnegative modes. -/
theorem ncoeff_iterate_derivative_apply_of_nonneg {A : VertexOperator R V} {v : V}
    (hA : ∀ m : ℤ, 0 ≤ m → (A[[m]]) v = 0) (k : ℕ) {m : ℤ} (hm : 0 ≤ m) :
    (((derivative (R := R) (V := V))^[k] A)[[m]]) v = 0 := by
  induction k generalizing m with
  | zero => exact hA m hm
  | succ k ih =>
    simpa only [Function.iterate_succ_apply'] using
      ncoeff_derivative_apply_of_nonneg (fun _ ↦ ih) hm

end VertexOperator
