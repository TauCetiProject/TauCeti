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
import Mathlib.Tactic.Module

/-!
# Formal derivatives of vertex operators

The formal derivative of a field is again a field: differentiating a Laurent series lowers
its lower bound by at most one. In normalized mode indexing its coefficients are
`(∂A)[[n]] = -n • A[[n - 1]]`. This construction is linear over the coefficient ring and
requires no characteristic-zero assumption. When an endomorphism `T` kills a vector `vac` and acts
as `∂` by commutation on a field `B`, iterating this mode formula yields the division-free creation
identity `k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac)` (`VertexOperator.factorial_smul_ncoeff_apply`).

Differentiation preserves mutual locality, increasing a locality bound by one. More generally,
iterated derivatives in the two variables increase the bound by the sum of their orders.
These are the formal-calculus identities used for translation-covariant fields and reconstruction
of vertex algebras.

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

/-- **Division-free creation recursion.** If an endomorphism `T` kills `vac` and acts as `∂` on a
field `B` by commutation, then `k! • B₍₋ₖ₋₁₎ vac = Tᵏ (B₍₋₁₎ vac)` for every `k : ℕ`. -/
theorem factorial_smul_ncoeff_apply {T : Module.End R V} {vac : V} (hvac : T vac = 0)
    {B : VertexOperator R V} (hT : ∀ m : ℤ, ⁅T, B[[m]]⁆ = (derivative B)[[m]]) (k : ℕ) :
    k.factorial • (B[[-k - 1]]) vac = (T ^ k) ((B[[-1]]) vac) := by
  have hrec (m : ℤ) : T ((B[[m]]) vac) = (-m) • (B[[m - 1]]) vac := by
    have h := LinearMap.congr_fun (hT m) vac
    rwa [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp, mul_apply_eq_comp, hvac, map_zero,
      sub_zero, ncoeff_derivative, LinearMap.smul_apply] at h
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hrec (-(k : ℤ) - 1)
    have h₁ : -(-(k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    have h₂ : -(k : ℤ) - 1 - 1 = -((k + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
    rw [h₁, h₂, natCast_zsmul] at h
    rw [pow_succ', mul_apply_eq_comp, ← ih, map_nsmul, h, Nat.factorial_succ, mul_nsmul,
      smul_comm]

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

end VertexOperator
