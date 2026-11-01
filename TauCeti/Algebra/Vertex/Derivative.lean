/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.VertexOperator
import Mathlib.Tactic.Module

/-!
# Formal derivatives of vertex operators

The formal derivative of a field is again a field: differentiating a Laurent series lowers
its lower bound by at most one. In normalized mode indexing its coefficients are
`(∂A)[[n]] = -n • A[[n - 1]]`. This construction is linear over the coefficient ring and
requires no characteristic-zero assumption.

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

/-- The coefficients of the formal derivative have a lower bound on every vector. -/
private theorem bddBelow_support_derivative (A : VertexOperator R V) (v : V) :
    BddBelow (Function.support fun n : ℤ ↦ ((n + 1) • HVertexOperator.coeff A (n + 1)) v) := by
  refine ⟨HahnSeries.order ((HahnModule.of R).symm (A v)) - 1, fun n hn ↦ ?_⟩
  by_contra h
  have hz := coeff_eq_zero_of_lt_order A (n + 1) v (by omega)
  exact hn (by simp only [LinearMap.smul_apply, hz, smul_zero])

/-- Formal differentiation of fields, defined on Laurent coefficients by
`(∂A).coeff n = (n + 1) • A.coeff (n + 1)`. -/
def derivative : VertexOperator R V →ₗ[R] VertexOperator R V where
  toFun A := of_coeff (fun n ↦ (n + 1) • HVertexOperator.coeff A (n + 1))
    (bddBelow_support_derivative A)
  map_add' A B := by
    apply ext_ncoeff
    intro n
    simp only [ncoeff_of_coeff, map_add, Pi.add_apply, smul_add]
  map_smul' r A := by
    apply ext_ncoeff
    intro n
    simp only [ncoeff_of_coeff, map_smul, RingHom.id_apply, Pi.smul_apply]
    exact smul_comm _ _ _

-- As with Mathlib's coefficient API, this is not a simp lemma: the simp normal form
-- uses normalized coefficients instead.
/-- Differentiation shifts the unnormalized Laurent coefficients down by one. -/
theorem coeff_derivative (A : VertexOperator R V) (n : ℤ) :
    HVertexOperator.coeff (derivative A) n = (n + 1) • HVertexOperator.coeff A (n + 1) := by
  ext v
  simp only [derivative, LinearMap.coe_mk, AddHom.coe_mk, HVertexOperator.coeff_apply_apply,
    of_coeff_apply_coeff, LinearMap.smul_apply]

/-- The normalized modes of the derivative are `(∂A)₍ₙ₎ = -n A₍ₙ₋₁₎`. -/
@[simp]
theorem ncoeff_derivative (A : VertexOperator R V) (n : ℤ) :
    (derivative A)[[n]] = (-n) • A[[n - 1]] := by
  simp only [ncoeff_apply, coeff_derivative]
  have h₁ : -n - 1 + 1 = -n := by omega
  have h₂ : -(n - 1) - 1 = -n := by omega
  rw [h₁, h₂]

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
    rw [Nat.sum_antidiagonal_succ]
    simp only [Nat.cast_zero, zero_smul, smul_zero, zero_add]
    have e : ∀ ij ∈ antidiagonal N,
        (N + 1).choose (ij.1 + 1) • (-1 : ℤ) ^ ij.2 • (↑(ij.1 + 1) : ℤ) •
          (A[[m + ↑(ij.1 + 1) - 1]] * B[[n + ij.2]] -
            B[[n + ij.2]] * A[[m + ↑(ij.1 + 1) - 1]]) =
        (N + 1) • (N.choose ij.1 • (-1 : ℤ) ^ ij.2 •
          (A[[m + ij.1]] * B[[n + ij.2]] - B[[n + ij.2]] * A[[m + ij.1]])) := by
      intro ij _
      have hi : m + ↑(ij.1 + 1) - 1 = m + ij.1 := by omega
      rw [hi, natCast_zsmul, smul_comm ((-1 : ℤ) ^ ij.2) (ij.1 + 1), ← mul_smul,
        ← Nat.add_one_mul_choose_eq, mul_smul]
    rw [sum_congr rfl e, ← smul_sum, isLocalOfOrder_iff.mp h m n, smul_zero]
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
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    ((h.iterate_derivative_left k).symm.iterate_derivative_left l).symm

end IsLocalOfOrder

end VertexOperator
