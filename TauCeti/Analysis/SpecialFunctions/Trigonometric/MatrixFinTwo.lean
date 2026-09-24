/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

/-!
# Real `2 × 2` matrices with trace `2 cos θ`

A real `2 × 2` matrix `A` of determinant one and trace `2 cos θ` has powers given by the Chebyshev
form of the Cayley–Hamilton recurrence, `sin θ • A ^ n = sin (n θ) • A - sin ((n - 1) θ) • 1`. At
`θ = π / k` with `2 ≤ k` this gives `A ^ k = -1`, so an element of `PSL(2, ℝ)` whose
representatives have trace `± 2 cos (π / k)` is elliptic of order dividing `k`.

The rotation `!![cos θ, sin θ; -sin θ, cos θ]` conjugated by `diag (exp (t / 2), exp (-t / 2))` is
the matrix `!![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ]` of `SL(2, ℝ)`, of trace
`2 cos θ`. Two such matrices with parameters `(θ₁, 0)` and `(θ₂, t)` have a product of trace
`2 cos θ₁ cos θ₂ - 2 cosh t sin θ₁ sin θ₂` and, by the Fricke trace identity, a commutator of trace
`2 + 4 (sin θ₁ sin θ₂ sinh t) ^ 2`. These are the matrices of the representation of a hyperbolic
triangle group in `PSL(2, ℝ)`.

## Main results

* `Matrix.sin_smul_pow_fin_two`: the powers of a determinant-one matrix of trace `2 cos θ`.
* `Matrix.pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div`: a determinant-one real matrix of trace
  `2 cos (π / k)`, with `2 ≤ k`, has `k`-th power `-1`.
* `Matrix.ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq_two_mul_cos_pi_div_sq`: if
  `trace A ^ 2 = (2 cos (π / k)) ^ 2` with `2 ≤ k`, then the class of `A` has `k`-th power `1`.
* `Matrix.SpecialLinearGroup.conjRotation`: the conjugated rotation matrix, with its trace
  `trace_conjRotation`, the trace `trace_conjRotation_mul_conjRotation` of a product, and the trace
  `trace_commutatorElement_conjRotation` of a commutator.

## References

* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §2.1 (elliptic elements of `PSL(2, ℝ)` and their traces).
-/

public section

noncomputable section

open Real
open scoped commutatorElement MatrixGroups

namespace Matrix

/-- The powers of a real `2 × 2` matrix of determinant one and trace `2 cos θ`:
`sin θ • A ^ n = sin (n θ) • A - sin ((n - 1) θ) • 1`. The coefficients are the values of the
Chebyshev polynomials of the second kind at `cos θ`, multiplied by `sin θ`. -/
theorem sin_smul_pow_fin_two {A : Matrix (Fin 2) (Fin 2) ℝ} {θ : ℝ} (hdet : A.det = 1)
    (htr : A.trace = 2 * cos θ) (n : ℕ) :
    sin θ • A ^ n = sin (n * θ) • A - sin ((n - 1) * θ) • 1 := by
  -- The sine sequence obeys the same recurrence as the powers:
  -- `sin ((m + 1) θ) = 2 cos θ sin (m θ) - sin ((m - 1) θ)`.
  have hsin (m : ℝ) : sin ((m + 1) * θ) = 2 * cos θ * sin (m * θ) - sin ((m - 1) * θ) := by
    have h₁ : (m + 1) * θ = m * θ + θ := by ring
    have h₂ : (m - 1) * θ = m * θ - θ := by ring
    rw [h₁, h₂, sin_add, sin_sub]
    ring
  suffices ∀ n : ℕ, sin θ • A ^ n = sin (n * θ) • A - sin ((n - 1) * θ) • 1 ∧
      sin θ • A ^ (n + 1) = sin ((n + 1 : ℕ) * θ) • A - sin ((((n + 1 : ℕ) : ℝ) - 1) * θ) • 1 from
    (this n).1
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    rw [pow_add_two_fin_two, hdet, htr, one_smul, smul_sub, smul_comm, ih.2, ih.1]
    have e₁ := hsin ((n + 1 : ℕ) : ℝ)
    have e₂ := hsin (n : ℝ)
    push_cast at e₁ e₂ ⊢
    -- Normalize the predecessor indices so the sine recurrence matches the casted goal.
    rw [show (n : ℝ) + 1 + 1 - 1 = n + 1 by ring]
    rw [show (n : ℝ) + 1 - 1 = n by ring] at e₁ ⊢
    rw [e₁, e₂]
    module

/-- A real `2 × 2` matrix of determinant one and trace `2 cos (π / k)`, with `2 ≤ k`, has `k`-th
power `-1`. Its image in `PSL(2, ℝ)` has order dividing `k`. -/
theorem pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div {A : Matrix (Fin 2) (Fin 2) ℝ} {k : ℕ}
    (hdet : A.det = 1) (hk : 2 ≤ k) (htr : A.trace = 2 * cos (π / k)) : A ^ k = -1 := by
  have hk₀ : (k : ℝ) ≠ 0 := by positivity
  have hs : 0 < sin (π / k) := TauCeti.sin_pi_div_pos (Nat.one_lt_cast.2 hk)
  have h := sin_smul_pow_fin_two hdet htr k
  -- Normalize the two sine arguments before using `sin_pi` and `sin_pi_sub`.
  rw [show (k : ℝ) * (π / k) = π by field_simp, show ((k : ℝ) - 1) * (π / k) = π - π / k by
    field_simp, sin_pi, sin_pi_sub, zero_smul, zero_sub, ← smul_neg] at h
  exact smul_right_injective _ hs.ne' h

namespace ProjectiveSpecialLinearGroup

/-- If a matrix of `SL(2, ℝ)` has trace `± 2 cos (π / k)` with `2 ≤ k`, then its class in
`PSL(2, ℝ)` has `k`-th power `1`: the matrix itself, or its negative, has `k`-th power `-1`. The
hypothesis is stated on the square of the trace, which depends only on the class in `PSL(2, ℝ)`. -/
theorem mk_pow_eq_one_of_trace_sq_eq_two_mul_cos_pi_div_sq {A : SL(2, ℝ)} {k : ℕ} (hk : 2 ≤ k)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = (2 * cos (π / k)) ^ 2) :
    (A : PSL(2, ℝ)) ^ k = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact .inr (Subtype.ext (by
      rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one]
      exact pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div A.det_coe hk h))
  · -- The negative of `A` has trace `2 cos (π / k)`, and `(-A) ^ k = ± A ^ k`.
    have hneg := pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div (A := -(A : Matrix _ _ ℝ))
      (by simp [det_neg]) hk (by rw [trace_neg, h, neg_neg])
    rcases k.even_or_odd with hk' | hk'
    · rw [hk'.neg_pow] at hneg
      exact .inr (Subtype.ext (by
        rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one,
          hneg]))
    · rw [hk'.neg_pow, neg_inj] at hneg
      exact .inl (Subtype.ext (by rw [SpecialLinearGroup.coe_pow, hneg,
        SpecialLinearGroup.coe_one]))

end ProjectiveSpecialLinearGroup

namespace SpecialLinearGroup

/-- The matrix `!![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ]` of `SL(2, ℝ)`: the rotation
`!![cos θ, sin θ; -sin θ, cos θ]` conjugated by `diag (exp (t / 2), exp (-t / 2))`. -/
def conjRotation (θ t : ℝ) : SL(2, ℝ) :=
  ⟨!![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ], by
    rw [det_fin_two_of, exp_neg]
    field_simp
    linear_combination cos_sq_add_sin_sq θ⟩

/-- The entries of `conjRotation θ t`. -/
theorem coe_conjRotation (θ t : ℝ) :
    (conjRotation θ t : Matrix (Fin 2) (Fin 2) ℝ) =
      !![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ] := (rfl)

/-- The conjugated rotation `conjRotation θ t` has the trace `2 cos θ` of the rotation. -/
@[simp]
theorem trace_conjRotation (θ t : ℝ) :
    (conjRotation θ t : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * cos θ := by
  rw [coe_conjRotation, trace_fin_two_of]
  ring

/-- The product of the conjugated rotations with parameters `(θ₂, t)` and `(θ₁, 0)` has trace
`2 cos θ₁ cos θ₂ - 2 cosh t sin θ₁ sin θ₂`. -/
theorem trace_conjRotation_mul_conjRotation (θ₁ θ₂ t : ℝ) :
    ((conjRotation θ₂ t * conjRotation θ₁ 0 : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      2 * cos θ₁ * cos θ₂ - 2 * cosh t * (sin θ₁ * sin θ₂) := by
  rw [SpecialLinearGroup.coe_mul, coe_conjRotation, coe_conjRotation, mul_fin_two,
    trace_fin_two_of, cosh_eq]
  simp only [exp_zero, neg_zero, one_mul]
  ring

/-- The commutator of the conjugated rotations with parameters `(θ₁, 0)` and `(θ₂, t)` has trace
`2 + 4 (sin θ₁ sin θ₂ sinh t) ^ 2`, by the Fricke trace identity. -/
theorem trace_commutatorElement_conjRotation (θ₁ θ₂ t : ℝ) :
    ((⁅conjRotation θ₁ 0, conjRotation θ₂ t⁆ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
      2 + 4 * (sin θ₁ * sin θ₂ * sinh t) ^ 2 := by
  rw [trace_commutatorElement_fin_two, trace_conjRotation, trace_conjRotation,
    SpecialLinearGroup.coe_mul, trace_mul_comm, ← SpecialLinearGroup.coe_mul,
    trace_conjRotation_mul_conjRotation]
  linear_combination 4 * (1 - cos θ₂ ^ 2) * cos_sq_add_sin_sq θ₁ +
    4 * sin θ₁ ^ 2 * cos_sq_add_sin_sq θ₂ + 4 * (sin θ₁ * sin θ₂) ^ 2 * cosh_sq t

end SpecialLinearGroup

end Matrix
