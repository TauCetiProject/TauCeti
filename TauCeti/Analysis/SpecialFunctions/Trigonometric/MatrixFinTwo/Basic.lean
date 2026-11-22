/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Algebra.Group.Matrix
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo
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
* `Matrix.pow_eq_cos_smul_one_add_fin_two`,
  `Matrix.SpecialLinearGroup.coe_zpow_eq_cos_smul_one_add`: for `sin θ ≠ 0`, the natural and
  integer powers `A ^ n = cos (n θ) • 1 + (sin (n θ) / sin θ) • (A - cos θ • 1)`.
* `Matrix.trace_pow_eq_two_mul_cos_fin_two`: the traces `2 cos (n θ)` of those powers.
* `Matrix.pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div`: a determinant-one real matrix of trace
  `2 cos (π / k)`, with `2 ≤ k`, has `k`-th power `-1`.
* `Matrix.ProjectiveSpecialLinearGroup.orderOf_mk_of_trace_sq_eq_two_mul_cos_pi_div_sq`: if
  `trace A ^ 2 = (2 cos (π / k)) ^ 2` with `2 ≤ k`, then the class of `A` has order exactly `k`.
* `Matrix.ProjectiveSpecialLinearGroup.mk_pow_eq_one_of_trace_sq_eq_two_mul_cos_pi_div_sq`: if
  `trace A ^ 2 = (2 cos (π / k)) ^ 2` with `2 ≤ k`, then the class of `A` has `k`-th power `1`.
* `Matrix.SpecialLinearGroup.rotation`: the rotation matrix `!![cos θ, sin θ; -sin θ, cos θ]`;
  `rotation_zero`, `rotation_add` and `rotation_inv` make the family a one-parameter subgroup,
  `continuous_rotation` a continuous one, and `pslMk_rotation_pi_div_two` identifies the class of
  the quarter turn in `PSL(2, ℝ)` with `TauCeti.pslS`, and `trace_rotation_mul` gives the trace
  `trace A cos θ + (A₁₀ - A₀₁) sin θ` of `rotation θ * A`.
* `Matrix.SpecialLinearGroup.conjRotation`: the conjugated rotation matrix
  (`conjRotation_zero_right` identifies the unconjugated case with `rotation`), with its trace
  `trace_conjRotation`, the trace `trace_conjRotation_mul_conjRotation` of a product, and the
  trace `trace_commutatorElement_conjRotation` of a commutator.

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
    ring_nf at e₁ e₂ ⊢
    rw [e₁, e₂]
    module

/-- The powers of a real `2 × 2` matrix of determinant one and trace `2 cos θ`, for `sin θ ≠ 0`:
`A ^ n = cos (n θ) • 1 + (sin (n θ) / sin θ) • (A - cos θ • 1)`. -/
theorem pow_eq_cos_smul_one_add_fin_two {A : Matrix (Fin 2) (Fin 2) ℝ} {θ : ℝ} (hdet : A.det = 1)
    (htr : A.trace = 2 * cos θ) (hθ : sin θ ≠ 0) (n : ℕ) :
    A ^ n =
      cos (n * θ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (sin (n * θ) / sin θ) • (A - cos θ • 1) := by
  refine smul_right_injective _ hθ ?_
  dsimp only
  rw [sin_smul_pow_fin_two hdet htr n, sub_mul, one_mul, sin_sub, smul_add, smul_smul, smul_smul,
    mul_div_cancel₀ _ hθ]
  module

/-- The traces of the powers of a real `2 × 2` matrix of determinant one and trace `2 cos θ` are
`trace (A ^ n) = 2 cos (n θ)`. -/
theorem trace_pow_eq_two_mul_cos_fin_two {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 1)
    {θ : ℝ} (htr : A.trace = 2 * cos θ) (n : ℕ) : (A ^ n).trace = 2 * cos (n * θ) := by
  -- Two-step induction on the trace recurrence `t (n + 2) = t 1 t (n + 1) - t n`, matched by
  -- `cos ((m + 2) θ) + cos (m θ) = 2 cos θ cos ((m + 1) θ)`.
  suffices ∀ m : ℕ, (A ^ m).trace = 2 * cos (m * θ) ∧
      (A ^ (m + 1)).trace = 2 * cos ((m + 1 : ℕ) * θ) from (this n).1
  intro m
  induction m with
  | zero => simp [htr]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    rw [trace_pow_add_two_fin_two, hdet, htr, ih.1, ih.2, one_mul]
    have h₁ : ((m + 1 + 1 : ℕ) : ℝ) * θ = (m + 1 : ℕ) * θ + θ := by push_cast; ring
    have h₂ : (m : ℝ) * θ = (m + 1 : ℕ) * θ - θ := by push_cast; ring
    rw [h₁, h₂, cos_add, cos_sub]
    ring

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

private theorem mk_pow_eq_one_of_trace_eq_two_mul_cos_pi_div {A : SL(2, ℝ)} {k : ℕ}
    (hk : 2 ≤ k) (h : (A : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * cos (π / k)) :
    (A : PSL(2, ℝ)) ^ k = 1 := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one]
  exact .inr (Subtype.ext (by
    rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_neg, SpecialLinearGroup.coe_one]
    exact pow_eq_neg_one_of_trace_eq_two_mul_cos_pi_div A.det_coe hk h))

/-- If a matrix of `SL(2, ℝ)` has trace `± 2 cos (π / k)` with `2 ≤ k`, then its class in
`PSL(2, ℝ)` has `k`-th power `1`: the matrix itself, or its negative, has `k`-th power `-1`. The
hypothesis is stated on the square of the trace, which depends only on the class in `PSL(2, ℝ)`. -/
theorem mk_pow_eq_one_of_trace_sq_eq_two_mul_cos_pi_div_sq {A : SL(2, ℝ)} {k : ℕ} (hk : 2 ≤ k)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = (2 * cos (π / k)) ^ 2) :
    (A : PSL(2, ℝ)) ^ k = 1 := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact mk_pow_eq_one_of_trace_eq_two_mul_cos_pi_div hk h
  · have hneg : ((-A : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
        2 * cos (π / k) := by rw [SpecialLinearGroup.coe_neg, trace_neg, h, neg_neg]
    simpa only [mk_neg] using
      (mk_pow_eq_one_of_trace_eq_two_mul_cos_pi_div (A := -A) hk hneg)

private theorem orderOf_mk_of_trace_eq_two_mul_cos_pi_div {A : SL(2, ℝ)} {k : ℕ} (hk : 2 ≤ k)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * cos (π / k)) :
    orderOf (A : PSL(2, ℝ)) = k := by
  refine (orderOf_eq_iff (by omega)).2 ⟨mk_pow_eq_one_of_trace_eq_two_mul_cos_pi_div hk h,
    fun m hmk hm hpow ↦ ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
    SpecialLinearGroup.mem_center_iff_eq_one_or_eq_neg_one] at hpow
  -- `A ^ m = ± 1` has squared trace `4`, while `(2 cos (m π / k)) ^ 2 < 4` for `0 < m < k`
  have htr : ((A ^ m : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = 4 := by
    rcases hpow with hpow | hpow <;> simp [hpow, trace_one] <;> norm_num
  have hs : 0 < sin (m * (π / k)) := by
    refine sin_pos_of_pos_of_lt_pi (by positivity) ?_
    rw [mul_div_assoc', div_lt_iff₀ (by positivity), mul_comm]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast hmk) pi_pos
  rw [SpecialLinearGroup.coe_pow, trace_pow_eq_two_mul_cos_fin_two A.det_coe h] at htr
  nlinarith [sin_sq_add_cos_sq (m * (π / k))]

/-- **The order of an elliptic element of `PSL(2, ℝ)`.** If a matrix of `SL(2, ℝ)` has trace
`± 2 cos (π / k)` with `2 ≤ k`, then its class in `PSL(2, ℝ)` has order exactly `k`: a power
`A ^ m = ± 1` with `0 < m < k` would have trace `± 2 cos (m π / k) = ± 2`. -/
theorem orderOf_mk_of_trace_sq_eq_two_mul_cos_pi_div_sq {A : SL(2, ℝ)} {k : ℕ} (hk : 2 ≤ k)
    (h : (A : Matrix (Fin 2) (Fin 2) ℝ).trace ^ 2 = (2 * cos (π / k)) ^ 2) :
    orderOf (A : PSL(2, ℝ)) = k := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact orderOf_mk_of_trace_eq_two_mul_cos_pi_div hk h
  · have hneg : ((-A : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace =
        2 * cos (π / k) := by rw [SpecialLinearGroup.coe_neg, trace_neg, h, neg_neg]
    simpa only [mk_neg] using orderOf_mk_of_trace_eq_two_mul_cos_pi_div (A := -A) hk hneg

end ProjectiveSpecialLinearGroup

namespace SpecialLinearGroup

/-- The integer powers of a matrix of `SL(2, ℝ)` of trace `2 cos θ`, for `sin θ ≠ 0`:
`A ^ n = cos (n θ) • 1 + (sin (n θ) / sin θ) • (A - cos θ • 1)` for every `n : ℤ`. -/
theorem coe_zpow_eq_cos_smul_one_add {A : SL(2, ℝ)} {θ : ℝ}
    (htr : (A : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * cos θ) (hθ : sin θ ≠ 0) (n : ℤ) :
    ((A ^ n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      cos (n * θ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (sin (n * θ) / sin θ) • ((A : Matrix (Fin 2) (Fin 2) ℝ) - cos θ • 1) := by
  cases n with
  | ofNat m =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, coe_pow, Int.cast_natCast]
    exact pow_eq_cos_smul_one_add_fin_two A.det_coe htr hθ m
  | negSucc m =>
    -- `A⁻¹ = adjugate A = trace A • 1 - A` also has trace `2 cos θ`
    have hinv : ((A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
        (2 * cos θ) • 1 - (A : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [coe_inv, adjugate_fin_two_eq_trace_smul_one_sub, htr]
    have htr' : ((A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * cos θ := by
      rw [hinv, trace_sub, trace_smul, trace_one, htr, Fintype.card_fin, smul_eq_mul]
      ring
    rw [zpow_negSucc, ← inv_pow, coe_pow,
      pow_eq_cos_smul_one_add_fin_two (A⁻¹).det_coe htr' hθ (m + 1), hinv, Int.cast_negSucc,
      neg_mul, cos_neg, sin_neg, neg_div]
    push_cast
    module

/-- The rotation `!![cos θ, sin θ; -sin θ, cos θ]`, an element of `SL(2, ℝ)`. -/
def rotation (θ : ℝ) : SL(2, ℝ) :=
  ⟨!![cos θ, sin θ; -sin θ, cos θ], by
    rw [det_fin_two_of]
    linear_combination cos_sq_add_sin_sq θ⟩

/-- The entries of `rotation θ`. -/
@[simp]
theorem coe_rotation (θ : ℝ) :
    (rotation θ : Matrix (Fin 2) (Fin 2) ℝ) = !![cos θ, sin θ; -sin θ, cos θ] := (rfl)

/-- The rotation by `0` is the identity. -/
@[simp]
theorem rotation_zero : rotation 0 = 1 :=
  SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp

-- Not `@[simp]`: the family form `rotation θ` is the simp normal form, so that the action
-- lemmas stated in it keep firing.
/-- The rotations form a one-parameter subgroup: `rotation (θ + φ) = rotation θ * rotation φ`. -/
theorem rotation_add (θ φ : ℝ) : rotation (θ + φ) = rotation θ * rotation φ :=
  SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp [cos_add, sin_add, Matrix.mul_apply] <;> ring

/-- The inverse of `rotation θ` is `rotation (-θ)`. -/
@[simp]
theorem rotation_inv (θ : ℝ) : (rotation θ)⁻¹ = rotation (-θ) :=
  inv_eq_of_mul_eq_one_right (by rw [← rotation_add, add_neg_cancel, rotation_zero])

/-- The rotations `θ ↦ rotation θ` form a continuous family in `SL(2, ℝ)`. -/
@[fun_prop]
theorem continuous_rotation : Continuous rotation :=
  Continuous.subtype_mk (continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_zero,
        cons_val_one, cons_val_fin_one] <;>
      fun_prop) _

/-- The class of `rotation (π/2) = !![0, 1; -1, 0]` in `PSL(2, ℝ)` is `pslS`, the image of
`ModularGroup.S = !![0, -1; 1, 0]`: the two matrices differ by a sign. -/
@[simp]
theorem pslMk_rotation_pi_div_two : (↑(rotation (π / 2)) : PSL(2, ℝ)) = TauCeti.pslS := by
  have h : rotation (π / 2) = -(map (Int.castRingHom ℝ) ModularGroup.S) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [map_apply_coe, ModularGroup.coe_S]
  rw [h, ProjectiveSpecialLinearGroup.mk_neg, TauCeti.pslS_def, psl2zToPSL2R_mk,
    sl2zToPSL2R_apply]

/-- The trace of the product of `rotation θ` with a `2 × 2` matrix `A`:
`trace (R(θ) A) = trace A cos θ + (A₁₀ - A₀₁) sin θ`. -/
theorem trace_rotation_mul (θ : ℝ) (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ((rotation θ : Matrix (Fin 2) (Fin 2) ℝ) * A).trace =
      A.trace * cos θ + (A 1 0 - A 0 1) * sin θ := by
  rw [coe_rotation, trace_fin_two, trace_fin_two, Matrix.mul_apply, Matrix.mul_apply]
  simp only [Fin.sum_univ_two, of_apply, cons_val', cons_val_zero, cons_val_one,
    cons_val_fin_one, empty_val']
  ring

/-- The matrix `!![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ]` of `SL(2, ℝ)`: the rotation
`rotation θ = !![cos θ, sin θ; -sin θ, cos θ]` conjugated by `diag (exp (t / 2), exp (-t / 2))`. -/
def conjRotation (θ t : ℝ) : SL(2, ℝ) :=
  ⟨!![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ], by
    rw [det_fin_two_of, exp_neg]
    field_simp
    linear_combination cos_sq_add_sin_sq θ⟩

/-- The entries of `conjRotation θ t`. -/
@[simp]
theorem coe_conjRotation (θ t : ℝ) :
    (conjRotation θ t : Matrix (Fin 2) (Fin 2) ℝ) =
      !![cos θ, exp t * sin θ; -(exp (-t) * sin θ), cos θ] := (rfl)

-- Not `@[simp]`: `conjRotation θ 0` is the form the triangle-group generators use, and the
-- `@[simp]` trace lemmas below are stated in it.
/-- The unconjugated case of `conjRotation` is `rotation`. -/
theorem conjRotation_zero_right (θ : ℝ) : conjRotation θ 0 = rotation θ :=
  SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp

/-- The conjugated rotation `conjRotation θ t` has the trace `2 cos θ` of the rotation. -/
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
@[simp]
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
