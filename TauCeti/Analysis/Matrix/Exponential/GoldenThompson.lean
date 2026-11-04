/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Matrix.Exponential.Log
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Normed.Algebra.Trotter

/-!
# The Golden–Thompson inequality

For Hermitian matrices `A` and `B` over `ℝ` or `ℂ` (any `RCLike` field),

`Tr (exp (A + B)) ≤ Tr (exp A * exp B)`.

Although `exp (A + B)` and `exp A * exp B` need not commute or compare in the Loewner order, their
traces satisfy the scalar inequality. Both traces are real: `exp (A + B)` is positive definite, and
`Tr (exp A * exp B) = Tr (exp (A / 2) * exp B * exp (A / 2)) ≥ 0`
(`Matrix.IsHermitian.trace_exp_mul_nonneg`).

The proof combines the dyadic trace-power inequalities of Cohen, Friedland, Kato, and Kelly with
the Banach-algebra Lie–Trotter formula (`NormedSpace.tendsto_exp_inv_smul_mul_exp_inv_smul_pow`):

1. Using Cauchy–Schwarz for the Frobenius inner product (`Matrix.frobeniusInnerProductSpace`),
   mutual induction on `k` establishes `Re Tr (Y ^ (2 ^ (k + 1))) ≤ Re Tr ((Yᴴ * Y) ^ (2 ^ k))`
   for every square matrix `Y` alongside
   `Re Tr ((A * B) ^ (2 ^ k)) ≤ √(Re Tr (A ^ (2 ^ (k + 1)))) * √(Re Tr (B ^ (2 ^ (k + 1))))` for
   Hermitian `A` and `B`.
2. Applying the first bound to `Y = A * B` for Hermitian `A, B` and cycling `B` inside the trace
   yields `Re Tr ((A * B) ^ (2 ^ (k + 1))) ≤ Re Tr ((A ^ 2 * B ^ 2) ^ (2 ^ k))`, and iterating
   `k` times gives `Re Tr ((A * B) ^ (2 ^ k)) ≤ Re Tr (A ^ (2 ^ k) * B ^ (2 ^ k))`.
3. Substituting `exp ((2 ^ k)⁻¹ • A)` and `exp ((2 ^ k)⁻¹ • B)` and letting `k → ∞` via
   Lie–Trotter gives the Golden–Thompson inequality.

## Main results

* `Matrix.re_trace_pow_two_pow_succ_le`: `Re Tr (Y ^ (2 ^ (k + 1))) ≤ Re Tr ((Yᴴ * Y) ^ (2 ^ k))`
  for every square matrix `Y`.
* `Matrix.IsHermitian.re_trace_mul_pow_two_pow_le`: for Hermitian `A` and `B`,
  `Re Tr ((A * B) ^ (2 ^ k)) ≤ Re Tr (A ^ (2 ^ k) * B ^ (2 ^ k))`.
* `Matrix.IsHermitian.re_trace_exp_add_le`: **the Golden–Thompson inequality** in real-part form,
  `RCLike.re (exp (A + B)).trace ≤ RCLike.re (exp A * exp B).trace`.
* `Matrix.IsHermitian.trace_exp_add_le`: **the Golden–Thompson inequality** in the `RCLike` order,
  `(exp (A + B)).trace ≤ (exp A * exp B).trace`.

## References

* S. Golden, *Lower bounds for the Helmholtz function*, Phys. Rev. 137 (1965), B1127–B1128.
* C. J. Thompson, *Inequality with applications in statistical mechanics*, J. Math. Phys. 6 (1965),
  1812–1813.
* J. E. Cohen, S. Friedland, T. Kato, F. P. Kelly, *Eigenvalue inequalities for products of matrix
  exponentials*, Linear Algebra Appl. 45 (1982), 55–95.
-/

public section

open Filter NormedSpace Topology
open scoped ComplexOrder Matrix

noncomputable section

namespace Matrix

section DyadicTracePowers

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Reassociating `(U * V) ^ m` between `V` and `U` yields `(V * U) ^ (m + 1)`. -/
private theorem mul_pow_mul_eq (U V : Matrix n n 𝕜) :
    ∀ m : ℕ, V * (U * V) ^ m * U = (V * U) ^ (m + 1)
  | 0 => by simp
  | m + 1 => by
    calc V * (U * V) ^ (m + 1) * U
        = (V * U) * (V * (U * V) ^ m * U) := by
            rw [pow_succ']
            simp only [Matrix.mul_assoc]
      _ = (V * U) * (V * U) ^ (m + 1) := by rw [mul_pow_mul_eq U V m]
      _ = (V * U) ^ (m + 2) := (pow_succ' (V * U) (m + 1)).symm

/-- Positive powers of `U * V` and `V * U` have equal traces. -/
private theorem trace_mul_pow_succ (U V : Matrix n n 𝕜) (m : ℕ) :
    ((U * V) ^ (m + 1)).trace = ((V * U) ^ (m + 1)).trace := by
  calc ((U * V) ^ (m + 1)).trace
      = (U * (V * (U * V) ^ m)).trace := by rw [pow_succ', Matrix.mul_assoc]
    _ = (V * (U * V) ^ m * U).trace := Matrix.trace_mul_comm U _
    _ = ((V * U) ^ (m + 1)).trace := by rw [mul_pow_mul_eq]

/-- Dyadic powers of `U * V` and `V * U` have equal traces. -/
private theorem trace_mul_two_pow (U V : Matrix n n 𝕜) (k : ℕ) :
    ((U * V) ^ (2 ^ k)).trace = ((V * U) ^ (2 ^ k)).trace := by
  have hk : 2 ^ k = (2 ^ k - 1) + 1 := (Nat.sub_add_cancel (Nat.two_pow_pos k)).symm
  rw [hk, trace_mul_pow_succ]

section FrobeniusHelpers

open scoped InnerProductSpace Matrix.Norms.Frobenius

private theorem frobenius_norm_eq_sqrt_re_trace (X : Matrix n n 𝕜) :
    ‖X‖ = √(RCLike.re (Xᴴ * X).trace) := by
  rw [← frobenius_inner_eq_trace_conjTranspose_mul, inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg X)]

private theorem re_trace_hermitian_two_pow_succ_nonneg {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (k : ℕ) :
    0 ≤ RCLike.re (H ^ (2 ^ (k + 1))).trace := by
  have hpow : H ^ (2 ^ (k + 1)) = (H ^ (2 ^ k))ᴴ * H ^ (2 ^ k) := by
    rw [(hH.pow (2 ^ k)).eq, ← sq, ← pow_mul, ← pow_succ]
  rw [hpow, ← frobenius_inner_eq_trace_conjTranspose_mul, inner_self_eq_norm_sq]
  positivity

/-- Base case `k = 0`: Cauchy–Schwarz for `Tr (A * B)` with Hermitian `A` and `B`. -/
private theorem re_trace_mul_le_sqrt_mul_sqrt {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (A * B).trace ≤ √(RCLike.re (A ^ 2).trace) * √(RCLike.re (B ^ 2).trace) := by
  calc RCLike.re (A * B).trace
      = RCLike.re ⟪A, B⟫_𝕜 := by rw [frobenius_inner_eq_trace_conjTranspose_mul, hA.eq]
    _ ≤ ‖A‖ * ‖B‖ := re_inner_le_norm A B
    _ = √(RCLike.re (A ^ 2).trace) * √(RCLike.re (B ^ 2).trace) := by
        rw [frobenius_norm_eq_sqrt_re_trace, frobenius_norm_eq_sqrt_re_trace, hA.eq, hB.eq, sq, sq]

/-- Base case `k = 0`: `Re Tr (Y ^ 2) ≤ Re Tr (Yᴴ * Y)` for every square matrix `Y`. -/
private theorem re_trace_sq_le_re_trace_conjTranspose_mul (Y : Matrix n n 𝕜) :
    RCLike.re (Y ^ 2).trace ≤ RCLike.re (Yᴴ * Y).trace := by
  have hnorm_conj : ‖Yᴴ‖ = ‖Y‖ := by
    rw [frobenius_norm_eq_sqrt_re_trace, frobenius_norm_eq_sqrt_re_trace,
      conjTranspose_conjTranspose, Matrix.trace_mul_comm Y Yᴴ]
  calc RCLike.re (Y ^ 2).trace
      = RCLike.re ⟪Yᴴ, Y⟫_𝕜 := by
          rw [frobenius_inner_eq_trace_conjTranspose_mul, conjTranspose_conjTranspose, sq]
    _ ≤ ‖Yᴴ‖ * ‖Y‖ := re_inner_le_norm Yᴴ Y
    _ = ‖Y‖ ^ 2 := by rw [hnorm_conj, sq]
    _ = RCLike.re (Yᴴ * Y).trace := by
        rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), frobenius_inner_eq_trace_conjTranspose_mul]

/-- Mutual induction establishing the dyadic Cauchy–Schwarz and singular-value trace bounds. -/
private theorem dyadic_trace_bounds :
    ∀ k : ℕ,
      (∀ {A B : Matrix n n 𝕜}, A.IsHermitian → B.IsHermitian →
        RCLike.re ((A * B) ^ (2 ^ k)).trace ≤
          √(RCLike.re (A ^ (2 ^ (k + 1))).trace) * √(RCLike.re (B ^ (2 ^ (k + 1))).trace)) ∧
      (∀ Y : Matrix n n 𝕜,
        RCLike.re (Y ^ (2 ^ (k + 1))).trace ≤ RCLike.re ((Yᴴ * Y) ^ (2 ^ k)).trace)
  | 0 =>
    ⟨fun hA hB ↦ by simpa using re_trace_mul_le_sqrt_mul_sqrt hA hB,
      fun Y ↦ by simpa using re_trace_sq_le_re_trace_conjTranspose_mul Y⟩
  | k + 1 => by
    obtain ⟨ihP, ihQ⟩ := dyadic_trace_bounds k
    refine ⟨fun {A B} hA hB ↦ ?_, fun Y ↦ ?_⟩
    · have hcyc : (((A * B)ᴴ * (A * B)) ^ (2 ^ k)).trace = ((A ^ 2 * B ^ 2) ^ (2 ^ k)).trace := by
        have hmul : (A * B)ᴴ * (A * B) = B * (A ^ 2 * B) := by
          rw [conjTranspose_mul, hA.eq, hB.eq, sq]
          simp only [Matrix.mul_assoc]
        rw [hmul, trace_mul_two_pow B (A ^ 2 * B), Matrix.mul_assoc, ← sq]
      calc RCLike.re ((A * B) ^ (2 ^ (k + 1))).trace
          ≤ RCLike.re (((A * B)ᴴ * (A * B)) ^ (2 ^ k)).trace := ihQ (A * B)
        _ = RCLike.re ((A ^ 2 * B ^ 2) ^ (2 ^ k)).trace := by rw [hcyc]
        _ ≤ √(RCLike.re ((A ^ 2) ^ (2 ^ (k + 1))).trace) *
              √(RCLike.re ((B ^ 2) ^ (2 ^ (k + 1))).trace) := ihP (hA.pow 2) (hB.pow 2)
        _ = √(RCLike.re (A ^ (2 ^ (k + 2))).trace) *
              √(RCLike.re (B ^ (2 ^ (k + 2))).trace) := by
              simp only [← pow_mul, ← pow_succ']
    · have hsq : Y ^ (2 ^ (k + 2)) = (Y ^ 2) ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, ← pow_succ']
      have hcyc : (((Y ^ 2)ᴴ * Y ^ 2) ^ (2 ^ k)).trace =
          (((Yᴴ * Y) * (Y * Yᴴ)) ^ (2 ^ k)).trace := by
        have hmul : (Y ^ 2)ᴴ * Y ^ 2 = Yᴴ * ((Yᴴ * Y) * Y) := by
          simp only [sq, conjTranspose_mul, Matrix.mul_assoc]
        rw [hmul, trace_mul_two_pow Yᴴ ((Yᴴ * Y) * Y), Matrix.mul_assoc]
      have hH₁ : (Yᴴ * Y).IsHermitian := isHermitian_conjTranspose_mul_self Y
      have hH₂ : (Y * Yᴴ).IsHermitian := isHermitian_mul_conjTranspose_self Y
      have htr_eq : ((Y * Yᴴ) ^ (2 ^ (k + 1))).trace = ((Yᴴ * Y) ^ (2 ^ (k + 1))).trace :=
        trace_mul_two_pow Y Yᴴ (k + 1)
      calc RCLike.re (Y ^ (2 ^ (k + 2))).trace
          = RCLike.re ((Y ^ 2) ^ (2 ^ (k + 1))).trace := by rw [hsq]
        _ ≤ RCLike.re (((Y ^ 2)ᴴ * Y ^ 2) ^ (2 ^ k)).trace := ihQ (Y ^ 2)
        _ = RCLike.re (((Yᴴ * Y) * (Y * Yᴴ)) ^ (2 ^ k)).trace := by rw [hcyc]
        _ ≤ √(RCLike.re ((Yᴴ * Y) ^ (2 ^ (k + 1))).trace) *
              √(RCLike.re ((Y * Yᴴ) ^ (2 ^ (k + 1))).trace) := ihP hH₁ hH₂
        _ = RCLike.re ((Yᴴ * Y) ^ (2 ^ (k + 1))).trace := by
              rw [htr_eq, Real.mul_self_sqrt (re_trace_hermitian_two_pow_succ_nonneg hH₁ k)]

end FrobeniusHelpers

/-- For every square matrix `Y` and `k : ℕ`,
`RCLike.re (Y ^ (2 ^ (k + 1))).trace ≤ RCLike.re ((Yᴴ * Y) ^ (2 ^ k)).trace`. -/
theorem re_trace_pow_two_pow_succ_le (Y : Matrix n n 𝕜) (k : ℕ) :
    RCLike.re (Y ^ (2 ^ (k + 1))).trace ≤ RCLike.re ((Yᴴ * Y) ^ (2 ^ k)).trace :=
  (dyadic_trace_bounds k).2 Y

/-- For Hermitian matrices `A` and `B`,
`RCLike.re ((A * B) ^ (2 ^ k)).trace ≤ RCLike.re (A ^ (2 ^ k) * B ^ (2 ^ k)).trace`. -/
theorem IsHermitian.re_trace_mul_pow_two_pow_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∀ k : ℕ, RCLike.re ((A * B) ^ (2 ^ k)).trace ≤ RCLike.re (A ^ (2 ^ k) * B ^ (2 ^ k)).trace
  | 0 => by simp
  | k + 1 => by
    have hcyc : (((A * B)ᴴ * (A * B)) ^ (2 ^ k)).trace = ((A ^ 2 * B ^ 2) ^ (2 ^ k)).trace := by
      have hmul : (A * B)ᴴ * (A * B) = B * (A ^ 2 * B) := by
        rw [conjTranspose_mul, hA.eq, hB.eq, sq]
        simp only [Matrix.mul_assoc]
      rw [hmul, trace_mul_two_pow B (A ^ 2 * B), Matrix.mul_assoc, ← sq]
    calc RCLike.re ((A * B) ^ (2 ^ (k + 1))).trace
        ≤ RCLike.re (((A * B)ᴴ * (A * B)) ^ (2 ^ k)).trace :=
          re_trace_pow_two_pow_succ_le (A * B) k
      _ = RCLike.re ((A ^ 2 * B ^ 2) ^ (2 ^ k)).trace := by rw [hcyc]
      _ ≤ RCLike.re ((A ^ 2) ^ (2 ^ k) * (B ^ 2) ^ (2 ^ k)).trace :=
          (hA.pow 2).re_trace_mul_pow_two_pow_le (hB.pow 2) k
      _ = RCLike.re (A ^ (2 ^ (k + 1)) * B ^ (2 ^ (k + 1))).trace := by
          simp only [← pow_mul, ← pow_succ']

end DyadicTracePowers

section GoldenThompson

open scoped Matrix.Norms.L2Operator

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **Golden–Thompson inequality** (real-part form): for Hermitian matrices `A` and `B`,
`RCLike.re (exp (A + B)).trace ≤ RCLike.re (exp A * exp B).trace`. -/
theorem IsHermitian.re_trace_exp_add_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (NormedSpace.exp (A + B)).trace ≤
      RCLike.re (NormedSpace.exp A * NormedSpace.exp B).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have htrotter :
      Tendsto (fun k : ℕ ↦
        (NormedSpace.exp (((2 ^ k : ℕ) : ℝ)⁻¹ • A) *
          NormedSpace.exp (((2 ^ k : ℕ) : ℝ)⁻¹ • B)) ^ (2 ^ k))
        atTop (𝓝 (NormedSpace.exp (A + B))) :=
    (tendsto_exp_inv_smul_mul_exp_inv_smul_pow A B).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hcont : Continuous (fun X : Matrix n n 𝕜 ↦ RCLike.re X.trace) :=
    RCLike.continuous_re.comp (Continuous.matrix_trace continuous_id)
  refine le_of_tendsto' (hcont.continuousAt.tendsto.comp htrotter) fun k ↦ ?_
  have hpos : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
  have hAk : (NormedSpace.exp (((2 ^ k : ℕ) : ℝ)⁻¹ • A)).IsHermitian :=
    (hA.smul (IsSelfAdjoint.all (((2 ^ k : ℕ) : ℝ)⁻¹))).posDef_exp.isHermitian
  have hBk : (NormedSpace.exp (((2 ^ k : ℕ) : ℝ)⁻¹ • B)).IsHermitian :=
    (hB.smul (IsSelfAdjoint.all (((2 ^ k : ℕ) : ℝ)⁻¹))).posDef_exp.isHermitian
  have hpowA : (NormedSpace.exp (((2 ^ k : ℕ) : ℝ)⁻¹ • A)) ^ (2 ^ k) = NormedSpace.exp A := by
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have hpowB : (NormedSpace.exp (((2 ^ k : ℕ) : ℝ)⁻¹ • B)) ^ (2 ^ k) = NormedSpace.exp B := by
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  simpa only [Function.comp_def, hpowA, hpowB] using hAk.re_trace_mul_pow_two_pow_le hBk k

/-- **Golden–Thompson inequality**: for Hermitian matrices `A` and `B`,
`(exp (A + B)).trace ≤ (exp A * exp B).trace` in the `RCLike` order. -/
theorem IsHermitian.trace_exp_add_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (NormedSpace.exp (A + B)).trace ≤ (NormedSpace.exp A * NormedSpace.exp B).trace := by
  have hnonneg_lhs : 0 ≤ (NormedSpace.exp (A + B)).trace :=
    (hA.add hB).posDef_exp.posSemidef.trace_nonneg
  have hnonneg_rhs : 0 ≤ (NormedSpace.exp A * NormedSpace.exp B).trace := by
    open scoped MatrixOrder in
    exact hA.trace_exp_mul_nonneg hB.posDef_exp.posSemidef.nonneg
  rw [RCLike.le_iff_re_im]
  exact ⟨hA.re_trace_exp_add_le hB,
    (RCLike.nonneg_iff.1 hnonneg_lhs).2.trans (RCLike.nonneg_iff.1 hnonneg_rhs).2.symm⟩

end GoldenThompson

end Matrix
