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

For Hermitian matrices `A` and `B` over any `RCLike` field, `Tr (exp (A + B)) ≤ Tr (exp A * exp B)`,
proved via the Cohen–Friedland–Kato–Kelly dyadic trace-power bounds and the Lie–Trotter formula.

## Main results

* `Matrix.re_trace_pow_two_pow_succ_le`, `Matrix.IsHermitian.re_trace_mul_pow_two_pow_le`.
* `Matrix.IsHermitian.re_trace_exp_add_le`, `Matrix.IsHermitian.trace_exp_add_le`:
  **the Golden–Thompson inequality** in real-part and `RCLike`-order forms.

## References

* S. Golden, Phys. Rev. 137 (1965); C. J. Thompson, J. Math. Phys. 6 (1965);
  J. E. Cohen, S. Friedland, T. Kato, F. P. Kelly, Linear Algebra Appl. 45 (1982), 55–95.
-/

public section

open Filter NormedSpace Topology
open scoped ComplexOrder Matrix

noncomputable section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

private theorem mul_pow_mul_eq (U V : Matrix n n 𝕜) :
    ∀ m : ℕ, V * (U * V) ^ m * U = (V * U) ^ (m + 1)
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ' (V * U) (m + 1), ← mul_pow_mul_eq U V m, pow_succ']; simp only [Matrix.mul_assoc]

private theorem trace_mul_two_pow (U V : Matrix n n 𝕜) (k : ℕ) :
    ((U * V) ^ (2 ^ k)).trace = ((V * U) ^ (2 ^ k)).trace := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.two_pow_pos k).ne'
  rw [hm, pow_succ', Matrix.mul_assoc, Matrix.trace_mul_comm U, mul_pow_mul_eq]

private theorem trace_conjTranspose_mul_self_two_pow {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : ℕ) :
    (((A * B)ᴴ * (A * B)) ^ (2 ^ k)).trace = ((A ^ 2 * B ^ 2) ^ (2 ^ k)).trace := by
  rw [show (A * B)ᴴ * (A * B) = B * (A ^ 2 * B) by
    rw [conjTranspose_mul, hA.eq, hB.eq, sq]; simp only [Matrix.mul_assoc],
    trace_mul_two_pow B (A ^ 2 * B), Matrix.mul_assoc, ← sq]

section FrobeniusHelpers

open scoped InnerProductSpace Matrix.Norms.Frobenius

private theorem frobenius_norm_eq_sqrt_re_trace (X : Matrix n n 𝕜) :
    ‖X‖ = √(RCLike.re (Xᴴ * X).trace) := by
  rw [← frobenius_inner_eq_trace_conjTranspose_mul, inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg X)]

private theorem dyadic_trace_bounds :
    ∀ k : ℕ,
      (∀ {A B : Matrix n n 𝕜}, A.IsHermitian → B.IsHermitian →
        RCLike.re ((A * B) ^ (2 ^ k)).trace ≤
          √(RCLike.re (A ^ (2 ^ (k + 1))).trace) * √(RCLike.re (B ^ (2 ^ (k + 1))).trace)) ∧
      (∀ Y : Matrix n n 𝕜,
        RCLike.re (Y ^ (2 ^ (k + 1))).trace ≤ RCLike.re ((Yᴴ * Y) ^ (2 ^ k)).trace)
  | 0 => by
    refine ⟨fun {A B} hA hB ↦ ?_, fun Y ↦ ?_⟩
    · calc RCLike.re ((A * B) ^ (2 ^ 0)).trace
          = RCLike.re ⟪A, B⟫_𝕜 := by
            rw [frobenius_inner_eq_trace_conjTranspose_mul, hA.eq, pow_zero, pow_one]
        _ ≤ ‖A‖ * ‖B‖ := re_inner_le_norm (𝕜 := 𝕜) A B
        _ = √(RCLike.re (A ^ (2 ^ (0 + 1))).trace) *
              √(RCLike.re (B ^ (2 ^ (0 + 1))).trace) := by
            simp [frobenius_norm_eq_sqrt_re_trace, hA.eq, hB.eq, sq]
    · have hnorm_conj : ‖Yᴴ‖ = ‖Y‖ := by
        rw [frobenius_norm_eq_sqrt_re_trace, frobenius_norm_eq_sqrt_re_trace,
          conjTranspose_conjTranspose, Matrix.trace_mul_comm Y Yᴴ]
      calc RCLike.re (Y ^ (2 ^ (0 + 1))).trace
          = RCLike.re ⟪Yᴴ, Y⟫_𝕜 := by
            rw [frobenius_inner_eq_trace_conjTranspose_mul, conjTranspose_conjTranspose]; simp [sq]
        _ ≤ ‖Yᴴ‖ * ‖Y‖ := re_inner_le_norm (𝕜 := 𝕜) Yᴴ Y
        _ = RCLike.re ((Yᴴ * Y) ^ (2 ^ 0)).trace := by
            rw [hnorm_conj, ← sq, ← inner_self_eq_norm_sq (𝕜 := 𝕜),
              frobenius_inner_eq_trace_conjTranspose_mul, pow_zero, pow_one]
  | k + 1 => by
    obtain ⟨ihP, ihQ⟩ := dyadic_trace_bounds k
    refine ⟨fun {A B} hA hB ↦ ?_, fun Y ↦ ?_⟩
    · refine (ihQ (A * B)).trans ?_
      rw [trace_conjTranspose_mul_self_two_pow hA hB k]
      exact (ihP (hA.pow 2) (hB.pow 2)).trans_eq (by simp only [← pow_mul, ← pow_succ'])
    · have hcyc : (((Y ^ 2)ᴴ * Y ^ 2) ^ (2 ^ k)).trace =
          (((Yᴴ * Y) * (Y * Yᴴ)) ^ (2 ^ k)).trace := by
        rw [show (Y ^ 2)ᴴ * Y ^ 2 = Yᴴ * ((Yᴴ * Y) * Y) by
          simp only [sq, conjTranspose_mul, Matrix.mul_assoc],
          trace_mul_two_pow Yᴴ ((Yᴴ * Y) * Y), Matrix.mul_assoc]
      have hH₁ : (Yᴴ * Y).IsHermitian := isHermitian_conjTranspose_mul_self Y
      have hnonneg : 0 ≤ RCLike.re ((Yᴴ * Y) ^ (2 ^ (k + 1))).trace := by
        rw [show (Yᴴ * Y) ^ (2 ^ (k + 1)) = ((Yᴴ * Y) ^ (2 ^ k))ᴴ * (Yᴴ * Y) ^ (2 ^ k) by
          rw [(hH₁.pow (2 ^ k)).eq, ← sq, ← pow_mul, ← pow_succ],
          ← frobenius_inner_eq_trace_conjTranspose_mul, inner_self_eq_norm_sq]
        positivity
      calc RCLike.re (Y ^ (2 ^ (k + 2))).trace
          = RCLike.re ((Y ^ 2) ^ (2 ^ (k + 1))).trace := by rw [← pow_mul, ← pow_succ']
        _ ≤ RCLike.re (((Y ^ 2)ᴴ * Y ^ 2) ^ (2 ^ k)).trace := ihQ (Y ^ 2)
        _ = RCLike.re (((Yᴴ * Y) * (Y * Yᴴ)) ^ (2 ^ k)).trace := by rw [hcyc]
        _ ≤ √(RCLike.re ((Yᴴ * Y) ^ (2 ^ (k + 1))).trace) *
              √(RCLike.re ((Y * Yᴴ) ^ (2 ^ (k + 1))).trace) :=
            ihP hH₁ (isHermitian_mul_conjTranspose_self Y)
        _ = RCLike.re ((Yᴴ * Y) ^ (2 ^ (k + 1))).trace := by
            rw [trace_mul_two_pow Y Yᴴ (k + 1), Real.mul_self_sqrt hnonneg]

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
  | k + 1 =>
    (re_trace_pow_two_pow_succ_le (A * B) k).trans <| by
      rw [trace_conjTranspose_mul_self_two_pow hA hB k]
      exact ((hA.pow 2).re_trace_mul_pow_two_pow_le (hB.pow 2) k).trans_eq <| by
        simp only [← pow_mul, ← pow_succ']

section GoldenThompson

open scoped Matrix.Norms.L2Operator

/-- **Golden–Thompson inequality** (real-part form): for Hermitian matrices `A` and `B`,
`RCLike.re (exp (A + B)).trace ≤ RCLike.re (exp A * exp B).trace`. -/
theorem IsHermitian.re_trace_exp_add_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.re (NormedSpace.exp (A + B)).trace ≤
      RCLike.re (NormedSpace.exp A * NormedSpace.exp B).trace := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have htrotter := (tendsto_exp_inv_smul_mul_exp_inv_smul_pow A B).comp
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hcont : Continuous (fun X : Matrix n n 𝕜 ↦ RCLike.re X.trace) :=
    RCLike.continuous_re.comp (Continuous.matrix_trace continuous_id)
  refine le_of_tendsto' (hcont.continuousAt.tendsto.comp htrotter) fun k ↦ ?_
  have hpos : (0 : ℝ) < (2 ^ k : ℕ) := by positivity
  have hpow (X : Matrix n n 𝕜) :
      (NormedSpace.exp (((2 ^ k : ℕ) : ℝ)⁻¹ • X)) ^ (2 ^ k) = NormedSpace.exp X := by
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  have hsc : IsSelfAdjoint (((2 ^ k : ℕ) : ℝ)⁻¹) := IsSelfAdjoint.all _
  simpa only [Function.comp_def, hpow A, hpow B] using
    (hA.smul hsc).posDef_exp.isHermitian.re_trace_mul_pow_two_pow_le
      (hB.smul hsc).posDef_exp.isHermitian k

/-- **Golden–Thompson inequality**: for Hermitian matrices `A` and `B`,
`(exp (A + B)).trace ≤ (exp A * exp B).trace` in the `RCLike` order. -/
theorem IsHermitian.trace_exp_add_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (NormedSpace.exp (A + B)).trace ≤ (NormedSpace.exp A * NormedSpace.exp B).trace := by
  open scoped MatrixOrder in
  exact RCLike.le_iff_re_im.2 ⟨hA.re_trace_exp_add_le hB,
    (RCLike.nonneg_iff.1 (hA.add hB).posDef_exp.posSemidef.trace_nonneg).2.trans
      (RCLike.nonneg_iff.1 (hA.trace_exp_mul_nonneg hB.posDef_exp.posSemidef.nonneg)).2.symm⟩

end GoldenThompson

end Matrix
