/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.MeanInequalities
import TauCeti.Analysis.Matrix.Sqrt

/-!
# The trace–determinant inequality and its equality case

For positive-semidefinite `n × n` matrices `A` and `B` over `ℝ` or `ℂ`,
`n * (det A * det B) ^ (1 / n) ≤ Re tr (A * B)`. For positive-definite `A` and `B` equality holds
exactly when `B = c • A⁻¹` for some `c > 0`. This is the arithmetic–geometric step of the
complex Hessian equation estimates: apply the inequality of arithmetic and geometric means to the
eigenvalues of `A ^ (1 / 2) * B * A ^ (1 / 2)`.

Determinants and traces of Hermitian matrices are real; the statements take their real parts.

## Main results

* `Matrix.PosSemidef.card_mul_re_det_rpow_le_re_trace`: `n * (det N) ^ (1 / n) ≤ tr N` for a
  positive-semidefinite `N`, with equality exactly when `N` is a real multiple of `1`
  (`Matrix.PosSemidef.card_mul_re_det_rpow_eq_re_trace_iff`).
* `Matrix.PosSemidef.card_mul_re_det_mul_det_rpow_le_re_trace_mul`: the two-matrix inequality.
* `Matrix.PosDef.card_mul_re_det_mul_det_rpow_eq_re_trace_mul_iff`: its equality case.

## References

* B. Guo, D. H. Phong and F. Tong, *On L^∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023).
-/

public section

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- A Hermitian matrix whose eigenvalues are all equal to `c` is `c • 1`. -/
theorem IsHermitian.eq_smul_one_of_eigenvalues_eq {N : Matrix n n 𝕜} (hN : N.IsHermitian)
    {c : ℝ} (hc : ∀ i, hN.eigenvalues i = c) : N = c • (1 : Matrix n n 𝕜) := by
  have hdiag : diagonal (RCLike.ofReal ∘ hN.eigenvalues) = algebraMap 𝕜 (Matrix n n 𝕜) c := by
    ext i j
    simp [hc, diagonal_apply, algebraMap_matrix_apply]
  rw [hN.spectral_theorem, hdiag, AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one,
    ← RCLike.real_smul_eq_coe_smul]

/-- **The determinant–trace inequality.** For a positive-semidefinite `n × n` matrix `N`,
`n * (det N) ^ (1 / n) ≤ tr N`: the inequality of arithmetic and geometric means for the
eigenvalues. For `n = 0` both sides are `0`. -/
theorem PosSemidef.card_mul_re_det_rpow_le_re_trace {N : Matrix n n 𝕜} (hN : N.PosSemidef) :
    Fintype.card n * RCLike.re N.det ^ (Fintype.card n : ℝ)⁻¹ ≤ RCLike.re N.trace := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  set μ := hN.isHermitian.eigenvalues
  have hμ := hN.eigenvalues_nonneg
  have hcard : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => (Fintype.card n : ℝ)⁻¹) μ (fun _ _ => by positivity)
    (by simp [Finset.card_univ, hcard]) fun i _ => hμ i
  rw [Real.finsetProd_rpow _ _ fun i _ => hμ i, ← Finset.mul_sum] at hamgm
  rw [hN.isHermitian.det_eq_prod_eigenvalues, hN.isHermitian.trace_eq_sum_eigenvalues,
    ← RCLike.ofReal_prod, ← RCLike.ofReal_sum, RCLike.ofReal_re, RCLike.ofReal_re]
  calc (Fintype.card n : ℝ) * (∏ i, μ i) ^ (Fintype.card n : ℝ)⁻¹
      ≤ Fintype.card n * ((Fintype.card n : ℝ)⁻¹ * ∑ i, μ i) := by gcongr
    _ = ∑ i, μ i := by field_simp

/-- **The equality case of the determinant–trace inequality.** For a positive-semidefinite
`n × n` matrix `N`, `n * (det N) ^ (1 / n) = tr N` exactly when `N` is a real multiple of `1`. -/
theorem PosSemidef.card_mul_re_det_rpow_eq_re_trace_iff {N : Matrix n n 𝕜}
    (hN : N.PosSemidef) :
    Fintype.card n * RCLike.re N.det ^ (Fintype.card n : ℝ)⁻¹ = RCLike.re N.trace ↔
      ∃ c : ℝ, N = c • (1 : Matrix n n 𝕜) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => by simp⟩
  have i₀ : n := Classical.arbitrary n
  have hcard : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨fun h => ?_, ?_⟩
  · set μ := hN.isHermitian.eigenvalues
    have hμ := hN.eigenvalues_nonneg
    have hamgm := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos Finset.univ
      (fun _ => (Fintype.card n : ℝ)⁻¹) μ (fun _ _ => by positivity)
      (by simp [Finset.card_univ, hcard]) fun i _ => hμ i
    rw [Real.finsetProd_rpow _ _ fun i _ => hμ i, ← Finset.mul_sum] at hamgm
    rw [hN.isHermitian.det_eq_prod_eigenvalues, hN.isHermitian.trace_eq_sum_eigenvalues,
      ← RCLike.ofReal_prod, ← RCLike.ofReal_sum, RCLike.ofReal_re, RCLike.ofReal_re,
      ← mul_right_inj' (inv_ne_zero hcard), ← mul_assoc, inv_mul_cancel₀ hcard, one_mul,
      hamgm] at h
    exact ⟨μ i₀, hN.isHermitian.eq_smul_one_of_eigenvalues_eq fun i =>
      h i (Finset.mem_univ _) i₀ (Finset.mem_univ _)⟩
  · rintro ⟨c, rfl⟩
    have hc : 0 ≤ c := by
      simpa [RCLike.real_smul_eq_coe_mul] using hN.diag_nonneg (i := i₀)
    simp only [det_smul_of_tower, det_one, trace_smul, trace_one, RCLike.smul_re, RCLike.one_re,
      mul_one, RCLike.natCast_re]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc, mul_inv_cancel₀ hcard, Real.rpow_one, mul_comm]

/-- **The trace–determinant inequality.** For positive-semidefinite `n × n` matrices `A` and `B`,
`n * (det A * det B) ^ (1 / n) ≤ Re tr (A * B)`. -/
theorem PosSemidef.card_mul_re_det_mul_det_rpow_le_re_trace_mul {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    Fintype.card n * RCLike.re (A.det * B.det) ^ (Fintype.card n : ℝ)⁻¹ ≤
      RCLike.re (A * B).trace := by
  set S := CFC.sqrt A
  have hS : S.IsHermitian := (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg A)).isHermitian
  have hN : (S * B * S).PosSemidef := by
    simpa only [hS.eq] using hB.mul_mul_conjTranspose_same S
  have hdet : (S * B * S).det = A.det * B.det := by
    rw [← CFC.sqrt_mul_sqrt_self A hA.nonneg]
    simp only [det_mul, S]
    ring
  rw [← hdet, ← trace_mul_comm, ← hA.trace_sqrt_mul_mul_sqrt]
  exact hN.card_mul_re_det_rpow_le_re_trace

/-- **The equality case of the trace–determinant inequality.** For positive-definite `n × n`
matrices `A` and `B`, `n * (det A * det B) ^ (1 / n) = Re tr (A * B)` exactly when
`B = c • A⁻¹` for some `c > 0`. -/
theorem PosDef.card_mul_re_det_mul_det_rpow_eq_re_trace_mul_iff {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) :
    Fintype.card n * RCLike.re (A.det * B.det) ^ (Fintype.card n : ℝ)⁻¹ =
      RCLike.re (A * B).trace ↔ ∃ c : ℝ, 0 < c ∧ B = c • A⁻¹ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨fun _ => ⟨1, one_pos, Subsingleton.elim _ _⟩, fun _ => by simp⟩
  set S := CFC.sqrt A
  have hS : S.IsHermitian := (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg A)).isHermitian
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSu : IsUnit S.det := hA.isUnit_det_sqrt
  have hN : (S * B * S).PosDef := by
    simpa only [hS.eq] using hB.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det S).2 hSu))
  have hdet : (S * B * S).det = A.det * B.det := by
    rw [← hSS]
    simp only [det_mul]
    ring
  rw [← hdet, ← trace_mul_comm, ← hA.posSemidef.trace_sqrt_mul_mul_sqrt,
    hN.posSemidef.card_mul_re_det_rpow_eq_re_trace_iff]
  have hAinv : A⁻¹ = S⁻¹ * S⁻¹ := by rw [← hSS, mul_inv_rev]
  constructor
  · rintro ⟨c, hc⟩
    have hB' : B = c • A⁻¹ := by
      have hBS : B = S⁻¹ * (S * B * S) * S⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSu, Matrix.mul_one,
          ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul]
      rw [hBS, hc, hAinv, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    refine ⟨c, ?_, hB'⟩
    obtain ⟨i⟩ := hn
    have hpos := hN.diag_pos (i := i)
    rw [hc] at hpos
    simpa using hpos
  · rintro ⟨c, -, rfl⟩
    refine ⟨c, ?_⟩
    rw [hAinv, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc S,
      Matrix.mul_nonsing_inv _ hSu, Matrix.one_mul, Matrix.nonsing_inv_mul _ hSu]

end Matrix
