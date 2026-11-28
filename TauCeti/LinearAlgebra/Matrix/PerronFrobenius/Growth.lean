/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Asymptotics.ExpGrowth
public import TauCeti.LinearAlgebra.Matrix.PerronFrobenius.Nonnegative
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import TauCeti.Analysis.Asymptotics.ExpGrowth
import TauCeti.LinearAlgebra.Matrix.OfReal

/-!
# Exponential growth of the entry sums of powers of a matrix

For a real square matrix `M`, the sums `∑ i, (M ^ n *ᵥ 1) i` of all entries of its powers grow
exponentially at most like the spectral radius `ρ` of `M` viewed as a complex matrix: each row sum
of `M ^ n` is bounded by the `L∞` operator norm of `M ^ n`, whose `n`-th roots tend to `ρ` by
Gelfand's formula. If `M` is entrywise nonnegative, `ρ` is also the real spectral radius
`spectralRadius ℝ M` (`Matrix.spectralRadius_real_eq_of_nonneg`), and the sums grow at least like
`ρ`, by the Perron–Frobenius theorem: a nonzero nonnegative eigenvector `v` for `ρ` gives
`ρ ^ n ∑ v ≤ (∑ v) ∑ i, (M ^ n *ᵥ 1) i`. So for a nonnegative matrix the upper exponential growth
of these sums is exactly `log ρ`.

## Main results

* `Matrix.expGrowthSup_sum_pow_mulVec_le`: the entry sums of `M ^ n` grow at most like the
  spectral radius of `M` viewed as a complex matrix.
* `Matrix.log_le_expGrowthInf_sum_pow_mulVec`: for a nonnegative matrix they grow at least like
  the spectral radius.
* `Matrix.expGrowthSup_sum_pow_mulVec_eq`: for a nonnegative matrix their upper exponential growth
  is `log (spectralRadius ℝ M)`.
-/

public section

open Filter ExpGrowth
open scoped Matrix ENNReal NNReal

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entry sums `∑ i, (M ^ k *ᵥ 1) i` of the powers of a real square matrix grow at most like
the spectral radius of `M` viewed as a complex matrix. -/
theorem expGrowthSup_sum_pow_mulVec_le (M : Matrix n n ℝ) :
    expGrowthSup (fun k ↦ ENNReal.ofReal (∑ i, (M ^ k *ᵥ 1) i)) ≤
      ENNReal.log (spectralRadius ℂ (M.map (↑) : Matrix n n ℂ)) := by
  let := Matrix.linftyOpNormedRing (n := n) (α := ℂ)
  let := Matrix.linftyOpNormedAlgebra (R := ℂ) (n := n) (α := ℂ)
  set N : Matrix n n ℂ := M.map (↑)
  have hbound (k : ℕ) : ENNReal.ofReal (∑ i, (M ^ k *ᵥ 1) i) ≤
      (Fintype.card n : ℝ≥0∞) * (‖N ^ k‖₊ : ℝ≥0∞) := by
    have hrow (i : n) : (M ^ k *ᵥ 1) i ≤ ‖N ^ k‖ := by
      have hk : (N ^ k *ᵥ 1) i = ((M ^ k *ᵥ 1) i : ℂ) := by
        have hpow : (M ^ k).map (↑) = N ^ k := Matrix.map_pow M Complex.ofRealHom k
        simpa [hpow, ← Pi.one_def] using congrFun (map_ofReal_mulVec (M ^ k) 1) i
      calc (M ^ k *ᵥ 1) i ≤ ‖(N ^ k *ᵥ 1) i‖ := by
            rw [hk, Complex.norm_real, Real.norm_eq_abs]
            exact le_abs_self _
        _ ≤ ‖N ^ k *ᵥ 1‖ := norm_le_pi_norm _ i
        _ ≤ ‖N ^ k‖ * ‖(1 : n → ℂ)‖ := linfty_opNorm_mulVec _ _
        _ ≤ ‖N ^ k‖ := mul_le_of_le_one_right (norm_nonneg _)
            ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun _ ↦ by simp)
    calc ENNReal.ofReal (∑ i, (M ^ k *ᵥ 1) i) ≤ ENNReal.ofReal (Fintype.card n * ‖N ^ k‖) := by
          gcongr
          simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hrow i
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ofReal_norm,
            eNorm_eq_nnNorm]
  calc _ ≤ expGrowthSup fun k ↦ (‖N ^ k‖₊ : ℝ≥0∞) :=
        expGrowthSup_le_of_eventually_le (ENNReal.natCast_ne_top _) (Eventually.of_forall hbound)
    _ = _ := expGrowthSup_eq_log_of_tendsto_rpow (spectrum.gelfand_formula N)

/-- The entry sums `∑ i, (M ^ k *ᵥ 1) i` of the powers of an entrywise nonnegative real square
matrix grow at least like its spectral radius, by the Perron–Frobenius theorem. -/
theorem log_le_expGrowthInf_sum_pow_mulVec {M : Matrix n n ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    ENNReal.log (spectralRadius ℂ (M.map (↑) : Matrix n n ℂ)) ≤
      expGrowthInf (fun k ↦ ENNReal.ofReal (∑ i, (M ^ k *ᵥ 1) i)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [spectralRadius]
  obtain ⟨r, hr, hρ, v, hv, hv0, hMv⟩ := exists_mulVec_eq_smul_of_nonneg hM
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hv0
  set D : ℝ := ∑ i, v i
  have hD : 0 < D := Finset.sum_pos' (fun i _ ↦ hv i) ⟨j, Finset.mem_univ j, (hv j).lt_of_ne' hj⟩
  have hle (k : ℕ) : r ^ k * D ≤ D * ∑ i, (M ^ k *ᵥ 1) i := by
    have hvD : v ≤ D • (1 : n → ℝ) := fun i ↦ by
      simpa using Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hv i) (Finset.mem_univ i)
    have hmono : M ^ k *ᵥ v ≤ M ^ k *ᵥ (D • (1 : n → ℝ)) := fun i ↦
      Finset.sum_le_sum fun l _ ↦ mul_le_mul_of_nonneg_left (hvD l) (pow_apply_nonneg hM k i l)
    rw [pow_mulVec_eq_pow_smul hMv, mulVec_smul] at hmono
    calc r ^ k * D = ∑ i, (r ^ k • v) i := by simp [D, Finset.mul_sum]
      _ ≤ ∑ i, (D • (M ^ k *ᵥ 1)) i := Finset.sum_le_sum fun i _ ↦ hmono i
      _ = D * ∑ i, (M ^ k *ᵥ 1) i := by simp [Finset.mul_sum]
  rw [hρ, ← expGrowthInf_pow]
  refine expGrowthInf_monotone fun k ↦ ?_
  rw [← ENNReal.ofReal_pow hr]
  exact ENNReal.ofReal_le_ofReal (le_of_mul_le_mul_right (by linarith [hle k]) hD)

/-- For an entrywise nonnegative real square matrix `M`, the entry sums `∑ i, (M ^ k *ᵥ 1) i` of
its powers have upper exponential growth `log (spectralRadius ℝ M)`. -/
theorem expGrowthSup_sum_pow_mulVec_eq {M : Matrix n n ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    expGrowthSup (fun k ↦ ENNReal.ofReal (∑ i, (M ^ k *ᵥ 1) i)) =
      ENNReal.log (spectralRadius ℝ M) := by
  rw [spectralRadius_real_eq_of_nonneg hM]
  exact (expGrowthSup_sum_pow_mulVec_le M).antisymm
    ((log_le_expGrowthInf_sum_pow_mulVec hM).trans expGrowthInf_le_expGrowthSup)

end Matrix
