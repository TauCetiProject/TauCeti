/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Compressible
public import TauCeti.MeasureTheory.Integral.Lebesgue.Encard

import TauCeti.MeasureTheory.Measure.Real

/-!
# Invertibility on incompressible vectors via column distances

If a linear combination with incompressible unit coefficients is small, many columns are close
to the spans of the remaining columns. The bad-event measure is bounded by the sum of the
column-distance measures divided by `k + 1`. When `k` is proportional to the number of columns,
this avoids the column-count factor of a union bound. The columns may be dependent and need
not have the same law.

We work with finite families in a seminormed space, so the result applies to rectangular real or
complex matrices. The threshold is `ε ρ / √n` for the unnormalized matrix, where
`n = Fintype.card ι` is the number of columns.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), Lemma 3.5.
-/

public section

open Finset MeasureTheory Metric Set

open scoped ENNReal

namespace TauCeti

variable {𝕜 E ι : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Fintype ι]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Invertibility via distance.** The outer measure of a small linear combination with
incompressible unit coefficients is bounded by the sum of the column-distance outer measures
divided by `k + 1`. No measurability or finiteness assumptions are needed. -/
theorem measure_exists_isIncompressibleVector_norm_sum_lt_le
    {k : ℕ} {ρ a ε : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a)
    (haρ : (Fintype.card ι : ℝ) * a ^ 2 ≤ ρ ^ 2) (v : Ω → ι → E) :
    P {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖∑ i, x i • v ω i‖ < a * ε} ≤
      (∑ i, P {ω | infDist (v ω i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v ω j) : Set E) < ε}) /
        (k + 1 : ℝ≥0∞) := by
  apply le_trans (measure_mono ?_) (measure_lt_card_filter_le (P := P) univ _ k)
  rintro ω ⟨x, hx, hsmall⟩
  exact hx.lt_card_filter_infDist_span_range_ne hρ ha haρ (v ω) hsmall

/-- The `ε ρ / √n` outer-measure bound, also valid for an empty column type. -/
theorem measure_exists_isIncompressibleVector_norm_sum_lt_div_sqrt_mul_le
    {k : ℕ} {ρ ε : ℝ} (hρ : 0 ≤ ρ) (v : Ω → ι → E) :
    P {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖∑ i, x i • v ω i‖ < ρ / Real.sqrt (Fintype.card ι) * ε} ≤
      (∑ i, P {ω | infDist (v ω i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v ω j) : Set E) < ε}) /
        (k + 1 : ℝ≥0∞) := by
  apply measure_exists_isIncompressibleVector_norm_sum_lt_le hρ (by positivity) _ v
  by_cases hn : Fintype.card ι = 0
  · simp [hn, sq_nonneg]
  · have hnp : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_pow, Real.sq_sqrt hnp.le]
    exact (mul_div_cancel₀ (ρ ^ 2) (ne_of_gt hnp)).le

/-- The outer-measure matrix form of invertibility via distance for rectangular real or complex
matrices, with no measurability, independence, or finite-measure assumptions. -/
theorem measure_exists_isIncompressibleVector_norm_toEuclideanLin_lt_le
    {κ : Type*} [Fintype κ] [DecidableEq ι]
    {k : ℕ} {ρ ε : ℝ} (hρ : 0 ≤ ρ) (A : Ω → Matrix κ ι 𝕜) :
    P {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖Matrix.toEuclideanLin (A ω) x‖ < ρ / Real.sqrt (Fintype.card ι) * ε} ≤
      (∑ i, P {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦
          WithLp.toLp 2 fun r ↦ A ω r j) : Set (EuclideanSpace 𝕜 κ)) < ε}) /
        (k + 1 : ℝ≥0∞) := by
  have hsum (ω : Ω) (x : EuclideanSpace 𝕜 ι) :
      (∑ i, x i • (WithLp.toLp 2 fun r ↦ A ω r i : EuclideanSpace 𝕜 κ)) =
        Matrix.toEuclideanLin (A ω) x := by
    ext r
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm]
  simpa only [hsum] using measure_exists_isIncompressibleVector_norm_sum_lt_div_sqrt_mul_le
    (𝕜 := 𝕜) (k := k) (ε := ε) hρ
    (fun ω i ↦ (WithLp.toLp 2 fun r ↦ A ω r i : EuclideanSpace 𝕜 κ))

variable [IsFiniteMeasure P]

/-- The real-valued finite-measure form of invertibility via distance. The bad-event measure
is bounded by the sum of the column-distance measures divided by `k + 1`. -/
theorem measureReal_exists_isIncompressibleVector_norm_sum_lt_le
    {k : ℕ} {ρ a ε : ℝ} (hρ : 0 ≤ ρ) (ha : 0 ≤ a)
    (haρ : (Fintype.card ι : ℝ) * a ^ 2 ≤ ρ ^ 2) (v : Ω → ι → E) :
    P.real {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖∑ i, x i • v ω i‖ < a * ε} ≤
      (∑ i, P.real {ω | infDist (v ω i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v ω j) : Set E) < ε}) /
        (k + 1 : ℝ) := by
  simpa [ENNReal.toReal_add] using
    P.measureReal_le_sum_div_of_le (by positivity : (k + 1 : ℝ≥0∞) ≠ 0)
    (measure_exists_isIncompressibleVector_norm_sum_lt_le
      (𝕜 := 𝕜) (k := k) (ε := ε) hρ ha haρ v)

/-- The real-valued `ε ρ / √n` bound, valid also for an empty column type. In that case there
are no unit coefficient vectors and both sides vanish. -/
theorem measureReal_exists_isIncompressibleVector_norm_sum_lt_div_sqrt_mul_le
    {k : ℕ} {ρ ε : ℝ} (hρ : 0 ≤ ρ) (v : Ω → ι → E) :
    P.real {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖∑ i, x i • v ω i‖ < ρ / Real.sqrt (Fintype.card ι) * ε} ≤
      (∑ i, P.real {ω | infDist (v ω i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v ω j) : Set E) < ε}) /
        (k + 1 : ℝ) := by
  simpa [ENNReal.toReal_add] using
    P.measureReal_le_sum_div_of_le (by positivity : (k + 1 : ℝ≥0∞) ≠ 0)
    (measure_exists_isIncompressibleVector_norm_sum_lt_div_sqrt_mul_le
      (𝕜 := 𝕜) (k := k) (ε := ε) hρ v)

/-- The real-valued matrix bound for rectangular real or complex matrices. The distances are
Euclidean distances between columns and the spans of the other columns; `A` is unnormalized. -/
theorem measureReal_exists_isIncompressibleVector_norm_toEuclideanLin_lt_le
    {κ : Type*} [Fintype κ] [DecidableEq ι]
    {k : ℕ} {ρ ε : ℝ} (hρ : 0 ≤ ρ) (A : Ω → Matrix κ ι 𝕜) :
    P.real {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖Matrix.toEuclideanLin (A ω) x‖ < ρ / Real.sqrt (Fintype.card ι) * ε} ≤
      (∑ i, P.real {ω | infDist (WithLp.toLp 2 fun r ↦ A ω r i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦
          WithLp.toLp 2 fun r ↦ A ω r j) : Set (EuclideanSpace 𝕜 κ)) < ε}) /
        (k + 1 : ℝ) := by
  simpa [ENNReal.toReal_add] using
    P.measureReal_le_sum_div_of_le (by positivity : (k + 1 : ℝ≥0∞) ≠ 0)
    (measure_exists_isIncompressibleVector_norm_toEuclideanLin_lt_le
      (k := k) (ε := ε) hρ A)

end TauCeti
