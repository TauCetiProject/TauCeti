/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Compressible
public import TauCeti.Analysis.Normed.Module.FiniteSpan
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

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

/-- A small linear combination with incompressible coefficients forces more than `k` column
distances to be small. The threshold `a` may be any nonnegative number with `n a² ≤ ρ²`. -/
theorem IsIncompressibleVector.lt_card_filter_infDist_span_range_ne
    {k : ℕ} {ρ a ε : ℝ} {x : EuclideanSpace 𝕜 ι} (hx : IsIncompressibleVector k ρ x)
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (haρ : (Fintype.card ι : ℝ) * a ^ 2 ≤ ρ ^ 2)
    (v : ι → E) (hv : ‖∑ i, x i • v i‖ < a * ε) :
    k < (univ.filter fun i ↦ infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) < ε).card := by
  apply (hx.lt_card_filter_norm hρ haρ).trans_le
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hd := norm_mul_infDist_span_range_ne_le v (fun j ↦ x j) i
  have he : 0 < ε := by nlinarith [norm_nonneg (∑ j, x j • v j)]
  by_contra h
  have hεd : ε ≤ infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_left hεd (norm_nonneg (x i))
  nlinarith

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
  classical
  let s (i : ι) : Set Ω := {ω | infDist (v ω i)
    (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v ω j) : Set E) < ε}
  let f (ω : Ω) : ℝ≥0∞ := ∑ i, (toMeasurable P (s i)).indicator (fun _ ↦ 1) ω
  have hi (i : ι) : Measurable ((toMeasurable P (s i)).indicator (fun _ ↦ (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_toMeasurable P (s i))
  have hf : Measurable f := Finset.measurable_sum _ fun i _ ↦ hi i
  have hfi : ∫⁻ ω, f ω ∂P = ∑ i, P (s i) := by
    rw [lintegral_finsetSum _ fun i _ ↦ hi i]
    apply sum_congr rfl
    intro i _
    rw [lintegral_indicator_const (measurableSet_toMeasurable P (s i)), one_mul,
      measure_toMeasurable]
  have hsub : {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
      ‖∑ i, x i • v ω i‖ < a * ε} ⊆ {ω | (k + 1 : ℝ≥0∞) ≤ f ω} := by
    rintro ω ⟨x, hx, hsmall⟩
    have hcard := hx.lt_card_filter_infDist_span_range_ne hρ ha haρ (v ω) hsmall
    have hcount : ((univ.filter fun i ↦ ω ∈ s i).card : ℝ≥0∞) ≤ f ω := by
      dsimp only [f]
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      rw [sum_filter]
      apply sum_le_sum
      intro i _
      by_cases hi : ω ∈ s i
      · simp [hi, indicator_of_mem (subset_toMeasurable P (s i) hi)]
      · simp [hi]
    have hcard' : (k + 1 : ℝ≥0∞) ≤ (univ.filter fun i ↦ ω ∈ s i).card := by
      exact_mod_cast Nat.succ_le_of_lt hcard
    exact hcard'.trans hcount
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  calc
    _ ≤ (k + 1 : ℝ≥0∞) * P {ω | (k + 1 : ℝ≥0∞) ≤ f ω} := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le
    _ ≤ ∫⁻ ω, f ω ∂P := mul_meas_ge_le_lintegral hf _
    _ = _ := hfi

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
  have h := measure_exists_isIncompressibleVector_norm_sum_lt_le
    (𝕜 := 𝕜) (P := P) (k := k) (ε := ε) hρ ha haρ v
  simpa [ENNReal.toReal_div, ENNReal.toReal_sum, ENNReal.toReal_add, measureReal_def] using
    ENNReal.toReal_mono
      (ENNReal.div_ne_top (ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _)
        (by positivity)) h

/-- The real-valued `ε ρ / √n` bound, valid also for an empty column type. In that case there
are no unit coefficient vectors and both sides vanish. -/
theorem measureReal_exists_isIncompressibleVector_norm_sum_lt_div_sqrt_mul_le
    {k : ℕ} {ρ ε : ℝ} (hρ : 0 ≤ ρ) (v : Ω → ι → E) :
    P.real {ω | ∃ x : EuclideanSpace 𝕜 ι, IsIncompressibleVector k ρ x ∧
        ‖∑ i, x i • v ω i‖ < ρ / Real.sqrt (Fintype.card ι) * ε} ≤
      (∑ i, P.real {ω | infDist (v ω i)
        (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v ω j) : Set E) < ε}) /
        (k + 1 : ℝ) := by
  have h := measure_exists_isIncompressibleVector_norm_sum_lt_div_sqrt_mul_le
    (𝕜 := 𝕜) (P := P) (k := k) (ε := ε) hρ v
  simpa [ENNReal.toReal_div, ENNReal.toReal_sum, ENNReal.toReal_add, measureReal_def] using
    ENNReal.toReal_mono
      (ENNReal.div_ne_top (ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _)
        (by positivity)) h

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
  have h := measure_exists_isIncompressibleVector_norm_toEuclideanLin_lt_le
    (P := P) (k := k) (ε := ε) hρ A
  simpa [ENNReal.toReal_div, ENNReal.toReal_sum, ENNReal.toReal_add, measureReal_def] using
    ENNReal.toReal_mono
      (ENNReal.div_ne_top (ENNReal.sum_ne_top.mpr fun _ _ ↦ measure_ne_top _ _)
        (by positivity)) h

end TauCeti
