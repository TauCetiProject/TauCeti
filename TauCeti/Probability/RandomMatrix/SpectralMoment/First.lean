/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# First spectral moment of a Wigner matrix

The first moment of the normalized empirical spectrum is the normalized sum of diagonal
entries. Its variance is the sum of the diagonal variances, with the appropriate scaling,
when those entries are pairwise independent and square-integrable. Centered entries with
uniformly bounded diagonal variances yield convergence to zero in probability, even for
arrays on varying probability spaces.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology

namespace TauCeti.Probability

variable {Ω : Type*}
variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- The first empirical spectral moment of the Wigner matrix is its diagonal average. -/
theorem integral_spectralMeasure_wignerMatrix (n : ℕ) (ω : Ω) :
    (∫ x, x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      ((n + 1 : ℝ)⁻¹ * (Real.sqrt (n + 1 : ℝ))⁻¹) *
        ∑ i : Fin (n + 1), η i.val ω := by
  have h := Matrix.integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
    (wignerMatrix_isHermitian ξ η ω (n + 1)) 1
  simp only [pow_one, Fintype.card_fin] at h
  rw [h]
  simp only [Matrix.trace, Matrix.diag_apply, wignerMatrix_apply_self, map_sum]
  have hdiag (i : Fin (n + 1)) :
      RCLike.re ((Real.sqrt (n + 1 : ℝ) : ℂ)⁻¹ * (η i.val ω : ℂ)) =
        (Real.sqrt (n + 1 : ℝ))⁻¹ * η i.val ω := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    rfl
  simp only [Nat.cast_add, Nat.cast_one] at hdiag ⊢
  simp_rw [hdiag]
  rw [← Finset.mul_sum]
  ring

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- The first spectral moment has the variance of the normalized diagonal sum. -/
theorem variance_integral_spectralMeasure_wignerMatrix (n : ℕ)
    (hη : ∀ i : Fin (n + 1), MemLp (η i.val) 2 P)
    (hindep : Pairwise fun i j : Fin (n + 1) ↦ IndepFun (η i.val) (η j.val) P) :
    Var[fun ω ↦ ∫ x, x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] =
      (((n + 1 : ℝ)⁻¹ * (Real.sqrt (n + 1 : ℝ))⁻¹) ^ 2) *
        ∑ i : Fin (n + 1), Var[η i.val; P] := by
  have heq : (fun ω ↦ ∫ x, x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      (fun ω ↦ ((n + 1 : ℝ)⁻¹ * (Real.sqrt (n + 1 : ℝ))⁻¹) *
        ∑ i : Fin (n + 1), η i.val ω) :=
    funext (integral_spectralMeasure_wignerMatrix n)
  rw [heq, variance_const_mul]
  simp only [← Finset.sum_apply]
  rw [IndepFun.variance_sum (fun i _ ↦ hη i) (by
    intro i hi j hj hij
    exact hindep hij)]
  simp only [Finset.sum_apply]

/-- Chebyshev's bound for the first spectral moment with centred diagonal entries. -/
theorem measure_integral_spectralMeasure_wignerMatrix_ge [IsProbabilityMeasure P] (n : ℕ)
    (hη : ∀ i : Fin (n + 1), MemLp (η i.val) 2 P)
    (hcenter : ∀ i : Fin (n + 1), ∫ ω, η i.val ω ∂P = 0)
    (hindep : Pairwise fun i j : Fin (n + 1) ↦ IndepFun (η i.val) (η j.val) P)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |∫ x, x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)|} ≤
      ENNReal.ofReal
        (((((n + 1 : ℝ)⁻¹ * (Real.sqrt (n + 1 : ℝ))⁻¹) ^ 2) *
          ∑ i : Fin (n + 1), Var[η i.val; P]) / ε ^ 2) := by
  let X : Ω → ℝ := fun ω ↦
    ∫ x, x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)
  have heq : X = fun ω ↦ ((n + 1 : ℝ)⁻¹ * (Real.sqrt (n + 1 : ℝ))⁻¹) *
      ∑ i : Fin (n + 1), η i.val ω :=
    funext (integral_spectralMeasure_wignerMatrix n)
  have hmem : MemLp X 2 P := by
    rw [heq]
    simpa only [Finset.sum_apply] using
      (memLp_finsetSum' (Finset.univ : Finset (Fin (n + 1)))
        (fun i _ ↦ hη i)).const_mul _
  have hmean : ∫ ω, X ω ∂P = 0 := by
    rw [heq]
    simp only [integral_const_mul]
    rw [integral_finsetSum]
    · simp [hcenter]
    · intro i _
      exact (hη i).integrable (by norm_num)
  have h := meas_ge_le_variance_div_sq hmem hε
  rw [hmean] at h
  simp only [sub_zero] at h
  rw [variance_integral_spectralMeasure_wignerMatrix n hη hindep] at h
  exact h

/-- A uniform diagonal variance bound gives an `O(n⁻²)` first-moment tail bound. -/
theorem measure_integral_spectralMeasure_wignerMatrix_le [IsProbabilityMeasure P] (n : ℕ)
    {V : ℝ}
    (hη : ∀ i : Fin (n + 1), MemLp (η i.val) 2 P)
    (hcenter : ∀ i : Fin (n + 1), ∫ ω, η i.val ω ∂P = 0)
    (hindep : Pairwise fun i j : Fin (n + 1) ↦ IndepFun (η i.val) (η j.val) P)
    (hvar : ∀ i : Fin (n + 1), Var[η i.val; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |∫ x, x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)|} ≤
      ENNReal.ofReal ((V / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt (n + 1 : ℝ) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by positivity)
  have hscale : (((n + 1 : ℝ)⁻¹ * (Real.sqrt (n + 1 : ℝ))⁻¹) ^ 2) *
      ((n + 1 : ℝ) * V) = V / (n + 1 : ℝ) ^ 2 := by
    rw [mul_pow]
    field_simp
    rw [hs]
  refine (measure_integral_spectralMeasure_wignerMatrix_ge n hη hcenter hindep hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
  calc
    _ ≤ (((n + 1 : ℝ)⁻¹ * (Real.sqrt (n + 1 : ℝ))⁻¹) ^ 2) *
        ∑ _i : Fin (n + 1), V :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ ↦ hvar i) (sq_nonneg _)
    _ = V / (n + 1 : ℝ) ^ 2 := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using hscale

/-- The first spectral moment tends to zero for centered, pairwise independent,
square-integrable diagonals with uniformly bounded variances, even on varying spaces. -/
theorem tendsto_integral_spectralMeasure_wignerMatrix_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ}
    {η : (n : ℕ) → ℕ → Ω n → ℝ} {V : ℝ}
    (hη : ∀ n (i : Fin (n + 1)), MemLp (η n i.val) 2 (P n))
    (hcenter : ∀ n (i : Fin (n + 1)), ∫ ω, η n i.val ω ∂P n = 0)
    (hindep : ∀ n, Pairwise fun i j : Fin (n + 1) ↦
      IndepFun (η n i.val) (η n j.val) (P n))
    (hvar : ∀ n (i : Fin (n + 1)), Var[η n i.val; P n] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |∫ x, x ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)|})
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreal : Tendsto (fun n : ℕ ↦ (V / (n + 1 : ℝ) ^ 2) / ε ^ 2)
      atTop (𝓝 0) := by
    convert ((hinv.pow 2).const_mul V).div_const (ε ^ 2) using 1
    · ext n
      simp [div_eq_mul_inv, inv_pow]
    · simp
  have hbound : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      ((V / (n + 1 : ℝ) ^ 2) / ε ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ bot_le) (fun n ↦
      measure_integral_spectralMeasure_wignerMatrix_le n (hη n) (hcenter n)
        (hindep n) (hvar n) hε)

end TauCeti.Probability
