/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Basic
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Probability.Moments.Variance

/-!
# Second spectral moment of a Wigner matrix

The second empirical spectral moment is the normalized squared Frobenius norm. Its
upper-triangular expansion counts each off-diagonal coordinate twice. Pairwise independence
and a uniform bound on the variances of the squared coordinate norms give an `O(n⁻²)` tail bound.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology

namespace TauCeti.Probability

variable {Ω : Type*} {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- The second empirical spectral moment is the normalized sum of squared entry norms. -/
theorem integral_sq_spectralMeasure_wignerMatrix (n : ℕ) (ω : Ω) :
    (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      (n + 1 : ℝ)⁻¹ *
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ‖wignerMatrix ξ η (n + 1) ω i j‖ ^ 2 := by
  have h := Matrix.integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
    (wignerMatrix_isHermitian ξ η ω (n + 1)) 2
  simpa only [pow_two, Fintype.card_fin,
    (wignerMatrix_isHermitian ξ η ω (n + 1)).trace_mul_self_eq_sum_norm_sq,
    RCLike.re_to_complex, Complex.ofReal_re, Nat.cast_add, Nat.cast_one] using h

/-- The diagonal squares occur once and the upper-triangular squared norms occur twice. -/
theorem integral_sq_spectralMeasure_wignerMatrix_coordinates (n : ℕ) (ω : Ω) :
    (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      (n + 1 : ℝ)⁻¹ ^ 2 *
        ((∑ i : Fin (n + 1), η i.val ω ^ 2) +
          2 * ∑ p : FinStrictUpper (n + 1), ‖ξ p.toStrictUpper ω‖ ^ 2) := by
  rw [integral_sq_spectralMeasure_wignerMatrix, sum_norm_wignerMatrix_apply_sq]
  push_cast
  ring

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- Finite coordinates embedded in the Wigner array. -/
def wignerCoordinateIndex (n : ℕ) : WignerCoordinateIndex n → StrictUpper ⊕ ℕ :=
  Sum.map FinStrictUpper.toStrictUpper Fin.val

/-- A strict-upper coordinate maps to its upper array index. -/
@[simp] theorem wignerCoordinateIndex_inl (n : ℕ) (p : FinStrictUpper n) :
    wignerCoordinateIndex n (.inl p) = .inl p.toStrictUpper := by rfl

/-- A diagonal coordinate maps to its diagonal array index. -/
@[simp] theorem wignerCoordinateIndex_inr (n : ℕ) (i : Fin n) :
    wignerCoordinateIndex n (.inr i) = .inr i.val := by rfl

/-- Distinct finite coordinates are distinct coordinates of the Wigner array. -/
theorem wignerCoordinateIndex_injective (n : ℕ) :
    Function.Injective (wignerCoordinateIndex n) :=
  FinStrictUpper.toStrictUpper_injective.sumMap Fin.val_injective

/-- Strict-upper coordinates carry weight two and diagonal coordinates weight one. -/
def wignerCoordinateWeight (n : ℕ) : WignerCoordinateIndex n → ℝ
  | .inl _ => 2
  | .inr _ => 1

/-- Strict-upper coordinates have weight two. -/
@[simp] theorem wignerCoordinateWeight_inl (n : ℕ) (p : FinStrictUpper n) :
    wignerCoordinateWeight n (.inl p) = 2 := by rfl

/-- Diagonal coordinates have weight one. -/
@[simp] theorem wignerCoordinateWeight_inr (n : ℕ) (i : Fin n) :
    wignerCoordinateWeight n (.inr i) = 1 := by rfl

/-- Squared absolute value of each Wigner coordinate. -/
noncomputable def wignerCoordinateSquare (ξ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (n : ℕ) : WignerCoordinateIndex n → Ω → ℝ :=
  fun i ω ↦ ‖(Sum.elim ξ (fun j ω ↦ (η j ω : ℂ)) (wignerCoordinateIndex n i)) ω‖ ^ 2

omit [MeasurableSpace Ω] in
/-- The strict-upper statistic is the squared norm of the corresponding entry. -/
@[simp] theorem wignerCoordinateSquare_inl (n : ℕ) (p : FinStrictUpper n) (ω : Ω) :
    wignerCoordinateSquare ξ η n (.inl p) ω =
      ‖ξ p.toStrictUpper ω‖ ^ 2 := by
  simp [wignerCoordinateSquare]

omit [MeasurableSpace Ω] in
/-- The diagonal statistic is the square of the corresponding entry. -/
@[simp] theorem wignerCoordinateSquare_inr (n : ℕ) (i : Fin n) (ω : Ω) :
    wignerCoordinateSquare ξ η n (.inr i) ω = η i.val ω ^ 2 := by
  simp [wignerCoordinateSquare, Complex.norm_real, Real.norm_eq_abs]

/-- The squared coordinate norms of the `n × n` corner are independent when its finite family of
Wigner coordinates is. -/
theorem wignerCoordinateSquare_independent {n : ℕ}
    (h : iIndepFun (fun k ω ↦ wignerCoordinates ξ η n ω k) P) :
    iIndepFun (wignerCoordinateSquare ξ η n) P := by
  convert h.comp (γ := fun _ ↦ ℝ) (fun k ↦ match k with
    | .inl _ => fun z : ℂ ↦ ‖z‖ ^ 2
    | .inr _ => fun x : ℝ ↦ x ^ 2) (by rintro (_ | _) <;> fun_prop) using 1
  funext k ω
  cases k <;> simp only [wignerCoordinateSquare_inl, wignerCoordinateSquare_inr,
    Function.comp_apply, wignerCoordinates_inl, wignerCoordinates_inr]

/-- Joint independence of the finite family of Wigner coordinates of the `n × n` corner implies
pairwise independence of its squared coordinate norms. -/
theorem wignerCoordinateSquare_pairwise_independent {n : ℕ}
    (h : iIndepFun (fun k ω ↦ wignerCoordinates ξ η n ω k) P) :
    Pairwise fun i j ↦ IndepFun (wignerCoordinateSquare ξ η n i)
      (wignerCoordinateSquare ξ η n j) P :=
  fun _ _ hij ↦ (wignerCoordinateSquare_independent h).indepFun hij

omit [MeasurableSpace Ω] in
/-- The second spectral moment is a weighted sum of coordinate statistics. -/
theorem integral_sq_spectralMeasure_wignerMatrix_weighted (n : ℕ) (ω : Ω) :
    (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      ∑ i : WignerCoordinateIndex (n + 1),
        ((n + 1 : ℝ)⁻¹ ^ 2 * wignerCoordinateWeight (n + 1) i) *
          wignerCoordinateSquare ξ η (n + 1) i ω := by
  rw [integral_sq_spectralMeasure_wignerMatrix_coordinates]
  simp only [Fintype.sum_sum_type, wignerCoordinateWeight_inl, wignerCoordinateWeight_inr,
    wignerCoordinateSquare_inl, wignerCoordinateSquare_inr, mul_one]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

private theorem wignerCoordinate_card_le (n : ℕ) :
    Fintype.card (WignerCoordinateIndex n) ≤ n + n ^ 2 := by
  rw [Fintype.card_sum, card_finStrictUpper, Fintype.card_fin, add_comm]
  exact Nat.add_le_add_left (Nat.choose_le_pow n 2) n

private theorem wignerCoordinateWeight_sq_le (n : ℕ) (i : WignerCoordinateIndex n) :
    wignerCoordinateWeight n i ^ 2 ≤ 4 := by
  cases i <;> norm_num only [wignerCoordinateWeight_inl, wignerCoordinateWeight_inr]

private theorem wignerCoordinate_variance_bound (n : ℕ)
    {V : ℝ}
    (hv : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    (∑ i, (((n + 1 : ℝ)⁻¹ ^ 2) * wignerCoordinateWeight (n + 1) i) ^ 2 *
      Var[wignerCoordinateSquare ξ η (n + 1) i; P]) ≤
      8 * V / (n + 1 : ℝ) ^ 2 := by
  have hV : 0 ≤ V :=
    (variance_nonneg (wignerCoordinateSquare ξ η (n + 1) (.inr 0)) P).trans (hv (.inr 0))
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hc : (Fintype.card (WignerCoordinateIndex (n + 1)) : ℝ) ≤
      2 * (n + 1 : ℝ) ^ 2 := by
    have h := wignerCoordinate_card_le (n + 1)
    have hh : (Fintype.card (WignerCoordinateIndex (n + 1)) : ℝ) ≤
        (n + 1 : ℝ) + (n + 1 : ℝ) ^ 2 := by exact_mod_cast h
    nlinarith
  have hp (i : WignerCoordinateIndex (n + 1)) :
      wignerCoordinateWeight (n + 1) i ^ 2 *
        Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ 4 * V := by
    calc
      _ ≤ wignerCoordinateWeight (n + 1) i ^ 2 * V :=
        mul_le_mul_of_nonneg_left (hv i) (sq_nonneg _)
      _ ≤ 4 * V := mul_le_mul_of_nonneg_right (wignerCoordinateWeight_sq_le _ i) hV
  calc
    _ = ((n + 1 : ℝ)⁻¹ ^ 2) ^ 2 *
        ∑ i, wignerCoordinateWeight (n + 1) i ^ 2 *
          Var[wignerCoordinateSquare ξ η (n + 1) i; P] := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ((n + 1 : ℝ)⁻¹ ^ 2) ^ 2 * ((2 * (n + 1 : ℝ) ^ 2) * (4 * V)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      calc
        _ ≤ ∑ _i : WignerCoordinateIndex (n + 1), 4 * V :=
          Finset.sum_le_sum (fun i _ ↦ hp i)
        _ = (Fintype.card (WignerCoordinateIndex (n + 1)) : ℝ) * (4 * V) := by simp
        _ ≤ (2 * (n + 1 : ℝ) ^ 2) * (4 * V) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 8 * V / (n + 1 : ℝ) ^ 2 := by field_simp; ring

/-- The variance of the second spectral moment is `O(n⁻²)` under a uniform bound on
the variances of the squared coordinate norms. -/
theorem variance_second_spectralMoment_le
    (n : ℕ) {V : ℝ}
    (hindep : Pairwise fun i j ↦ IndepFun (wignerCoordinateSquare ξ η (n + 1) i)
      (wignerCoordinateSquare ξ η (n + 1) j) P)
    (hmem : ∀ i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    Var[fun ω ↦ ∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      8 * V / (n + 1 : ℝ) ^ 2 := by
  simp_rw [integral_sq_spectralMeasure_wignerMatrix_weighted]
  rw [variance_weighted_coordinate_sum _ hmem hindep]
  exact wignerCoordinate_variance_bound n hvar

/-- The second spectral moment concentrates if the squared coordinate norms are pairwise
independent and have uniformly bounded variances. -/
theorem measure_second_spectralMoment_sub_mean_ge [IsProbabilityMeasure P]
    (n : ℕ) {V : ℝ}
    (hindep : Pairwise fun i j ↦ IndepFun (wignerCoordinateSquare ξ η (n + 1) i)
      (wignerCoordinateSquare ξ η (n + 1) j) P)
    (hmem : ∀ i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((8 * V / (n + 1 : ℝ) ^ 2) / ε ^ 2) := by
  have h := measure_weighted_coordinate_sum_sub_mean_ge
    (fun i ↦ (n + 1 : ℝ)⁻¹ ^ 2 * wignerCoordinateWeight (n + 1) i)
    hmem hindep hε
  have hbound := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (wignerCoordinate_variance_bound n hvar) (sq_nonneg ε))
  simp_rw [integral_sq_spectralMeasure_wignerMatrix_weighted]
  exact h.trans hbound

/-- Second-moment fluctuations vanish in probability, also for triangular arrays with
varying sample spaces and coordinate laws. -/
theorem tendsto_second_spectralMoment_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ}
    {η : (n : ℕ) → ℕ → Ω n → ℝ} {V : ℝ}
    (hindep : ∀ n, Pairwise fun i j ↦
      IndepFun (wignerCoordinateSquare (ξ n) (η n) (n + 1) i)
        (wignerCoordinateSquare (ξ n) (η n) (n + 1) j) (P n))
    (hmem : ∀ n i, MemLp (wignerCoordinateSquare (ξ n) (η n) (n + 1) i) 2 (P n))
    (hvar : ∀ n i, Var[wignerCoordinateSquare (ξ n) (η n) (n + 1) i; P n] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ 2 ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n|})
      atTop (𝓝 0) := by
  have hmem' (n : ℕ) : MemLp (fun ω ↦ ∫ x, x ^ 2
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) 2 (P n) := by
    simp_rw [integral_sq_spectralMeasure_wignerMatrix_weighted]
    exact memLp_finsetSum Finset.univ fun i _ ↦ (hmem n i).const_mul _
  have hvar' : Tendsto (fun n ↦ Var[fun ω ↦ ∫ x, x ^ 2
      ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ); P n]) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ variance_nonneg _ _)
      (fun n ↦ variance_second_spectralMoment_le n (hindep n) (hmem n) (hvar n))
      (by
        simpa using tendsto_const_nhds.div_atTop
          ((tendsto_pow_atTop two_ne_zero).comp
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)))
  exact tendsto_measure_abs_sub_integral_ge_of_tendsto_variance hmem' hvar' hε

/-- The variance bound applies in particular when the Wigner coordinates of the corner are jointly
independent. -/
theorem variance_second_spectralMoment_le_of_independent_coordinates
    (n : ℕ) {V : ℝ}
    (hindep : iIndepFun (fun k ω ↦ wignerCoordinates ξ η (n + 1) ω k) P)
    (hmem : ∀ i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    Var[fun ω ↦ ∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      8 * V / (n + 1 : ℝ) ^ 2 :=
  variance_second_spectralMoment_le n
    (wignerCoordinateSquare_pairwise_independent hindep) hmem hvar

/-- The second-moment Chebyshev bound when the Wigner coordinates of the corner are jointly
independent. -/
theorem measure_second_spectralMoment_sub_mean_ge_of_independent_coordinates
    [IsProbabilityMeasure P] (n : ℕ) {V : ℝ}
    (hindep : iIndepFun (fun k ω ↦ wignerCoordinates ξ η (n + 1) ω k) P)
    (hmem : ∀ i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((8 * V / (n + 1 : ℝ) ^ 2) / ε ^ 2) :=
  measure_second_spectralMoment_sub_mean_ge n
    (wignerCoordinateSquare_pairwise_independent hindep) hmem hvar hε

/-- Second-moment fluctuations vanish for triangular arrays whose corner Wigner coordinates are
jointly independent at each size. -/
theorem tendsto_second_spectralMoment_sub_mean_probability_of_independent_coordinates
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ}
    {η : (n : ℕ) → ℕ → Ω n → ℝ} {V : ℝ}
    (hindep : ∀ n, iIndepFun (fun k ω ↦ wignerCoordinates (ξ n) (η n) (n + 1) ω k) (P n))
    (hmem : ∀ n i, MemLp (wignerCoordinateSquare (ξ n) (η n) (n + 1) i) 2 (P n))
    (hvar : ∀ n i, Var[wignerCoordinateSquare (ξ n) (η n) (n + 1) i; P n] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω | ε ≤
      |(∫ x, x ^ 2 ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
      ∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) ∂P n|})
      atTop (𝓝 0) :=
  tendsto_second_spectralMoment_sub_mean_probability
    (fun n ↦ wignerCoordinateSquare_pairwise_independent (hindep n))
    hmem hvar hε

end TauCeti.Probability
