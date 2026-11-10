/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Algebra.BigOperators.Finset.Pairs
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
          2 * ∑ p : FinStrictUpper (n + 1),
            ‖ξ ⟨(p.val.1.val, p.val.2.val), p.property⟩ ω‖ ^ 2) := by
  let H := wignerMatrix ξ η (n + 1) ω
  have hs : ∀ i j, ‖H i j‖ ^ 2 = ‖H j i‖ ^ 2 := by
    intro i j
    have h := (wignerMatrix_isHermitian ξ η ω (n + 1)).apply i j
    dsimp only [H] at h ⊢
    rw [← h, norm_star]
  have hn : ‖(Real.sqrt (n + 1 : ℝ) : ℂ)⁻¹‖ ^ 2 = (n + 1 : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (by positivity)]
  have hn' : ‖(Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)⁻¹‖ ^ 2 =
      (n + 1 : ℝ)⁻¹ := by simpa using hn
  have hd (i : Fin (n + 1)) :
      ‖H i i‖ ^ 2 = (n + 1 : ℝ)⁻¹ * η i.val ω ^ 2 := by
    dsimp only [H]
    rw [wignerMatrix_apply_self, norm_mul, mul_pow, hn', Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hu (p : FinStrictUpper (n + 1)) :
      ‖H p.val.1 p.val.2‖ ^ 2 =
        (n + 1 : ℝ)⁻¹ * ‖ξ ⟨(p.val.1.val, p.val.2.val), p.property⟩ ω‖ ^ 2 := by
    dsimp only [H]
    rw [wignerMatrix_apply_of_lt _ _ _ p.property, norm_mul, mul_pow, hn']
  rw [integral_sq_spectralMeasure_wignerMatrix]
  -- Name the Wigner matrix so the diagonal and upper-coordinate identities apply.
  change (n + 1 : ℝ)⁻¹ * (∑ i, ∑ j, ‖H i j‖ ^ 2) = _
  rw [sum_symmetric_pairs _ hs]
  simp only [nsmul_eq_mul]
  simp_rw [hd, hu, ← Finset.mul_sum]
  ring

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- Finite coordinates embedded in the Wigner array. -/
def wignerCoordinateIndex (n : ℕ) : Fin n ⊕ FinStrictUpper n → StrictUpper ⊕ ℕ
  | .inl i => .inr i.val
  | .inr p => .inl ⟨(p.val.1.val, p.val.2.val), p.property⟩

/-- A diagonal coordinate maps to its diagonal array index. -/
@[simp] theorem wignerCoordinateIndex_inl (n : ℕ) (i : Fin n) :
    wignerCoordinateIndex n (.inl i) = .inr i.val := by rfl

/-- A strict-upper coordinate maps to its upper array index. -/
@[simp] theorem wignerCoordinateIndex_inr (n : ℕ) (p : FinStrictUpper n) :
    wignerCoordinateIndex n (.inr p) = .inl ⟨(p.val.1.val, p.val.2.val), p.property⟩ := by rfl

theorem wignerCoordinateIndex_injective (n : ℕ) :
    Function.Injective (wignerCoordinateIndex n) := by
  intro a b h
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      simp only [wignerCoordinateIndex, Sum.inr.injEq] at h
      exact congrArg Sum.inl (Fin.ext h)
    | inr j => simp [wignerCoordinateIndex] at h
  | inr i =>
    cases b with
    | inl j => simp [wignerCoordinateIndex] at h
    | inr j =>
      simp only [wignerCoordinateIndex, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq] at h
      apply congrArg Sum.inr
      apply Subtype.ext
      exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- Diagonal coordinates carry weight one and strict-upper coordinates weight two. -/
def wignerCoordinateWeight (n : ℕ) : Fin n ⊕ FinStrictUpper n → ℝ
  | .inl _ => 1
  | .inr _ => 2

/-- Diagonal coordinates have weight one. -/
@[simp] theorem wignerCoordinateWeight_inl (n : ℕ) (i : Fin n) :
    wignerCoordinateWeight n (.inl i) = 1 := by rfl

/-- Strict-upper coordinates have weight two. -/
@[simp] theorem wignerCoordinateWeight_inr (n : ℕ) (p : FinStrictUpper n) :
    wignerCoordinateWeight n (.inr p) = 2 := by rfl

/-- Squared absolute value of each Wigner coordinate. -/
noncomputable def wignerCoordinateSquare (ξ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (n : ℕ) : Fin n ⊕ FinStrictUpper n → Ω → ℝ :=
  fun i ω ↦ ‖(Sum.elim ξ (fun j ω ↦ (η j ω : ℂ)) (wignerCoordinateIndex n i)) ω‖ ^ 2

omit [MeasurableSpace Ω] in
/-- The diagonal statistic is the square of the corresponding entry. -/
@[simp] theorem wignerCoordinateSquare_inl (n : ℕ) (i : Fin n) (ω : Ω) :
    wignerCoordinateSquare ξ η n (.inl i) ω = η i.val ω ^ 2 := by
  simp [wignerCoordinateSquare, wignerCoordinateIndex, Complex.norm_real, Real.norm_eq_abs]

omit [MeasurableSpace Ω] in
/-- The strict-upper statistic is the squared norm of the corresponding entry. -/
@[simp] theorem wignerCoordinateSquare_inr (n : ℕ) (p : FinStrictUpper n) (ω : Ω) :
    wignerCoordinateSquare ξ η n (.inr p) ω =
      ‖ξ ⟨(p.val.1.val, p.val.2.val), p.property⟩ ω‖ ^ 2 := by
  simp [wignerCoordinateSquare, wignerCoordinateIndex]

/-- Squared coordinate norms remain independent. -/
theorem wignerCoordinateSquare_independent
    (h : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P) (n : ℕ) :
    iIndepFun (wignerCoordinateSquare ξ η n) P := by
  exact (h.precomp (wignerCoordinateIndex_injective n)).comp (fun _ (z : ℂ) ↦ ‖z‖ ^ 2)
    (fun _ ↦ by fun_prop)

/-- Joint independence of the original Wigner coordinates implies pairwise independence
of the finite squared-coordinate family. -/
theorem wignerCoordinateSquare_pairwise_independent
    (h : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P) (n : ℕ) :
    Pairwise fun i j ↦ IndepFun (wignerCoordinateSquare ξ η n i)
      (wignerCoordinateSquare ξ η n j) P :=
  fun _ _ hij ↦ (wignerCoordinateSquare_independent h n).indepFun hij

omit [MeasurableSpace Ω] in
/-- The second spectral moment is a weighted sum of coordinate statistics. -/
theorem integral_sq_spectralMeasure_wignerMatrix_weighted (n : ℕ) (ω : Ω) :
    (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      ∑ i : Fin (n + 1) ⊕ FinStrictUpper (n + 1),
        ((n + 1 : ℝ)⁻¹ ^ 2 * wignerCoordinateWeight (n + 1) i) *
          wignerCoordinateSquare ξ η (n + 1) i ω := by
  rw [integral_sq_spectralMeasure_wignerMatrix_coordinates]
  simp only [Fintype.sum_sum_type, wignerCoordinateWeight, wignerCoordinateSquare,
    wignerCoordinateIndex, Sum.elim_inl, Sum.elim_inr, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, mul_one]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

private theorem wignerCoordinate_card_le (n : ℕ) :
    Fintype.card (Fin n ⊕ FinStrictUpper n) ≤ n + n ^ 2 := by
  have h : Fintype.card (FinStrictUpper n) ≤ Fintype.card (Fin n × Fin n) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simpa [Fintype.card_sum, Fintype.card_prod, pow_two] using Nat.add_le_add_left h n

private theorem wignerCoordinateWeight_sq_le (n : ℕ) (i : Fin n ⊕ FinStrictUpper n) :
    wignerCoordinateWeight n i ^ 2 ≤ 4 := by
  cases i <;> norm_num [wignerCoordinateWeight]

private theorem wignerCoordinate_variance_bound (n : ℕ)
    {V : ℝ}
    (hv : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    (∑ i, (((n + 1 : ℝ)⁻¹ ^ 2) * wignerCoordinateWeight (n + 1) i) ^ 2 *
      Var[wignerCoordinateSquare ξ η (n + 1) i; P]) ≤
      8 * V / (n + 1 : ℝ) ^ 2 := by
  have hV : 0 ≤ V :=
    (variance_nonneg (wignerCoordinateSquare ξ η (n + 1) (.inl 0)) P).trans (hv (.inl 0))
  have hN : 1 ≤ (n + 1 : ℝ) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hc : (Fintype.card (Fin (n + 1) ⊕ FinStrictUpper (n + 1)) : ℝ) ≤
      2 * (n + 1 : ℝ) ^ 2 := by
    have h := wignerCoordinate_card_le (n + 1)
    have hh : (Fintype.card (Fin (n + 1) ⊕ FinStrictUpper (n + 1)) : ℝ) ≤
        (n + 1 : ℝ) + (n + 1 : ℝ) ^ 2 := by exact_mod_cast h
    nlinarith
  have hp (i : Fin (n + 1) ⊕ FinStrictUpper (n + 1)) :
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
        _ ≤ ∑ _i : Fin (n + 1) ⊕ FinStrictUpper (n + 1), 4 * V :=
          Finset.sum_le_sum (fun i _ ↦ hp i)
        _ = (Fintype.card (Fin (n + 1) ⊕ FinStrictUpper (n + 1)) : ℝ) * (4 * V) := by simp
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
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreal : Tendsto (fun n : ℕ ↦ (8 * V / (n + 1 : ℝ) ^ 2) / ε ^ 2)
      atTop (𝓝 0) := by
    convert ((hinv.pow 2).const_mul (8 * V)).div_const (ε ^ 2) using 1
    · ext n
      simp [div_eq_mul_inv, inv_pow]
    · simp
  have hbound : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      ((8 * V / (n + 1 : ℝ) ^ 2) / ε ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ bot_le) (fun n ↦ measure_second_spectralMoment_sub_mean_ge n
      (hindep n) (hmem n) (hvar n) hε)

/-- The variance bound applies in particular when the original Wigner coordinates are jointly
independent. -/
theorem variance_second_spectralMoment_le_of_independent_coordinates
    (n : ℕ) {V : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hmem : ∀ i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    Var[fun ω ↦ ∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      8 * V / (n + 1 : ℝ) ^ 2 :=
  variance_second_spectralMoment_le n
    (wignerCoordinateSquare_pairwise_independent hindep (n + 1)) hmem hvar

/-- The second-moment Chebyshev bound for jointly independent Wigner coordinates. -/
theorem measure_second_spectralMoment_sub_mean_ge_of_independent_coordinates
    [IsProbabilityMeasure P] (n : ℕ) {V : ℝ}
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hmem : ∀ i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) -
      ∫ ω, (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) ∂P|} ≤
      ENNReal.ofReal ((8 * V / (n + 1 : ℝ) ^ 2) / ε ^ 2) :=
  measure_second_spectralMoment_sub_mean_ge n
    (wignerCoordinateSquare_pairwise_independent hindep (n + 1)) hmem hvar hε

/-- Second-moment fluctuations vanish for triangular arrays whose original coordinates
are jointly independent at each size. -/
theorem tendsto_second_spectralMoment_sub_mean_probability_of_independent_coordinates
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ}
    {η : (n : ℕ) → ℕ → Ω n → ℝ} {V : ℝ}
    (hindep : ∀ n, iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim (ξ n) (fun i ω ↦ (η n i ω : ℂ)) k) (P n))
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
    (fun n ↦ wignerCoordinateSquare_pairwise_independent (hindep n) (n + 1))
    hmem hvar hε

end TauCeti.Probability
