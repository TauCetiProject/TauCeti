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
# Second spectral moment of a Wigner matrix

The second empirical spectral moment is the normalized squared Frobenius norm. Its
upper-triangular expansion counts each off-diagonal coordinate twice. Independence and a
uniform bound on the variances of the squared coordinate norms give an `O(n⁻²)` tail bound.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology

namespace TauCeti.Probability

variable {Ω : Type*} {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Strict upper-triangular coordinates in a finite matrix. -/
abbrev FinStrictUpper (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private theorem sum_symmetric {n : ℕ} (g : Fin n → Fin n → ℝ)
    (hs : ∀ i j, g i j = g j i) :
    (∑ i, ∑ j, g i j) =
      (∑ i, g i i) + 2 * ∑ p : FinStrictUpper n, g p.val.1 p.val.2 := by
  classical
  have hlower : (∑ i, ∑ j, if j < i then g i j else 0) =
      ∑ i, ∑ j, if i < j then g i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j i]
  have hdiag : (∑ i, ∑ j, if i = j then g i j else 0) = ∑ i, g i i := by
    simp
  have hu : (∑ p : FinStrictUpper n, g p.val.1 p.val.2) =
      ∑ i, ∑ j, if i < j then g i j else 0 := by
    let s : Finset (Fin n × Fin n) := Finset.univ.filter (fun p ↦ p.1 < p.2)
    have h : (∑ p ∈ s, g p.1 p.2) = ∑ p : FinStrictUpper n, g p.val.1 p.val.2 :=
      Finset.sum_subtype s (by simp [s]) (fun p ↦ g p.1 p.2)
    rw [← h]
    simp only [s, Finset.sum_filter, Fintype.sum_prod_type]
  have hsplit : (∑ i, ∑ j, g i j) =
      (∑ i, ∑ j, if i = j then g i j else 0) +
      (∑ i, ∑ j, if i < j then g i j else 0) +
      (∑ i, ∑ j, if j < i then g i j else 0) := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij, hij.ne, hij.not_gt]
    · subst j
      simp
    · simp [hij, hij.ne', hij.not_gt]
  rw [hdiag, hlower, ← hu] at hsplit
  linarith

/-- The second empirical spectral moment is the normalized sum of squared entry norms. -/
theorem integral_sq_spectralMeasure_wignerMatrix (n : ℕ) (ω : Ω) :
    (∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
      (n + 1 : ℝ)⁻¹ *
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ‖wignerMatrix ξ η (n + 1) ω i j‖ ^ 2 := by
  have htrace : (wignerMatrix ξ η (n + 1) ω * wignerMatrix ξ η (n + 1) ω).trace =
      ((∑ i, ∑ j, ‖wignerMatrix ξ η (n + 1) ω i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [trace, diag_apply, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← (wignerMatrix_isHermitian ξ η ω (n + 1)).apply j i, Complex.star_def,
      Complex.mul_conj']
  have h := Matrix.integral_pow_spectralMeasure (wignerMatrix ξ η (n + 1) ω)
    (wignerMatrix_isHermitian ξ η ω (n + 1)) 2
  simp only [pow_two, Fintype.card_fin, htrace] at h
  change (∫ x, x * x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ)) =
    ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        ‖wignerMatrix ξ η (n + 1) ω i j‖ * ‖wignerMatrix ξ η (n + 1) ω i j‖ at h
  simpa only [pow_two, Nat.cast_add, Nat.cast_one] using h

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
    change star (H j i) = H i j at h
    rw [← h, norm_star]
  have hn : ‖(Real.sqrt (n + 1 : ℝ) : ℂ)⁻¹‖ ^ 2 = (n + 1 : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      inv_pow, Real.sq_sqrt (by positivity)]
  have hn' : ‖(Real.sqrt ((n + 1 : ℕ) : ℝ) : ℂ)⁻¹‖ ^ 2 =
      (n + 1 : ℝ)⁻¹ := by simpa using hn
  have hd (i : Fin (n + 1)) :
      ‖H i i‖ ^ 2 = (n + 1 : ℝ)⁻¹ * η i.val ω ^ 2 := by
    change ‖wignerMatrix ξ η (n + 1) ω i i‖ ^ 2 = _
    rw [wignerMatrix_apply_self, norm_mul, mul_pow, hn', Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hu (p : FinStrictUpper (n + 1)) :
      ‖H p.val.1 p.val.2‖ ^ 2 =
        (n + 1 : ℝ)⁻¹ * ‖ξ ⟨(p.val.1.val, p.val.2.val), p.property⟩ ω‖ ^ 2 := by
    change ‖wignerMatrix ξ η (n + 1) ω p.val.1 p.val.2‖ ^ 2 = _
    rw [wignerMatrix_apply_of_lt _ _ _ p.property, norm_mul, mul_pow, hn']
  rw [integral_sq_spectralMeasure_wignerMatrix]
  change (n + 1 : ℝ)⁻¹ * (∑ i, ∑ j, ‖H i j‖ ^ 2) = _
  rw [sum_symmetric _ hs]
  simp_rw [hd, hu, ← Finset.mul_sum]
  ring

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- The variance of a weighted sum of independent coordinate statistics is the weighted sum
of their variances. It applies in particular to squares or squared complex norms. -/
private theorem variance_weighted_coordinate_sum {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} (a : ι → ℝ) (hX : ∀ i, MemLp (X i) 2 P)
    (hindep : iIndepFun X P) :
    Var[fun ω ↦ ∑ i, a i * X i ω; P] =
      ∑ i, a i ^ 2 * Var[X i; P] := by
  have hi : iIndepFun (fun i ω ↦ a i * X i ω) P :=
    hindep.comp (fun i x ↦ a i * x) (fun _ ↦ by fun_prop)
  have heq : (fun ω ↦ ∑ i, a i * X i ω) =
      ∑ i, (fun ω ↦ a i * X i ω) := by
    ext ω
    simp only [Finset.sum_apply]
  rw [heq, IndepFun.variance_sum
    (fun i _ ↦ (hX i).const_mul _) (by
      intro i _ j _ hij
      exact hi.indepFun hij)]
  simp only [variance_const_mul]

/-- A weighted sum of independent square-integrable coordinate statistics satisfies a
Chebyshev bound in terms of their individual variances. -/
private theorem measure_weighted_coordinate_sum_sub_mean_ge [IsProbabilityMeasure P]
    {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (a : ι → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (hindep : iIndepFun X P)
    {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε ≤ |(∑ i, a i * X i ω) -
        ∫ ω, ∑ i, a i * X i ω ∂P|} ≤
      ENNReal.ofReal ((∑ i, a i ^ 2 * Var[X i; P]) / ε ^ 2) := by
  have hmem : MemLp (fun ω ↦ ∑ i, a i * X i ω) 2 P := by
    have h := memLp_finsetSum' (Finset.univ : Finset ι)
      (fun i _ ↦ (hX i).const_mul (a i))
    convert h using 1
    ext ω
    simp only [Finset.sum_apply]
  have h := meas_ge_le_variance_div_sq hmem hε
  rw [variance_weighted_coordinate_sum a hX hindep] at h
  exact h

/-- Finite coordinates embedded in the Wigner array. -/
def wignerCoordinateIndex (n : ℕ) : Fin n ⊕ FinStrictUpper n → StrictUpper ⊕ ℕ
  | .inl i => .inr i.val
  | .inr p => .inl ⟨(p.val.1.val, p.val.2.val), p.property⟩

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

/-- Squared absolute value of each independent Wigner coordinate. -/
noncomputable def wignerCoordinateSquare (ξ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (n : ℕ) : Fin n ⊕ FinStrictUpper n → Ω → ℝ :=
  fun i ω ↦ ‖(Sum.elim ξ (fun j ω ↦ (η j ω : ℂ)) (wignerCoordinateIndex n i)) ω‖ ^ 2

/-- Squared coordinate norms remain independent. -/
theorem wignerCoordinateSquare_independent
    (h : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P) (n : ℕ) :
    iIndepFun (wignerCoordinateSquare ξ η n) P := by
  exact (h.precomp (wignerCoordinateIndex_injective n)).comp (fun _ (z : ℂ) ↦ ‖z‖ ^ 2)
    (fun _ ↦ by fun_prop)

omit [MeasurableSpace Ω] in
/-- The second spectral moment is a weighted sum of independent coordinate statistics. -/
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
    {V : ℝ} (hV : 0 ≤ V)
    (hv : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    (∑ i, (((n + 1 : ℝ)⁻¹ ^ 2) * wignerCoordinateWeight (n + 1) i) ^ 2 *
      Var[wignerCoordinateSquare ξ η (n + 1) i; P]) ≤
      8 * V / (n + 1 : ℝ) ^ 2 := by
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
    (n : ℕ) {V : ℝ} (hV : 0 ≤ V)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
    (hmem : ∀ i, MemLp (wignerCoordinateSquare ξ η (n + 1) i) 2 P)
    (hvar : ∀ i, Var[wignerCoordinateSquare ξ η (n + 1) i; P] ≤ V) :
    Var[fun ω ↦ ∫ x, x ^ 2 ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ); P] ≤
      8 * V / (n + 1 : ℝ) ^ 2 := by
  simp_rw [integral_sq_spectralMeasure_wignerMatrix_weighted]
  rw [variance_weighted_coordinate_sum _ hmem
    (wignerCoordinateSquare_independent hindep (n + 1))]
  exact wignerCoordinate_variance_bound n hV hvar

/-- The second spectral moment concentrates about its expectation if the original Wigner
coordinates are independent and the variances of their squared norms are uniformly bounded. -/
theorem measure_second_spectralMoment_sub_mean_ge [IsProbabilityMeasure P]
    (n : ℕ) {V : ℝ} (hV : 0 ≤ V)
    (hindep : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P)
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
    hmem (wignerCoordinateSquare_independent hindep (n + 1)) hε
  have hbound := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
    (wignerCoordinate_variance_bound n hV hvar) (sq_nonneg ε))
  simp_rw [integral_sq_spectralMeasure_wignerMatrix_weighted]
  exact h.trans hbound

/-- Second-moment fluctuations vanish in probability, also for triangular arrays with
varying sample spaces and coordinate laws. -/
theorem tendsto_second_spectralMoment_sub_mean_probability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {ξ : (n : ℕ) → StrictUpper → Ω n → ℂ}
    {η : (n : ℕ) → ℕ → Ω n → ℝ} {V : ℝ} (hV : 0 ≤ V)
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
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    convert h.comp (tendsto_add_atTop_nat 1) using 1
    ext n
    simp
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
    (fun _ ↦ bot_le) (fun n ↦ measure_second_spectralMoment_sub_mean_ge n hV
      (hindep n) (hmem n) (hvar n) hε)

end TauCeti.Probability
