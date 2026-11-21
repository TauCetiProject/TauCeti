/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Probability.Distributions.Semicircle.ResolventTransform
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import TauCeti.Probability.Moments.QuadraticForm.SecondMoment
import TauCeti.Probability.RandomMatrix.Diagonal
import TauCeti.Analysis.Matrix.Resolvent.Semicircle
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Measure.ResolventTransform.InProbability

/-!
# The Wigner semicircle law for Lindeberg arrays

For triangular Wigner arrays, the average of the absolute leave-one-out quadratic-form
errors is sufficient to control the resolvent trace. Off-diagonal products are bounded
using only second moments. The truncation of the squared entries controls the diagonal
part of each quadratic form, and its discarded second moments appear in the Lindeberg sum.
A diagonal with vanishing normalized mean-square norm contributes a separate error.

The sample spaces can vary with the size of the matrix.
`MeasureTheory.ProbabilityMeasure.tendsto_measure_integral_iff_resolventTransform`
turns the transform bounds into weak convergence in probability.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), §2.1, Theorem 2.4.
* G. W. Anderson, A. Guionnet, and O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.4.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter Finset
open scoped BigOperators Topology NNReal ENNReal Matrix.Norms.L2Operator BoundedContinuousFunction

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Integrate the squared modulus above the cutoff, sum over ordered off-diagonal pairs and
divide by the dimension `N`. The sum is infinite if any discarded second moment is infinite.
The entries already include the Wigner normalization. The cutoff `r` corresponds to an
unnormalized modulus cutoff `√(r * N)`. -/
def wignerLindebergSum {N : ℕ} (A : Ω → Matrix (Fin N) (Fin N) ℂ) (P : Measure Ω)
    (r : ℝ≥0) : ℝ≥0∞ :=
  (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i},
    ∫⁻ ω, ENNReal.ofReal
      ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω) ∂P

/-- The entrywise formula for the normalized Lindeberg sum. -/
theorem wignerLindebergSum_def {N : ℕ} (A : Ω → Matrix (Fin N) (Fin N) ℂ) (P : Measure Ω)
    (r : ℝ≥0) :
    wignerLindebergSum A P r =
      (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i},
        ∫⁻ ω, ENNReal.ofReal
          ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω) ∂P := by
  rw [wignerLindebergSum]

/-- Almost-everywhere equality of the off-diagonal entries preserves the Lindeberg sum. -/
theorem wignerLindebergSum_congr_ae {N : ℕ}
    {A B : Ω → Matrix (Fin N) (Fin N) ℂ} (r : ℝ≥0)
    (h : ∀ i j, j ≠ i → (fun ω ↦ A ω j i) =ᵐ[P] (fun ω ↦ B ω j i)) :
    wignerLindebergSum A P r = wignerLindebergSum B P r := by
  simp only [wignerLindebergSum_def]
  congr 1
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ lintegral_congr_ae ?_
  filter_upwards [h i j j.property] with ω hω
  simp [Set.indicator_apply, hω]

/-- Raising the squared-modulus cutoff decreases the Lindeberg sum. -/
theorem wignerLindebergSum_antitone {N : ℕ} (A : Ω → Matrix (Fin N) (Fin N) ℂ) :
    Antitone (wignerLindebergSum A P) := by
  intro r s hrs
  simp only [wignerLindebergSum_def]
  refine mul_le_mul_of_nonneg_left
    (sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ lintegral_mono ?_) zero_le
  intro ω
  by_cases h : (s : ℝ) < ‖A ω j i‖ ^ 2
  · have ht : (r : ℝ) < ‖A ω j i‖ ^ 2 := (NNReal.coe_le_coe.mpr hrs).trans_lt h
    simp [h, ht]
  · simp [Set.indicator_apply, h]

@[simp]
theorem wignerLindebergSum_zero {A : Ω → Matrix (Fin 0) (Fin 0) ℂ} (r : ℝ≥0) :
    wignerLindebergSum A P r = 0 := by simp [wignerLindebergSum_def]

@[simp]
theorem wignerLindebergSum_one {A : Ω → Matrix (Fin 1) (Fin 1) ℂ} (r : ℝ≥0) :
    wignerLindebergSum A P r = 0 := by
  have (i : Fin 1) : IsEmpty {j : Fin 1 // j ≠ i} :=
    ⟨fun j ↦ j.property (Subsingleton.elim _ _)⟩
  simp [wignerLindebergSum_def]

/-- If the discarded second moments are integrable, the Lindeberg sum is finite. -/
theorem wignerLindebergSum_ne_top {N : ℕ} (A : Ω → Matrix (Fin N) (Fin N) ℂ) (r : ℝ≥0)
    (hA : ∀ (i : Fin N) (j : {j : Fin N // j ≠ i}),
      Integrable ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2)) P) :
    wignerLindebergSum A P r ≠ ∞ := by
  cases N with
  | zero => simp
  | succ n =>
    rw [wignerLindebergSum_def]
    refine ENNReal.mul_ne_top (by simp) (ENNReal.sum_ne_top.mpr fun i _ ↦
      ENNReal.sum_ne_top.mpr fun j _ ↦ ?_)
    rw [← ofReal_integral_eq_lintegral_ofReal (hA i j)
      (.of_forall fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)]
    exact ENNReal.ofReal_ne_top

/-- For integrable discarded second moments, the real value of the Lindeberg sum uses Bochner
integrals of the squared modulus above the cutoff, summed over ordered off-diagonal pairs and
divided by the matrix dimension. -/
theorem wignerLindebergSum_toReal {N : ℕ} (A : Ω → Matrix (Fin N) (Fin N) ℂ) (r : ℝ≥0)
    (hA : ∀ (i : Fin N) (j : {j : Fin N // j ≠ i}),
      Integrable ({ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2)) P) :
    (wignerLindebergSum A P r).toReal =
      (N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : {j : Fin N // j ≠ i},
        ∫ ω, {ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω ∂P := by
  have hnonneg (i : Fin N) (j : {j : Fin N // j ≠ i}) (ω : Ω) :
      0 ≤ {ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω :=
    Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
  simp_rw [wignerLindebergSum_def, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ← ofReal_integral_eq_lintegral_ofReal (hA _ _) (.of_forall (hnonneg _ _))]
  rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top)]
  simp_rw [ENNReal.toReal_sum (fun _ _ ↦ ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (integral_nonneg (hnonneg _ _))]

variable {ξ : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ} {n : ℕ}

private abbrev zeroDiagonalWigner (ξ : StrictUpper → Ω → ℂ) (N : ℕ) :=
  wignerMatrix ξ (fun _ _ ↦ 0) N

private theorem wigner_minor_secondMoment_terms_le {m N : ℝ} (hN : 0 < N) (hm : m ≤ N)
    (r : ℝ≥0) :
    2 * N⁻¹ * Real.sqrt m + Real.sqrt ((r : ℝ) * m * N⁻¹) ≤
      2 / Real.sqrt N + Real.sqrt r := by
  apply add_le_add
  · calc
      _ ≤ 2 * N⁻¹ * Real.sqrt N := by gcongr
      _ = _ := by field_simp; nlinarith [Real.sq_sqrt hN.le]
  · apply Real.sqrt_le_sqrt
    calc
      _ ≤ (r : ℝ) * N * N⁻¹ := by gcongr
      _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hN.ne', mul_one]

private theorem integral_norm_wigner_minor_quadraticForm_sub_normalized_trace_le
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ ij.val) P)
    (hLp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) 2 P)
    (hc : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (i : Fin (n + 1)) {z : ℂ} (hz : 0 < z.im) (r : ℝ≥0) :
    let a := fun (j : {j // j ≠ i}) ω ↦ zeroDiagonalWigner ξ (n + 1) ω j i
    let Q := fun ω ↦ (zeroDiagonalWigner ξ (n + 1) ω).minorQuadraticError i z 1
    Integrable Q P ∧ (∫ ω, ‖Q ω‖ ∂P) ≤ z.im⁻¹ *
      (2 / Real.sqrt (n + 1) + Real.sqrt r +
        2 * ∑ j : {j // j ≠ i},
          ∫ ω, {ω | (r : ℝ) < ‖a j ω‖ ^ 2}.indicator (fun ω ↦ ‖a j ω‖ ^ 2) ω ∂P) := by
  intro a Q
  let R := fun ω ↦ (zeroDiagonalWigner ξ (n + 1) ω).minorResolvent i z
  have := hind.isProbabilityMeasure
  obtain ⟨_, hi, hia, ha⟩ :=
    aemeasurable_indepFun_wignerMatrix_zero_minor_column hind
      (fun ij hij ↦ (hLp ij hij).aemeasurable) hv i
  have hA : AEMeasurable (zeroDiagonalWigner ξ (n + 1)) P :=
    aemeasurable_wignerMatrix (fun ij hij ↦ (hLp ij hij).aemeasurable)
      (fun _ _ ↦ aemeasurable_const)
  have hR : AEMeasurable R P := (Matrix.measurable_minorResolvent i z).comp_aemeasurable hA
  have hiR : IndepFun R (fun ω j ↦ a j ω) P := by
    simpa only [R, a, zeroDiagonalWigner, Matrix.minorResolvent_def, Function.comp_def,
      id_eq] using hi.comp (φ := fun M : Matrix {j // j ≠ i} {j // j ≠ i} ℂ ↦ (M - z • 1)⁻¹)
        (by fun_prop) measurable_id
  have hRbound : ∀ᵐ ω ∂P, ‖R ω‖ ≤ z.im⁻¹ := .of_forall fun ω ↦ by
    simpa only [R, RCLike.im_eq_complex_im, abs_of_pos hz] using
      (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)).l2_opNorm_minorResolvent_le hz.ne' i
  have hmoment (j : {j // j ≠ i}) : ∫ ω, ‖a j ω‖ ^ 2 ∂P = (n + 1 : ℝ)⁻¹ := by
    simpa only [Nat.cast_succ, one_div] using ha j
  have hRi : Integrable (fun ω ↦ ‖R ω‖) P :=
    Integrable.of_bound hR.norm.aestronglyMeasurable _ (by simpa using hRbound)
  have hRm : (∫ ω, ‖R ω‖ ∂P) ≤ z.im⁻¹ := by
    simpa using integral_mono_ae hRi (integrable_const _) hRbound
  have h := hia.integral_norm_star_dotProduct_mulVec_sub_sum_diag_le_of_indepFun
    (fun j ↦ memLp_wignerMatrix_apply hLp (fun _ _ ↦ memLp_const 0) j i)
    (fun j ↦ integral_wignerMatrix_apply_eq_zero hc (by simp) j i) hR hiR hRi
    (fun j ↦ (hmoment j).le) r
  have hQ : Q = fun ω ↦ star (fun j ↦ a j ω) ⬝ᵥ R ω *ᵥ (fun j ↦ a j ω) -
      ∑ j, R ω j j * ((∫ y, ‖a j y‖ ^ 2 ∂P : ℝ) : ℂ) := by
    funext ω
    simp only [Q, Matrix.minorQuadraticError_def, NNReal.coe_one, Complex.ofReal_one, one_div,
      Fintype.card_fin, hmoment, R, a, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_natCast, Nat.cast_succ, Matrix.trace, Matrix.diag, Finset.mul_sum]
    congr 1
    exact sum_congr rfl fun j _ ↦ mul_comm _ _
  rw [hQ]
  refine ⟨h.1, h.2.trans ?_⟩
  have hcard : (Fintype.card {j // j ≠ i} : ℝ) ≤ n + 1 := by
    exact_mod_cast (Fintype.card_subtype_le (fun j : Fin (n + 1) ↦ j ≠ i)).trans_eq
      (Fintype.card_fin (n + 1))
  have hscale := wigner_minor_secondMoment_terms_le (by positivity) hcard r
  refine mul_le_mul hRm (add_le_add hscale le_rfl) ?_ (inv_nonneg.mpr hz.le)
  refine add_nonneg (by positivity) (mul_nonneg (by norm_num) (sum_nonneg fun _ _ ↦ ?_))
  exact integral_nonneg fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _

private theorem integrable_wignerTransform_error [IsFiniteMeasure P]
    (hξ : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hη : ∀ i < n + 1, AEMeasurable (η i) P) {z : ℂ} (hz : 0 < z.im) :
    Integrable (fun ω ↦
      resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
        resolventTransform (semicircleReal 0 1) z) P :=
  ((aemeasurable_wignerMatrix hξ hη).integrable_resolventTransform_spectralMeasure
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω (n + 1)) hz.ne').sub (integrable_const _)

private theorem integral_norm_resolventTransform_wignerMatrix_zero_sub_semicircleReal_le
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ ij.val) P)
    (hLp : ∀ ij : StrictUpper, ij.val.2 < n + 1 → MemLp (ξ ij) 2 P)
    (hc : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    {z : ℂ} (hz : 0 < z.im) (r : ℝ≥0) :
    (∫ ω, ‖resolventTransform
      ((wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z -
        resolventTransform (semicircleReal 0 1) z‖ ∂P) ≤ z.im⁻¹ ^ 2 *
      (z.im⁻¹ * (2 / Real.sqrt (n + 1) + Real.sqrt r +
        2 * (wignerLindebergSum (wignerMatrix ξ (fun _ _ ↦ 0) (n + 1)) P r).toReal) +
        3 / ((n + 1) * z.im)) := by
  have : IsProbabilityMeasure P := hind.isProbabilityMeasure
  let A := zeroDiagonalWigner ξ (n + 1)
  let Q (i : Fin (n + 1)) (ω : Ω) := (A ω).minorQuadraticError i z 1
  have hq i :=
    integral_norm_wigner_minor_quadraticForm_sub_normalized_trace_le hind hLp hc hv i hz r
  have hi (i : Fin (n + 1)) : Integrable (fun ω ↦ ‖Q i ω‖) P := (hq i).1.norm
  have htest := (integrable_wignerTransform_error (η := fun _ _ ↦ 0)
    (fun ij hij ↦ (hLp ij hij).aemeasurable) (fun _ _ ↦ aemeasurable_const) hz).norm
  let c := 3 / ((n + 1 : ℝ) * z.im)
  have hm : Integrable (fun ω ↦ 𝔼 i, ‖Q i ω‖) P := by
    simp only [Fintype.expect_eq_sum_div_card, div_eq_inv_mul]
    exact (integrable_finsetSum _ fun i _ ↦ hi i).const_mul _
  have hint : (∫ ω, (𝔼 i, ‖Q i ω‖) ∂P) = 𝔼 i, ∫ ω, ‖Q i ω‖ ∂P := by
    simp only [Fintype.expect_eq_sum_div_card, div_eq_inv_mul, integral_const_mul,
      integral_finsetSum _ fun i _ ↦ hi i]
  have hmajor : Integrable (fun ω ↦ z.im⁻¹ ^ 2 * ((𝔼 i, ‖Q i ω‖) + c)) P :=
    (hm.add (integrable_const c)).const_mul _
  have hpoint (ω : Ω) :=
    (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1))
      |>.norm_resolventTransform_spectralMeasure_sub_semicircleReal_le hz 1
  refine (integral_mono htest hmajor (fun ω ↦ by
    simpa only [Q, c, Fintype.card_fin, Nat.cast_succ, NNReal.coe_one, mul_one,
      wignerMatrix_apply_self, Complex.ofReal_zero, mul_zero, norm_zero,
      Finset.expect_const_zero, add_zero] using hpoint ω)).trans ?_
  rw [integral_const_mul, integral_add hm (integrable_const c), hint,
    integral_const, probReal_univ, one_smul]
  let b := 2 / Real.sqrt (n + 1) + Real.sqrt r
  let T (i : Fin (n + 1)) := ∑ j : {j // j ≠ i},
    ∫ ω, {ω | (r : ℝ) < ‖A ω j i‖ ^ 2}.indicator (fun ω ↦ ‖A ω j i‖ ^ 2) ω ∂P
  let U (i : Fin (n + 1)) := z.im⁻¹ * (b + 2 * T i)
  have hU (i : Fin (n + 1)) : (∫ ω, ‖Q i ω‖ ∂P) ≤ U i := by
    simpa only [U, T, b, A] using (hq i).2
  have htail : (wignerLindebergSum A P r).toReal = 𝔼 i, T i := by
    rw [Fintype.expect_eq_sum_div_card, div_eq_inv_mul, Fintype.card_fin]
    exact wignerLindebergSum_toReal A r (fun i j ↦ by
      have hsq := (memLp_wignerMatrix_apply hLp (fun _ _ ↦ memLp_const 0)
        j.val i).integrable_norm_pow (by decide : 2 ≠ 0)
      exact hsq.indicator₀ (nullMeasurableSet_lt aemeasurable_const hsq.aemeasurable))
  have hscaled : (𝔼 i, U i) = z.im⁻¹ * (b + 2 * (wignerLindebergSum A P r).toReal) := by
    dsimp only [U]
    rw [← Finset.mul_expect, Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect,
      ← htail]
  have hmean := Finset.expect_le_expect fun i (_ : i ∈ Finset.univ) ↦ hU i
  refine (mul_le_mul_of_nonneg_left (add_le_add hmean le_rfl) (sq_nonneg _)).trans_eq ?_
  simp only [hscaled, b, c, A, zeroDiagonalWigner]

/-- The upper/lower entry tails are unchanged by replacing the real diagonal. -/
theorem wignerLindebergSum_wignerMatrix_congr_diag {N : ℕ} (ξ : StrictUpper → Ω → ℂ)
    (η η' : ℕ → Ω → ℝ) (r : ℝ≥0) :
    wignerLindebergSum (wignerMatrix ξ η N) P r =
      wignerLindebergSum (wignerMatrix ξ η' N) P r := by
  apply wignerLindebergSum_congr_ae
  intro i j hij
  refine .of_forall fun ω ↦ ?_
  dsimp only
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · rw [wignerMatrix_apply_of_lt _ _ _ h, wignerMatrix_apply_of_lt _ _ _ h]
  · rw [wignerMatrix_apply_of_gt _ _ _ h, wignerMatrix_apply_of_gt _ _ _ h]

private def offDiagEquivStrictUpperFinSum (N : ℕ) :
    (Σ i : Fin N, {j : Fin N // j ≠ i}) ≃ StrictUpperFin N ⊕ StrictUpperFin N where
  toFun p :=
    if h : p.2.val.val < p.1.val then
      .inl ⟨(p.2.val, p.1), h⟩
    else
      .inr ⟨(p.1, p.2.val), lt_of_le_of_ne (le_of_not_gt h) (Fin.val_ne_of_ne p.2.property).symm⟩
  invFun
    | .inl u => ⟨u.val.2, ⟨u.val.1, Fin.ne_of_lt u.property⟩⟩
    | .inr u => ⟨u.val.1, ⟨u.val.2, (Fin.ne_of_lt u.property).symm⟩⟩
  left_inv := by
    rintro ⟨i, j⟩
    by_cases h : j.val.val < i.val <;> simp [h]
  right_inv := by
    rintro (u | u)
    · simp [u.property]
    · simp [u.property.not_gt]

/-- In unnormalized coordinates the Lindeberg sum is twice the sum of the discarded second
moments over the strict upper triangle, divided by the square of the dimension. -/
theorem wignerLindebergSum_wignerMatrix_eq_sum {N : ℕ} (ξ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (r : ℝ≥0) :
    wignerLindebergSum (wignerMatrix ξ η N) P r =
      2 * (N : ℝ≥0∞)⁻¹ ^ 2 * ∑ u : StrictUpperFin N,
        ∫⁻ ω, ENNReal.ofReal ({ω | (r : ℝ) * N < ‖ξ (wignerUpperIndex u) ω‖ ^ 2}.indicator
          (fun ω ↦ ‖ξ (wignerUpperIndex u) ω‖ ^ 2) ω) ∂P := by
  cases N with
  | zero => simp
  | succ n =>
    let edge (p : Σ i : Fin (n + 1), {j : Fin (n + 1) // j ≠ i}) : StrictUpper :=
      ⟨(min p.2.val.val p.1.val, max p.2.val.val p.1.val),
        min_lt_max.mpr (Fin.val_ne_of_ne p.2.property)⟩
    let T (u : StrictUpper) := ∫⁻ ω, ENNReal.ofReal
      ({ω | (r : ℝ) * (n + 1 : ℕ) < ‖ξ u ω‖ ^ 2}.indicator (fun ω ↦ ‖ξ u ω‖ ^ 2) ω) ∂P
    have hN : 0 < (n + 1 : ℝ) := by positivity
    have hscaled (i : Fin (n + 1)) (j : {j : Fin (n + 1) // j ≠ i}) :
        (∫⁻ ω, ENNReal.ofReal ({ω | (r : ℝ) < ‖wignerMatrix ξ η (n + 1) ω j i‖ ^ 2}.indicator
          (fun ω ↦ ‖wignerMatrix ξ η (n + 1) ω j i‖ ^ 2) ω) ∂P) =
        ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * T (edge ⟨i, j⟩) := by
      simp only [T]
      rw [← lintegral_const_mul' _ _ (by simp)]
      apply lintegral_congr
      intro ω
      simp only [norm_wignerMatrix_apply_sq_of_ne _ _ _ j.property, Nat.cast_succ,
        Set.indicator_apply, Set.mem_ofPred_eq]
      have hcut : (r : ℝ) < (n + 1 : ℝ)⁻¹ * ‖ξ (edge ⟨i, j⟩) ω‖ ^ 2 ↔
          (r : ℝ) * (n + 1 : ℝ) < ‖ξ (edge ⟨i, j⟩) ω‖ ^ 2 := by
        rw [← div_eq_inv_mul, lt_div_iff₀ hN]
      dsimp only [edge] at hcut ⊢
      simp only [hcut]
      split_ifs
      · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hN,
          ← Nat.cast_succ, ENNReal.ofReal_natCast, Nat.cast_succ]
      · simp
    have hsum : (∑ p, T (edge p)) = 2 * ∑ u : StrictUpperFin (n + 1), T (wignerUpperIndex u) := by
      rw [← (offDiagEquivStrictUpperFinSum (n + 1)).symm.sum_comp (fun p ↦ T (edge p)),
        Fintype.sum_sum_type, two_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro u _ <;>
        apply congrArg T <;> apply Subtype.ext <;> rw [wignerUpperIndex_val]
      · simp [offDiagEquivStrictUpperFinSum, edge, min_eq_left u.property.le,
          max_eq_right u.property.le]
      · simp [offDiagEquivStrictUpperFinSum, edge, min_eq_right u.property.le,
          max_eq_left u.property.le]
    have hordered : (∑ i : Fin (n + 1), ∑ j : {j // j ≠ i}, T (edge ⟨i, j⟩)) =
        2 * ∑ u : StrictUpperFin (n + 1), T (wignerUpperIndex u) :=
      (Fintype.sum_sigma (fun p ↦ T (edge p))).symm.trans hsum
    simp_rw [wignerLindebergSum_def, hscaled]
    simp only [← mul_sum]
    rw [hordered, pow_two]
    ac_rfl

private theorem memLp_upper_of_integral_norm_sq_eq_one
    (hm : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (ij : StrictUpper) (hij : ij.val.2 < n + 1) : MemLp (ξ ij) 2 P :=
  (memLp_two_iff_integrable_sq_norm (hm ij hij).aestronglyMeasurable).2
    (integrable_of_integral_eq_one (hv ij hij))

/-- At each upper-half-plane parameter, the mean absolute error of a Wigner resolvent
transform is controlled by the matrix size, the off-diagonal Lindeberg sum and the
diagonal second moments. Independence and the moment conditions concern the entries
in the corner of size `n + 1` and ensure that the Lindeberg sum is finite. -/
theorem integral_norm_resolventTransform_wignerMatrix_sub_semicircleReal_le
    (hind : iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ ij.val) P)
    (hm : ∀ ij : StrictUpper, ij.val.2 < n + 1 → AEMeasurable (ξ ij) P)
    (hc : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ξ ij ω ∂P = 0)
    (hv : ∀ ij : StrictUpper, ij.val.2 < n + 1 → ∫ ω, ‖ξ ij ω‖ ^ 2 ∂P = 1)
    (hd : ∀ i < n + 1, MemLp (η i) 2 P) {z : ℂ} (hz : 0 < z.im) (r : ℝ≥0) :
    (∫ ω, ‖resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z -
      resolventTransform (semicircleReal 0 1) z‖ ∂P) ≤ z.im⁻¹ ^ 2 *
      (z.im⁻¹ * (2 / Real.sqrt (n + 1) + Real.sqrt r +
        2 * (wignerLindebergSum (wignerMatrix ξ η (n + 1)) P r).toReal) +
        3 / ((n + 1) * z.im) + Real.sqrt ((n + 1 : ℝ)⁻¹ ^ 2 *
          ∑ i : Fin (n + 1), ∫ ω, η i ω ^ 2 ∂P)) := by
  have := hind.isProbabilityMeasure
  have ha := integrable_wignerTransform_error hm (fun i hi ↦ (hd i hi).aemeasurable) hz
  have hb := integrable_wignerTransform_error hm
    (η := fun _ _ ↦ 0) (fun _ _ ↦ aemeasurable_const) hz
  have h := integral_norm_resolventTransform_wignerMatrix_zero_sub_semicircleReal_le
    hind (memLp_upper_of_integral_norm_sq_eq_one hm hv) hc hv hz r
  rw [wignerLindebergSum_wignerMatrix_congr_diag ξ _ η] at h
  have hab := integral_norm_resolventTransform_wignerMatrix_sub_wignerMatrix_zero_le hm hd hz.ne'
  have hd' := (ha.sub hb).congr (.of_forall fun _ ↦ sub_sub_sub_cancel_right _ _ _)
  let L (ω : Ω) := resolventTransform ((wignerMatrix ξ η (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian ξ η ω (n + 1)) : Measure ℝ) z
  let L₀ (ω : Ω) := resolventTransform ((zeroDiagonalWigner ξ (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian ξ (fun _ _ ↦ 0) ω (n + 1)) : Measure ℝ) z
  let m := resolventTransform (semicircleReal 0 1) z
  have hsplit (ω : Ω) : L ω - m = (L₀ ω - m) + (L ω - L₀ ω) := by abel
  have htriangle := hb.integral_norm_add_le hd'
  calc
    _ = ∫ ω, ‖(L₀ ω - m) + (L ω - L₀ ω)‖ ∂P :=
      integral_congr_ae (.of_forall fun ω ↦ congrArg norm (hsplit ω))
    _ ≤ _ := htriangle.trans ((add_le_add h hab).trans_eq (by ring))


end TauCeti.Probability

namespace TauCeti.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {P : ∀ n, Measure (Ω n)}
  {ξ : ∀ n, StrictUpper → Ω n → ℂ} {η : ∀ n, ℕ → Ω n → ℝ}

/-- For triangular Wigner arrays with centered independent upper entries of unit second
absolute moment, the Lindeberg condition and a vanishing diagonal contribution imply
mean absolute convergence of the transforms at each upper-half-plane parameter. The
sample spaces may vary with the dimension. -/
theorem tendsto_integral_norm_resolventTransform_wignerMatrix_sub_semicircleReal_of_lindeberg
    (hind : ∀ n, iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ n ij.val) (P n))
    (hm : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → AEMeasurable (ξ n ij) (P n))
    (hc : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hv : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hd : ∀ n i, i < n + 1 → MemLp (η n i) 2 (P n))
    (hdiag : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2 *
      ∑ i : Fin (n + 1), ∫ ω, η n i ω ^ 2 ∂P n) atTop (𝓝 0))
    (hL : ∀ r : ℝ≥0, 0 < r → Tendsto (fun n ↦
      wignerLindebergSum (wignerMatrix (ξ n) (η n) (n + 1)) (P n) r) atTop (𝓝 0))
    {z : ℂ} (hz : 0 < z.im) :
    Tendsto (fun n ↦ ∫ ω, ‖resolventTransform
      ((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ) z -
      resolventTransform (semicircleReal 0 1) z‖ ∂P n) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
    simpa only [Nat.cast_succ, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hsize : Tendsto (fun n : ℕ ↦ 2 / Real.sqrt (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hN)
  have hminor : Tendsto (fun n : ℕ ↦ 3 / ((n + 1 : ℝ) * z.im)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hN.atTop_mul_const hz)
  apply tendsto_order.2
  refine ⟨fun ε hε ↦ .of_forall fun n ↦ hε.trans_le
    (integral_nonneg fun _ ↦ norm_nonneg _), ?_⟩
  intro ε hε
  let C := z.im⁻¹ ^ 2 * z.im⁻¹
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hC)
  let r : ℝ≥0 := ⟨δ ^ 2, sq_nonneg _⟩
  have hr : 0 < r := sq_pos_of_pos hδ
  have htail : Tendsto (fun n ↦
      (wignerLindebergSum (wignerMatrix (ξ n) (η n) (n + 1)) (P n) r).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hL r hr)
  have hlim := ((((hsize.add_const (Real.sqrt r)).add (htail.const_mul 2)).const_mul
    z.im⁻¹).add hminor |>.add hdiag.sqrt).const_mul (z.im⁻¹ ^ 2)
  have hlim' : z.im⁻¹ ^ 2 * (z.im⁻¹ * (0 + Real.sqrt (r : ℝ) + 2 * 0) + 0 + Real.sqrt 0)
      = ε / 2 := by
    have hr' : (r : ℝ) = δ ^ 2 := rfl
    simp only [hr', Real.sqrt_sq hδ.le, Real.sqrt_zero, mul_zero, zero_add, add_zero]
    simp only [← mul_assoc, C, δ]
    field_simp [hz.ne']
  rw [hlim'] at hlim
  filter_upwards [hlim.eventually_lt_const (u := ε) (by linarith)] with n hn
  exact (integral_norm_resolventTransform_wignerMatrix_sub_semicircleReal_le
    (hind n) (hm n) (hc n) (hv n) (hd n) hz r).trans_lt hn

/-- **Semicircle law in probability for triangular Wigner arrays.** Centered independent
upper entries have unit second absolute moment before division by the square root of the
dimension. The diagonal is real with negligible normalized mean-square size. Under the
Lindeberg condition, each bounded continuous test integral converges in probability to
its standard semicircle integral, including when the sample spaces vary. -/
theorem wigner_semicircle_in_probability_of_lindeberg
    (hind : ∀ n, iIndepFun (fun ij : {ij : StrictUpper // ij.val.2 < n + 1} ↦ ξ n ij.val) (P n))
    (hm : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → AEMeasurable (ξ n ij) (P n))
    (hc : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ξ n ij ω ∂P n = 0)
    (hv : ∀ n (ij : StrictUpper), ij.val.2 < n + 1 → ∫ ω, ‖ξ n ij ω‖ ^ 2 ∂P n = 1)
    (hd : ∀ n i, i < n + 1 → MemLp (η n i) 2 (P n))
    (hdiag : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)⁻¹ ^ 2 *
      ∑ i : Fin (n + 1), ∫ ω, η n i ω ^ 2 ∂P n) atTop (𝓝 0))
    (hL : ∀ r : ℝ≥0, 0 < r → Tendsto (fun n ↦
      wignerLindebergSum (wignerMatrix (ξ n) (η n) (n + 1)) (P n) r) atTop (𝓝 0))
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ P n {ω |
      ε ≤ |(∫ x, f x ∂((wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1)) : Measure ℝ)) -
        ∫ x, f x ∂semicircleReal 0 1|}) atTop (𝓝 0) := by
  let μ : ProbabilityMeasure ℝ := ⟨semicircleReal 0 1, inferInstance⟩
  let L (n : ℕ) (ω : Ω n) := (wignerMatrix (ξ n) (η n) (n + 1) ω).spectralMeasure
    (wignerMatrix_isHermitian (ξ n) (η n) ω (n + 1))
  refine (ProbabilityMeasure.tendsto_measure_integral_iff_resolventTransform P L atTop μ).2
    (fun z hz t ht ↦ ?_) f ε hε
  let E (n : ℕ) (ω : Ω n) :=
    resolventTransform (L n ω : Measure ℝ) z - resolventTransform (semicircleReal 0 1) z
  have hlim : Tendsto (fun n ↦ ∫ ω, ‖E n ω‖ ∂P n) atTop (𝓝 0) :=
    tendsto_integral_norm_resolventTransform_wignerMatrix_sub_semicircleReal_of_lindeberg
      hind hm hc hv hd hdiag hL hz
  have hupper := ENNReal.tendsto_ofReal (hlim.div_const t)
  simp only [zero_div, ENNReal.ofReal_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ ↦ bot_le) (fun n ↦ ?_)
  have := (hind n).isProbabilityMeasure
  have hi : Integrable (E n) (P n) := integrable_wignerTransform_error
    (hm n) (fun i hi ↦ (hd n i hi).aemeasurable) hz
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (.of_forall fun ω ↦ norm_nonneg (E n ω)) hi.norm t
  have hb := (le_div_iff₀ ht).2 (by simpa only [mul_comm] using hMarkov)
  exact (ofReal_measureReal (measure_ne_top _ _)).symm.le.trans (ENNReal.ofReal_le_ofReal hb)

end TauCeti.Probability
