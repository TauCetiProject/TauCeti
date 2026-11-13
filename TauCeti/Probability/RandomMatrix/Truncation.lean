/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner
public import TauCeti.Probability.RandomMatrix.Perturbation
public import TauCeti.Probability.Moments.CenteredTruncation

/-!
# Bounded centered approximation of Wigner off-diagonal entries

Replacing the upper entries by their centered truncations gives bounded centered entries
without changing their independence or identical distribution. The expected normalized squared
Frobenius error is at most the discarded second absolute moment of one entry. Consequently,
the difference of Lipschitz spectral statistics tends to zero in mean square and in probability
as the cutoff grows, uniformly over every positive matrix size.

The diagonal is kept unchanged: it needs no moment assumption and may depend on the upper
entries. Independence is needed only to assert independence of the approximating coordinates,
and is not used in the error estimates. This is the bounded-approximation reduction used when
extending the moment method to finite-second-moment entry laws.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press (2010), §2.1 and Lemma 2.1.19.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped Topology NNReal Matrix.Norms.Frobenius

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {ξ ξ' : StrictUpper → Ω → ℂ} {η : ℕ → Ω → ℝ}

/-- Truncating and centering upper coordinates preserves their joint independence with the
unchanged diagonal coordinates. -/
theorem iIndepFun_wignerMatrix_centeredTruncation
    (h : iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim ξ (fun i ω ↦ (η i ω : ℂ)) k) P) (R : ℝ≥0) :
    iIndepFun (fun k : StrictUpper ⊕ ℕ ↦
      Sum.elim (fun ij ↦ centeredTruncation (ξ ij) P R) (fun i ω ↦ (η i ω : ℂ)) k) P := by
  let g (k : StrictUpper ⊕ ℕ) : ℂ → ℂ := match k with
    | .inl ij => fun z ↦ {z | ‖z‖ ≤ R}.indicator id z -
        ∫ ω, {ω | ‖ξ ij ω‖ ≤ R}.indicator (ξ ij) ω ∂P
    | .inr _ => id
  have hg (k) : Measurable (g k) := by
    cases k
    · exact (measurable_id.indicator
        (measurableSet_le measurable_norm measurable_const)).sub measurable_const
    · exact measurable_id
  convert h.comp g hg using 1
  funext k ω
  cases k <;> simp only [g, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
    centeredTruncation_def, Set.indicator_apply, Set.mem_ofPred_eq, id_eq]

/-- Keeping the same diagonal, a common second absolute moment `s` of the upper-coordinate
differences gives expected squared Frobenius error `n * s` at size `n + 1`. -/
theorem integral_norm_wignerMatrix_sub_sq (hξ : ∀ ij, MemLp (fun ω ↦ ξ ij ω - ξ' ij ω) 2 P)
    {s : ℝ} (hs : ∀ ij, ∫ ω, ‖ξ ij ω - ξ' ij ω‖ ^ 2 ∂P = s) (n : ℕ) :
    ∫ ω, ‖wignerMatrix ξ η (n + 1) ω - wignerMatrix ξ' η (n + 1) ω‖ ^ 2 ∂P = n * s := by
  let d (ij : StrictUpper) (ω : Ω) := ξ ij ω - ξ' ij ω
  have heq (ω : Ω) : wignerMatrix ξ η (n + 1) ω - wignerMatrix ξ' η (n + 1) ω =
      wignerMatrix d (fun _ _ ↦ 0) (n + 1) ω := by
    simp only [wignerMatrix_sub, sub_self, d]
  have hn (ω : Ω) :
      (((n + 1 : ℂ)⁻¹ *
        (wignerMatrix d (fun _ _ ↦ 0) (n + 1) ω *
          wignerMatrix d (fun _ _ ↦ 0) (n + 1) ω).trace).re) =
        (n + 1 : ℝ)⁻¹ * ‖wignerMatrix d (fun _ _ ↦ 0) (n + 1) ω‖ ^ 2 := by
    rw [(wignerMatrix_isHermitian d (fun _ _ ↦ 0) ω _).trace_mul_self_eq_sum_norm_sq,
      Matrix.frobenius_norm_sq_eq_sum_normSq]
    simp only [Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := integral_re_trace_wignerMatrix_mul_self (ξ := d) (η := fun _ _ ↦ 0) (σ2 := 0)
    (fun ij ↦ (memLp_two_iff_integrable_sq_norm (hξ ij).aestronglyMeasurable).mp (hξ ij))
    hs (fun _ ↦ by simp) (fun _ ↦ by simp) (n + 1)
  simp only [Nat.cast_add, Nat.cast_one] at h
  simp only [hn, integral_const_mul] at h
  simp_rw [heq]
  have hN : (n + 1 : ℝ) ≠ 0 := by positivity
  simp only [add_sub_cancel_right, zero_add] at h
  field_simp at h
  exact h

variable [IsProbabilityMeasure P] {X : Ω → ℂ} (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0)
  (hd : ∀ ij, IdentDistrib (ξ ij) X P P)

include hd

omit [IsProbabilityMeasure P] in
private theorem identDistrib_truncation_error (R : ℝ≥0) (ij : StrictUpper) :
    IdentDistrib (fun ω ↦ ξ ij ω - centeredTruncation (ξ ij) P R ω)
      (fun ω ↦ X ω - centeredTruncation X P R ω) P P :=
  ((hd ij).prodMk_centeredTruncation R).comp (measurable_fst.sub measurable_snd)

include hX

/-- The squared Frobenius error of bounded centered off-diagonal approximation is integrable,
regardless of the diagonal law. -/
theorem integrable_norm_wignerMatrix_sub_centeredTruncation_sq (R : ℝ≥0) (n : ℕ) :
    Integrable (fun ω ↦ ‖wignerMatrix ξ η n ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η n ω‖ ^ 2) P := by
  simp_rw [wignerMatrix_sub, sub_self]
  exact integrable_norm_wignerMatrix_sq
    (fun ij ↦ ((hd ij).symm.memLp_snd hX).sub
      (memLp_centeredTruncation ((hd ij).symm.memLp_snd hX).aestronglyMeasurable R))
    (fun _ ↦ memLp_const 0) n

include hmean

/-- Uniform normalized mean-square approximation by bounded centered upper entries.
The bound is the second absolute moment discarded outside the cutoff. -/
theorem inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le
    (R : ℝ≥0) (n : ℕ) :
    (n + 1 : ℝ)⁻¹ * ∫ ω, ‖wignerMatrix ξ η (n + 1) ω -
      wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η (n + 1) ω‖ ^ 2 ∂P ≤
        ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P := by
  have hm (ij : StrictUpper) : MemLp (fun ω ↦ ξ ij ω - centeredTruncation (ξ ij) P R ω) 2 P :=
    ((hd ij).symm.memLp_snd hX).sub
      (memLp_centeredTruncation ((hd ij).symm.memLp_snd hX).aestronglyMeasurable R)
  rw [integral_norm_wignerMatrix_sub_sq hm
    (fun ij ↦ ((identDistrib_truncation_error hd R ij).comp
      (measurable_norm.pow_const 2)).integral_eq)]
  have he : 0 ≤ ∫ ω, ‖X ω - centeredTruncation X P R ω‖ ^ 2 ∂P :=
    integral_nonneg fun _ ↦ sq_nonneg _
  calc
    _ ≤ ∫ ω, ‖X ω - centeredTruncation X P R ω‖ ^ 2 ∂P := by
      have hc : (n : ℝ) / (n + 1) ≤ 1 := by
        exact (div_le_one (by positivity)).mpr (by linarith)
      simpa only [div_eq_inv_mul, mul_assoc, Function.comp_def] using
        mul_le_of_le_one_left he hc
    _ ≤ _ := integral_norm_sub_centeredTruncation_sq_le hX hmean R

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Mean-square control of a Lipschitz spectral statistic, uniformly in positive dimension. -/
theorem integral_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_sq_le
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f)
    (hη : ∀ i, AEMeasurable (η i) P) (R : ℝ≥0) (n : ℕ) :
    ∫ ω, ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
      ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
        (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖ ^ 2 ∂P ≤
      (K : ℝ) ^ 2 * ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P := by
  refine (integral_norm_integral_spectralMeasure_sub_sq_le _ _
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω _)
    (fun ω ↦ wignerMatrix_isHermitian _ η ω _)
    (integrable_norm_wignerMatrix_sub_centeredTruncation_sq hX hd R _) hf
    (aemeasurable_wignerMatrix (fun ij ↦ (hd ij).aemeasurable_fst) hη _)
    (aemeasurable_wignerMatrix (fun ij ↦
      (aestronglyMeasurable_centeredTruncation
        ((hd ij).symm.memLp_snd hX).aestronglyMeasurable R).aemeasurable) hη _)).trans ?_
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc] using
    mul_le_mul_of_nonneg_left
      (inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le hX hmean hd R n)
      (sq_nonneg (K : ℝ))

/-- A spectral-statistic approximation probability bound uniform over all positive dimensions. -/
theorem measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_ge_le
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε)
    (R : ℝ≥0) (n : ℕ) :
    P {ω | ε ≤ ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
      (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
      ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
        (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖} ≤
      ENNReal.ofReal ((K : ℝ) ^ 2 / ε ^ 2 *
        ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P) := by
  refine (measure_norm_integral_spectralMeasure_sub_ge_le _ _
    (fun ω ↦ wignerMatrix_isHermitian ξ η ω _)
    (fun ω ↦ wignerMatrix_isHermitian _ η ω _)
    (integrable_norm_wignerMatrix_sub_centeredTruncation_sq hX hd R _) hf hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, div_eq_mul_inv,
    mul_inv, mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left
      (inv_mul_integral_norm_wignerMatrix_sub_centeredTruncation_sq_le hX hmean hd R n)
      (by positivity : 0 ≤ (K : ℝ) ^ 2 / ε ^ 2)

/-- Bounded centered off-diagonal approximation is valid in probability, uniformly over
all positive matrix sizes, for every Lipschitz spectral statistic. -/
theorem tendsto_iSup_measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation
    {K : ℝ≥0} {f : ℝ → E} (hf : LipschitzWith K f) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ≥0 ↦ ⨆ n : ℕ,
      P {ω | ε ≤ ‖(∫ x, f x ∂((wignerMatrix ξ η (n + 1) ω).spectralMeasure
        (wignerMatrix_isHermitian ξ η ω _) : Measure ℝ)) -
        ∫ x, f x ∂((wignerMatrix (fun ij ↦ centeredTruncation (ξ ij) P R) η
          (n + 1) ω).spectralMeasure (wignerMatrix_isHermitian _ η ω _) : Measure ℝ)‖})
      atTop (𝓝 0) := by
  have ht : Tendsto (fun R : ℝ≥0 ↦ ENNReal.ofReal ((K : ℝ) ^ 2 / ε ^ 2 *
      ∫ ω, {ω | (R : ℝ) < ‖X ω‖}.indicator (fun ω ↦ ‖X ω‖ ^ 2) ω ∂P))
      atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (hX.tendsto_integral_indicator_norm_sq.const_mul ((K : ℝ) ^ 2 / ε ^ 2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ bot_le) (fun R ↦ iSup_le fun n ↦
      measure_norm_spectralMeasure_wignerMatrix_sub_centeredTruncation_ge_le
        hX hmean hd hf hε R n)

end TauCeti.Probability
