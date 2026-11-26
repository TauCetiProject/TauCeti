/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.LogarithmicPotential
public import TauCeti.Analysis.Matrix.SpectralMeasure.SingularValues

import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.LogIntegral

/-!
# Girko's hermitization

For a complex square matrix `A` of size `n` and a point `z` that is not an eigenvalue of `A`,
the logarithmic potential of the eigenvalue measure of `A` is
`U(z) = n⁻¹ log |det (A - z)| = ∫ log s dν(s)`, where `ν` is the singular-value measure of
`A - z`. By `Matrix.integral_log_spectralMeasure_conjTranspose_mul_self`, this also equals
`½ ∫ log x dL(x)` for the spectral measure `L` of the Hermitian matrix `(A - z)ᴴ (A - z)`. The
spectrum is finite, so the potential identity holds for Lebesgue-almost every `z`; for random
matrices it holds, for almost every `z`, almost surely and simultaneously for a whole sequence of
matrices.

This is how the eigenvalues of a non-Hermitian matrix are controlled through the singular values
of its shifts. Weak limits of eigenvalue measures follow from limits of `∫ log s dν(s)` for
almost every shift `z`. The normalized squared Frobenius norm bounds the logarithmic tail at
infinity, leaving the tail at zero to be estimated from the small singular values.

## Main results

* `Matrix.logarithmicPotential_eigenvalueMeasure_eq_log_norm_det`: off the spectrum,
  `U(z) = n⁻¹ log ‖det (A - z • 1)‖`.
* `Matrix.logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure`: Girko's
  hermitization identity off the spectrum, with its almost-everywhere and random-matrix forms
  `Matrix.ae_logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure` and
  `Matrix.ae_ae_logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure`.
* `Matrix.ae_tendsto_eigenvalueMeasure_of_ae_tendsto_singularValueMeasure`: transfer of almost-sure
  eigenvalue convergence from a reference sequence via common limiting singular-value laws and
  logarithmic tail bounds.

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS (2012),
  §2.8.3, identity (2.179).
* V. L. Girko, *The circular law*, Teor. Veroyatnost. i Primenen. 29 (1984), 669–679.
-/

public section

namespace Matrix

open MeasureTheory Polynomial

section Eigenvalues

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Off the spectrum, the logarithmic potential of the eigenvalue measure of a complex matrix is
the normalized logarithm of `‖det (A - z • 1)‖`. -/
theorem logarithmicPotential_eigenvalueMeasure_eq_log_norm_det (A : Matrix n n ℂ) {z : ℂ}
    (hz : z ∉ spectrum ℂ A) :
    (A.eigenvalueMeasure : Measure ℂ).logarithmicPotential z =
      (Fintype.card n : ℝ)⁻¹ * Real.log ‖(A - z • 1).det‖ := by
  have hroot : ∀ w ∈ A.charpoly.roots, w ≠ z := by
    rintro w hw rfl
    exact hz (mem_spectrum_iff_isRoot_charpoly.mpr (isRoot_of_mem_roots hw))
  -- `det (A - z • 1)` is the product of `λ - z` over the characteristic roots `λ`.
  have hdet := det_aeval_eq_prod_roots_charpoly A (X - C z)
  simp only [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, eval_sub, eval_X,
    eval_C] at hdet
  rw [Measure.logarithmicPotential_def, integral_eigenvalueMeasure, smul_eq_mul, hdet,
    Multiset.norm_prod, Multiset.map_map, Real.log_multiset_prod, Multiset.map_map]
  · congr 2
    refine Multiset.map_congr rfl fun w _ ↦ ?_
    simp [norm_sub_rev]
  · simp only [Multiset.mem_map, Function.comp_apply]
    rintro _ ⟨w, hw, rfl⟩
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hroot w hw))

/-- **Girko's hermitization.** If `z` is not an eigenvalue of `A`, the logarithmic potential of
the eigenvalue measure of `A` at `z` is the mean logarithm of the singular values of `A - z • 1`.
-/
theorem logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure
    (A : Matrix n n ℂ) {z : ℂ} (hz : z ∉ spectrum ℂ A) :
    (A.eigenvalueMeasure : Measure ℂ).logarithmicPotential z =
      ∫ s, Real.log s ∂((A - z • 1).singularValueMeasure : Measure ℝ) := by
  have hdet : (A - z • 1).det ≠ 0 := by
    simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using
      ((isUnit_iff_isUnit_det _).mp (spectrum.notMem_iff.mp hz).neg).ne_zero
  rw [logarithmicPotential_eigenvalueMeasure_eq_log_norm_det A hz,
    integral_log_singularValueMeasure_eq_log_norm_det hdet]

/-- **Girko's hermitization**, for Lebesgue-almost every `z`: the logarithmic potential of the
eigenvalue measure of `A` at `z` is the mean logarithm of the singular values of `A - z • 1`. -/
theorem ae_logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure
    (A : Matrix n n ℂ) :
    ∀ᵐ z ∂volume, (A.eigenvalueMeasure : Measure ℂ).logarithmicPotential z =
      ∫ s, Real.log s ∂((A - z • 1).singularValueMeasure : Measure ℝ) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (A.finite_spectrum.measure_zero volume)]
    with z hz
  exact logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure A hz

end Eigenvalues

/-- For Lebesgue-almost every complex number, almost surely that number is outside the
spectra of a sequence of random complex matrices. -/
theorem ae_ae_forall_notMem_spectrum
    {ιs : ℕ → Type*} [∀ k, Fintype (ιs k)] [∀ k, DecidableEq (ιs k)]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {A : ∀ k, Ω → Matrix (ιs k) (ιs k) ℂ} (hA : ∀ k, AEMeasurable (A k) P) :
    ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, ∀ k, z ∉ spectrum ℂ (A k ω) := by
  -- Work with measurable modifications `B k`; they agree with `A k` for all `k` almost surely.
  set B := fun k ↦ (hA k).mk _
  -- Being an eigenvalue of `B k ω` is a jointly measurable condition on `(z, ω)`, since it is
  -- the vanishing of `det (z • 1 - B k ω)`.
  have hmeas : MeasurableSet {p : ℂ × Ω | ∀ k, p.1 ∉ spectrum ℂ (B k p.2)} := by
    simp_rw [mem_spectrum_iff_isRoot_charpoly, IsRoot.def, eval_charpoly, Set.ofPred_forall]
    refine MeasurableSet.iInter fun k ↦ ?_
    have hc : Continuous fun q : ℂ × Matrix (ιs k) (ιs k) ℂ ↦ (scalar (ιs k) q.1 - q.2).det := by
      simp_rw [scalar_apply]
      fun_prop
    have hm := (hA k).measurable_mk
    exact (hc.measurable.comp (measurable_fst.prodMk (hm.comp measurable_snd)))
      (measurableSet_singleton 0).compl
  -- For each sample the exceptional points form a countable union of finite sets.
  have hspec : ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, ∀ k, z ∉ spectrum ℂ (B k ω) :=
    (Measure.ae_ae_comm hmeas).mpr (ae_of_all _ fun ω ↦ ae_all_iff.mpr fun k ↦
      measure_eq_zero_iff_ae_notMem.mp ((B k ω).finite_spectrum.measure_zero volume))
  filter_upwards [hspec] with z hz
  filter_upwards [hz, ae_all_iff.mpr fun k ↦ (hA k).ae_eq_mk] with ω hω hmk k
  rw [hmk k]
  exact hω k

/-- **Girko's hermitization for random matrices.** For a sequence of almost-everywhere measurable
random complex square matrices, for Lebesgue-almost every `z` it holds almost surely, for every
index `k`, that the logarithmic potential of the eigenvalue measure of `A k` at `z` is the mean
logarithm of the singular values of `A k - z • 1`. This is the form consumed by
`Matrix.ae_tendsto_eigenvalueMeasure_of_ae_ae_tendsto_logarithmicPotential`. -/
theorem ae_ae_logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure
    {ιs : ℕ → Type*} [∀ k, Fintype (ιs k)] [∀ k, DecidableEq (ιs k)] [∀ k, Nonempty (ιs k)]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {A : ∀ k, Ω → Matrix (ιs k) (ιs k) ℂ} (hA : ∀ k, AEMeasurable (A k) P) :
    ∀ᵐ z ∂volume, ∀ᵐ ω ∂P, ∀ k,
      ((A k ω).eigenvalueMeasure : Measure ℂ).logarithmicPotential z =
        ∫ s, Real.log s ∂((A k ω - z • 1).singularValueMeasure : Measure ℝ) := by
  filter_upwards [ae_ae_forall_notMem_spectrum hA] with z hz
  exact hz.mono fun ω hω k ↦
    logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure _ (hω k)

section Convergence

open Filter Set Topology
open scoped ENNReal Matrix.Norms.Frobenius NNReal

private theorem lintegral_sq_singularValueMeasure_sub_smul_one_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] (A : Matrix n n ℂ) (z : ℂ) :
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂((A - z • 1).singularValueMeasure : Measure ℝ) ≤
      ENNReal.ofReal (2 * (‖A‖ ^ 2 / Fintype.card n + ‖z‖ ^ 2)) := by
  have hone : ‖(1 : Matrix n n ℂ)‖ = Real.sqrt (Fintype.card n) := by
    simpa using congrArg (fun t : ℝ≥0 ↦ (t : ℝ)) (frobenius_nnNorm_one (n := n) (α := ℂ))
  have hz : ‖z • (1 : Matrix n n ℂ)‖ ^ 2 = ‖z‖ ^ 2 * Fintype.card n := by
    rw [norm_smul, hone, mul_pow, Real.sq_sqrt (by positivity)]
  have hcard : (0 : ℝ) < Fintype.card n := by positivity
  rw [lintegral_sq_singularValueMeasure]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (‖A‖ + ‖z • (1 : Matrix n n ℂ)‖) ^ 2 / Fintype.card n :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2) hcard.le
    _ ≤ (2 * (‖A‖ ^ 2 + ‖z • (1 : Matrix n n ℂ)‖ ^ 2)) / Fintype.card n := by
      apply div_le_div_of_nonneg_right _ hcard.le
      nlinarith [sq_nonneg (‖A‖ - ‖z • (1 : Matrix n n ℂ)‖)]
    _ = _ := by rw [hz, mul_div_assoc, add_div, mul_div_cancel_right₀ _ hcard.ne']

/-- At a fixed shift, weak convergence of the singular-value measures gives convergence of
the logarithmic integrals if the normalized squared Frobenius norms are bounded, the shifts
are eventually invertible, and the logarithmic tails at zero vanish uniformly in the limit.
The limiting singular-value law is carried by the positive axis and has an integrable logarithm. -/
theorem tendsto_integral_log_singularValueMeasure_sub_smul_one {ι : Type*}
    {l : Filter ι} [l.NeBot] {ιs : ι → Type*} [∀ i, Fintype (ιs i)] [∀ i, DecidableEq (ιs i)]
    [∀ i, Nonempty (ιs i)] {A : ∀ i, Matrix (ιs i) (ιs i) ℂ}
    {z : ℂ} {ν : ProbabilityMeasure ℝ}
    (hweak : Tendsto (fun n ↦ (A n - z • 1).singularValueMeasure) l (𝓝 ν))
    (hspec : ∀ᶠ n in l, z ∉ spectrum ℂ (A n))
    (hbound : ∃ C : ℝ≥0, ∀ᶠ n in l, ‖A n‖ ^ 2 / Fintype.card (ιs n) ≤ (C : ℝ))
    (hzero : ∀ ε : ℝ, 0 < ε → ∃ a > (0 : ℝ), ∀ᶠ n in l,
      ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x)
        ∂((A n - z • 1).singularValueMeasure : Measure ℝ) ≤ ENNReal.ofReal ε) :
    (∀ᵐ x ∂(ν : Measure ℝ), 0 < x) ∧ Integrable Real.log (ν : Measure ℝ) ∧
      Tendsto (fun n ↦ ∫ x, Real.log x ∂((A n - z • 1).singularValueMeasure : Measure ℝ)) l
        (𝓝 (∫ x, Real.log x ∂(ν : Measure ℝ))) := by
  obtain ⟨C, hC⟩ := hbound
  let D : ℝ≥0 := ⟨2 * ((C : ℝ) + ‖z‖ ^ 2), by positivity⟩
  have hsq : ∀ᶠ n in l,
      ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂((A n - z • 1).singularValueMeasure : Measure ℝ) ≤
        (D : ℝ≥0∞) := by
    filter_upwards [hC] with n hn
    refine (lintegral_sq_singularValueMeasure_sub_smul_one_le (A n) z).trans ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    -- Unfolding `D` reduces its real coercion to the value in the subtype constructor.
    simp only [D]
    exact mul_le_mul_of_nonneg_left (add_le_add_left hn _) (by norm_num)
  refine ProbabilityMeasure.tendsto_integral_log_of_log_tail_zero hweak ?_ hsq hzero
  filter_upwards [hspec] with k hk
  apply ae_pos_singularValueMeasure_of_det_ne_zero
  simpa only [Algebra.algebraMap_eq_smul_one, neg_sub] using
    ((isUnit_iff_isUnit_det _).mp (spectrum.notMem_iff.mp hk).neg).ne_zero

variable {ιs κs : ℕ → Type*} [∀ n, Fintype (ιs n)] [∀ n, DecidableEq (ιs n)]
  [∀ n, Nonempty (ιs n)] [∀ n, Fintype (κs n)] [∀ n, DecidableEq (κs n)] [∀ n, Nonempty (κs n)]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
  {X : ∀ n, Ω → Matrix (ιs n) (ιs n) ℂ} {Y : ∀ n, Ω → Matrix (κs n) (κs n) ℂ}
  {μ : ProbabilityMeasure ℂ}

/-- Transfer almost-sure weak eigenvalue convergence from a reference sequence with the same
weak limiting singular-value laws at almost every complex shift. Bounded normalized squared
Frobenius norms handle the large singular values. Both sequences must control the logarithmic
contribution of the small singular values. -/
theorem ae_tendsto_eigenvalueMeasure_of_ae_tendsto_singularValueMeasure
    (hX : ∀ n, AEMeasurable (X n) P) (hY : ∀ n, AEMeasurable (Y n) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ (Y n ω).eigenvalueMeasure) atTop (𝓝 μ))
    (hbound : ∀ᵐ ω ∂P, ∃ C : ℝ≥0, ∀ᶠ n in atTop,
      ‖X n ω‖ ^ 2 / Fintype.card (ιs n) ≤ (C : ℝ) ∧
      ‖Y n ω‖ ^ 2 / Fintype.card (κs n) ≤ (C : ℝ))
    (hweak : ∀ᵐ z : ℂ ∂volume, ∀ᵐ ω ∂P, ∃ ν : ProbabilityMeasure ℝ,
      Tendsto (fun n ↦ (X n ω - z • 1).singularValueMeasure) atTop (𝓝 ν) ∧
      Tendsto (fun n ↦ (Y n ω - z • 1).singularValueMeasure) atTop (𝓝 ν))
    (hzeroX : ∀ᵐ z : ℂ ∂volume, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ a > (0 : ℝ),
      ∀ᶠ n in atTop, ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x)
        ∂((X n ω - z • 1).singularValueMeasure : Measure ℝ) ≤ ENNReal.ofReal ε)
    (hzeroY : ∀ᵐ z : ℂ ∂volume, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ a > (0 : ℝ),
      ∀ᶠ n in atTop, ∫⁻ x in Ioo 0 a, ENNReal.ofReal (-Real.log x)
        ∂((Y n ω - z • 1).singularValueMeasure : Measure ℝ) ≤ ENNReal.ofReal ε) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ (X n ω).eigenvalueMeasure) atTop (𝓝 μ) := by
  refine ae_tendsto_eigenvalueMeasure_of_ae_tendsto_of_ae_ae_tendsto_logarithmicPotential_sub
    hX hY hlim ?_
  filter_upwards [hweak, hzeroX, hzeroY, ae_ae_forall_notMem_spectrum hX,
    ae_ae_forall_notMem_spectrum hY] with z hw hzX hzY hsX hsY
  filter_upwards [hw, hzX, hzY, hsX, hsY, hbound] with ω hω hωX hωY hsωX hsωY hb
  obtain ⟨ν, hνX, hνY⟩ := hω
  obtain ⟨C, hC⟩ := hb
  have hlogX := (tendsto_integral_log_singularValueMeasure_sub_smul_one hνX
    (Eventually.of_forall hsωX) ⟨C, hC.mono fun _ h ↦ h.1⟩ hωX).2.2
  have hlogY := (tendsto_integral_log_singularValueMeasure_sub_smul_one hνY
    (Eventually.of_forall hsωY) ⟨C, hC.mono fun _ h ↦ h.2⟩ hωY).2.2
  simp_rw [logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure _ (hsωX _),
    logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure _ (hsωY _)]
  simpa only [sub_self] using hlogX.sub hlogY

end Convergence

end Matrix
