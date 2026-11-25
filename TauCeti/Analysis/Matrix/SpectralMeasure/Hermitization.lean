/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.LogarithmicPotential
public import TauCeti.Analysis.Matrix.SpectralMeasure.SingularValues

import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

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
of its shifts: together with the potential continuity theorem
`Matrix.ae_tendsto_eigenvalueMeasure_of_ae_ae_tendsto_logarithmicPotential`, weak limits of
eigenvalue measures follow from limits of `∫ log s dν(s)` for almost every shift `z`.

## Main results

* `Matrix.logarithmicPotential_eigenvalueMeasure_eq_log_norm_det`: off the spectrum,
  `U(z) = n⁻¹ log ‖det (A - z • 1)‖`.
* `Matrix.logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure`: Girko's
  hermitization identity off the spectrum, with its almost-everywhere and random-matrix forms
  `Matrix.ae_logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure` and
  `Matrix.ae_ae_logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure`.

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
    rw [spectrum.notMem_iff, Algebra.algebraMap_eq_smul_one, ← neg_sub, IsUnit.neg_iff,
      isUnit_iff_isUnit_det] at hz
    exact hz.ne_zero
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
  exact logarithmicPotential_eigenvalueMeasure_eq_integral_log_singularValueMeasure _ (hω k)

end Eigenvalues

end Matrix
