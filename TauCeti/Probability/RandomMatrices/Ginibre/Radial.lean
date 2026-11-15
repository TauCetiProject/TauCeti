/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.RandomMatrices.Ginibre.Density

/-!
# Gamma marginals of complex Gaussian Gram matrices

The diagonal entries of an `m`-dimensional complex Gaussian Gram matrix with `n > 0` samples
are independent gamma variables with shape `n` and rate one. Its trace has gamma law with
shape `m * n` when both dimensions are positive. In dimension one this identifies the Gram
eigenvalue law explicitly, including the exponential law for one sample.

The independence is a joint-law statement: each diagonal is the squared norm of a different
Ginibre row. The trace is the sum of all squared entry moduli. At zero sample size the entire
Gram matrix is zero, rather than a gamma variable of shape zero.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace TauCeti.Probability

/-- The real diagonals of a standard complex Gaussian Gram matrix are independent
gamma variables of shape equal to the positive sample size and rate one. -/
theorem map_diag_re_gaussianGramComplex (m n : ℕ) [NeZero n] :
    (gaussianGramComplex m n).map (fun A i ↦ (A i i).re) =
      Measure.pi (fun _ : Fin m ↦ gammaMeasure n 1) := by
  have hc := (measurePreserving_piCurry
    (fun _ : Fin m ↦ fun _ : Fin n ↦ properComplexGaussianScalar)).comp
      ((measurePreserving_piCongrLeft
        (fun _ : Fin m × Fin n ↦ properComplexGaussianScalar)
        (Equiv.sigmaEquivProd (Fin m) (Fin n))).symm)
  have hsum : (Measure.pi fun _ : Fin m ↦
      Measure.pi fun _ : Fin n ↦ properComplexGaussianScalar).map
        (fun z i ↦ ∑ j, ‖z i j‖ ^ 2) =
      Measure.pi (fun _ : Fin m ↦ gammaMeasure n 1) := by
    rw [Measure.pi_map_pi (f := fun _ (z : Fin n → ℂ) ↦ ∑ j, ‖z j‖ ^ 2)
      (fun _ ↦ (by fun_prop : Measurable (fun z : Fin n → ℂ ↦ ∑ j, ‖z j‖ ^ 2)).aemeasurable)]
    simp only [map_sum_norm_sq_pi_properComplexGaussianScalar, Fintype.card_fin]
  rw [← hc.map_eq, Measure.map_map (by fun_prop) hc.measurable] at hsum
  have hc_fun :
      (⇑(MeasurableEquiv.piCurry (fun _ : Fin m ↦ fun _ : Fin n ↦ ℂ)) ∘
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin m × Fin n ↦ ℂ)
          (Equiv.sigmaEquivProd (Fin m) (Fin n))).symm) =
      (fun z i j ↦ z (i, j)) := by
    ext z i j
    rfl
  rw [hc_fun] at hsum
  rw [gaussianGramComplex_def, Measure.map_map (by fun_prop) (by fun_prop),
    ginibreComplex_def, Measure.map_map (by fun_prop) (by fun_prop)]
  convert hsum using 1
  congr 1
  funext z
  ext i
  simp only [Function.comp_def, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Complex.re_sum]
  simp [Complex.mul_re, ← pow_two, Complex.sq_norm, Complex.normSq_apply]

/-- A diagonal entry of a standard complex Gaussian Gram matrix has gamma law with
shape the positive sample size and rate one. -/
theorem map_apply_diag_re_gaussianGramComplex (m n : ℕ) [NeZero n] (i : Fin m) :
    (gaussianGramComplex m n).map (fun A ↦ (A i i).re) = gammaMeasure n 1 := by
  have : IsProbabilityMeasure (gammaMeasure (n : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
      (by norm_num)
  rw [← (measurePreserving_eval (fun _ : Fin m ↦ gammaMeasure (n : ℝ) 1) i).map_eq,
    ← map_diag_re_gaussianGramComplex m n, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The trace of a standard complex Gaussian Gram matrix is gamma with shape `m * n`
and rate one when both dimensions are positive. -/
theorem map_trace_re_gaussianGramComplex (m n : ℕ) [NeZero m] [NeZero n] :
    (gaussianGramComplex m n).map (fun A ↦ A.trace.re) = gammaMeasure (m * n) 1 := by
  rw [gaussianGramComplex_def, Measure.map_map (by fun_prop) (by fun_prop),
    ginibreComplex_def, Measure.map_map (by fun_prop) (by fun_prop)]
  have h := map_sum_norm_sq_pi_properComplexGaussianScalar (ι := Fin m × Fin n)
  convert h using 1
  · congr 1
    funext z
    simpa only [Function.comp_def, Matrix.of_apply, Fintype.sum_prod_type,
      RCLike.re_to_complex] using
      Matrix.re_trace_mul_conjTranspose_self (Matrix.of fun i j ↦ z (i, j))
  · simp

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
  {A : Ω → Matrix (Fin m) (Fin m) ℂ}

/-- The joint law of the diagonal entries of a complex Gaussian Gram random matrix is a
product of gamma laws. -/
theorem HasLaw.diag_re_gaussianGramComplex [NeZero n]
    (hA : HasLaw A (gaussianGramComplex m n) P) :
    HasLaw (fun ω i ↦ (A ω i i).re) (Measure.pi fun _ : Fin m ↦ gammaMeasure n 1) P :=
  (HasLaw.mk
    ((by fun_prop :
      Measurable (fun A : Matrix (Fin m) (Fin m) ℂ ↦ fun i ↦ (A i i).re)).aemeasurable)
    (map_diag_re_gaussianGramComplex m n)).comp hA

/-- The trace of a complex Gaussian Gram random matrix has gamma law with shape `m * n`.
Both dimensions must be positive. -/
theorem HasLaw.trace_re_gaussianGramComplex [NeZero m] [NeZero n]
    (hA : HasLaw A (gaussianGramComplex m n) P) :
    HasLaw (fun ω ↦ (A ω).trace.re) (gammaMeasure (m * n) 1) P :=
  (HasLaw.mk (by fun_prop) (map_trace_re_gaussianGramComplex m n)).comp hA

end ProbabilityTheory
