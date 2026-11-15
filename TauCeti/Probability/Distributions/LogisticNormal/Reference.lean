/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.LogisticNormal.Basic
import TauCeti.Probability.Distributions.Gaussian.Affine

/-!
# Changing the reference category of a logistic-normal law

Additive log ratios with reference category `r` become log ratios with reference `s` by
subtracting the log ratio of `s` from every coordinate, after restoring the omitted coordinate
as zero. This is a linear equivalence, with inverse given by exchanging the references.

`logisticNormalReferenceEquiv` bundles this change of coordinates, and
`logisticNormalReferenceMatrix` gives its matrix for transforming Gaussian covariances.
The logistic charts intertwine this equivalence, so changing reference and transforming the
Gaussian mean and covariance leaves the simplex law unchanged. The measure identity holds for
every covariance: invertibility preserves positive semidefiniteness, including its failure,
and hence also preserves the Gaussian point-mass fallback.

## References

* J. Aitchison and S. M. Shen, *Logistic-normal distributions: Some properties and uses*,
  Biometrika 67(2), 261–272, 1980.

The Gaussian transport uses `TauCeti.Probability.map_affine_multivariateGaussian`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The linear change from additive log ratios relative to `r` to those relative to `s`.
Restore the missing `r` coordinate as zero, then subtract the `s` coordinate. -/
def logisticNormalReferenceEquiv (r s : ι) :
    EuclideanSpace ℝ {i // i ≠ r} ≃ₗ[ℝ] EuclideanSpace ℝ {i // i ≠ s} where
  toFun z := WithLp.toLp 2 (fun j ↦
    (Equiv.funSplitAt r ℝ).symm (0, fun k ↦ z k) j -
      (Equiv.funSplitAt r ℝ).symm (0, fun k ↦ z k) s)
  invFun z := WithLp.toLp 2 (fun j ↦
    (Equiv.funSplitAt s ℝ).symm (0, fun k ↦ z k) j -
      (Equiv.funSplitAt s ℝ).symm (0, fun k ↦ z k) r)
  left_inv z := by
    ext j
    by_cases hrs : r = s
    · subst s
      simp [Equiv.funSplitAt_symm_apply, j.property]
    · by_cases hjs : (j : ι) = s
      · simpa [Equiv.funSplitAt_symm_apply, hrs, Ne.symm hrs, hjs] using
          congrArg z (Subtype.ext hjs.symm)
      · simp [Equiv.funSplitAt_symm_apply, hrs, Ne.symm hrs, hjs, j.property]
  right_inv z := by
    ext j
    by_cases hrs : r = s
    · subst s
      simp [Equiv.funSplitAt_symm_apply, j.property]
    · by_cases hjr : (j : ι) = r
      · simpa [Equiv.funSplitAt_symm_apply, hrs, Ne.symm hrs, hjr] using
          congrArg z (Subtype.ext hjr.symm)
      · simp [Equiv.funSplitAt_symm_apply, hrs, Ne.symm hrs, hjr, j.property]
  map_add' z w := by
    ext j
    simp only [Equiv.funSplitAt_symm_apply, PiLp.add_apply]
    split_ifs <;> ring
  map_smul' c z := by
    ext j
    simp only [Equiv.funSplitAt_symm_apply, PiLp.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

omit [Fintype ι] in
/-- The coordinate formula for a reference change, using zero for the omitted log ratio. -/
theorem logisticNormalReferenceEquiv_apply (r s : ι)
    (z : EuclideanSpace ℝ {i // i ≠ r}) (j : {i // i ≠ s}) :
    logisticNormalReferenceEquiv r s z j =
      (Equiv.funSplitAt r ℝ).symm (0, fun k ↦ z k) j -
        (Equiv.funSplitAt r ℝ).symm (0, fun k ↦ z k) s := (rfl)

omit [Fintype ι] in
/-- Exchanging the two references inverts the log-ratio coordinate change. -/
theorem logisticNormalReferenceEquiv_symm (r s : ι) :
    (logisticNormalReferenceEquiv r s).symm = logisticNormalReferenceEquiv s r := by
  ext z j
  rfl

omit [Fintype ι] in
/-- Keeping the same reference gives the identity equivalence. -/
@[simp]
theorem logisticNormalReferenceEquiv_self (r : ι) :
    logisticNormalReferenceEquiv r r = LinearEquiv.refl ℝ _ := by
  ext z j
  simp [logisticNormalReferenceEquiv_apply, j.property]

/-- The new additive log ratios of a logistic chart are its linear reference change. -/
@[simp]
theorem logisticNormalLogRatio_chart_reference (r s : ι)
    (z : EuclideanSpace ℝ {i // i ≠ r}) :
    logisticNormalLogRatio s (logisticNormalChart r z) =
      logisticNormalReferenceEquiv r s z := by
  ext j
  have hD : 1 + ∑ k, Real.exp (z k) ≠ 0 := by positivity
  simp only [logisticNormalLogRatio_apply, logisticNormalChart_apply,
    logisticNormalReferenceEquiv_apply, Equiv.funSplitAt_symm_apply]
  split_ifs <;> simp_all [Real.log_div]
  ring

/-- Reference changes intertwine the two logistic charts. -/
@[simp]
theorem logisticNormalChart_reference (r s : ι)
    (z : EuclideanSpace ℝ {i // i ≠ r}) :
    logisticNormalChart s (logisticNormalReferenceEquiv r s z) = logisticNormalChart r z := by
  rw [← logisticNormalLogRatio_chart_reference]
  exact logisticNormalChart_logRatio s (logisticNormalChart_pos r z)
    (sum_logisticNormalChart r z)

/-- The matrix of the linear log-ratio reference change. It sends Gaussian covariance `S` to
`B * S * B.transpose`. -/
def logisticNormalReferenceMatrix (r s : ι) : Matrix {i // i ≠ s} {i // i ≠ r} ℝ :=
  Matrix.toEuclideanLin.symm (logisticNormalReferenceEquiv r s).toLinearMap

/-- The reference-change matrix acts by the bundled coordinate equivalence. -/
@[simp]
theorem toEuclideanLin_logisticNormalReferenceMatrix (r s : ι) :
    (logisticNormalReferenceMatrix r s).toEuclideanLin =
      (logisticNormalReferenceEquiv r s).toLinearMap := by
  rw [logisticNormalReferenceMatrix, LinearEquiv.apply_symm_apply]

/-- The reference-change matrix has entries given by the difference of two coordinate
indicators, so it can be used directly in covariance calculations. -/
@[simp]
theorem logisticNormalReferenceMatrix_apply (r s : ι)
    (i : {i // i ≠ s}) (j : {i // i ≠ r}) :
    logisticNormalReferenceMatrix r s i j =
      (if (i : ι) = j then 1 else 0) - (if s = j then 1 else 0) := by
  have h := congrArg (fun f ↦ f (EuclideanSpace.single j 1) i)
    (toEuclideanLin_logisticNormalReferenceMatrix r s)
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.toLp_apply,
    PiLp.ofLp_single, Matrix.mulVec_single_one, Matrix.col_apply, LinearEquiv.coe_coe,
    logisticNormalReferenceEquiv_apply, Equiv.funSplitAt_symm_apply] at h
  rw [h]
  split_ifs <;> simp_all [Subtype.ext_iff, j.property]

/-- Keeping the same reference gives the identity matrix. -/
@[simp]
theorem logisticNormalReferenceMatrix_self (r : ι) :
    logisticNormalReferenceMatrix r r = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_logisticNormalReferenceMatrix, logisticNormalReferenceEquiv_self,
    Matrix.toLpLin_one]
  rfl

/-- The matrices for opposite reference changes multiply to the identity. -/
@[simp]
theorem logisticNormalReferenceMatrix_mul_reverse (r s : ι) :
    logisticNormalReferenceMatrix s r * logisticNormalReferenceMatrix r s = 1 := by
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toLpLin_mul_same, Matrix.toLpLin_one]
  rw [toEuclideanLin_logisticNormalReferenceMatrix,
    toEuclideanLin_logisticNormalReferenceMatrix]
  ext z j
  simpa only [logisticNormalReferenceEquiv_symm, LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_coe] using
    congrArg (fun x ↦ x j) ((logisticNormalReferenceEquiv r s).symm_apply_apply z)

/-- Changing log-ratio reference preserves covariance validity in both directions. -/
@[simp]
theorem posSemidef_logisticNormalReferenceMatrix_iff (r s : ι)
    (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) :
    (logisticNormalReferenceMatrix r s * S *
      (logisticNormalReferenceMatrix r s).transpose).PosSemidef ↔ S.PosSemidef := by
  constructor
  · intro h
    -- Applying the inverse congruence recovers the original covariance.
    have hback : logisticNormalReferenceMatrix s r *
        (logisticNormalReferenceMatrix r s * S *
          (logisticNormalReferenceMatrix r s).transpose) *
        (logisticNormalReferenceMatrix s r).transpose = S := by
      calc
        _ = (logisticNormalReferenceMatrix s r * logisticNormalReferenceMatrix r s) * S *
            (logisticNormalReferenceMatrix s r * logisticNormalReferenceMatrix r s).transpose := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = S := by simp
    have h' := h.mul_mul_conjTranspose_same (logisticNormalReferenceMatrix s r)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hback] using h'
  · intro h
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      h.mul_mul_conjTranspose_same (logisticNormalReferenceMatrix r s)

/-- The simplex logistic-normal law is independent of its reference category after the
corresponding linear change of Gaussian parameters. This includes singular and invalid
covariances, and the one-category case. -/
theorem logisticNormalMeasure_change_reference (r s : ι)
    (m : EuclideanSpace ℝ {i // i ≠ r}) (S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ) :
    logisticNormalMeasure r m S =
      logisticNormalMeasure s (logisticNormalReferenceEquiv r s m)
        (logisticNormalReferenceMatrix r s * S *
          (logisticNormalReferenceMatrix r s).transpose) := by
  by_cases hS : S.PosSemidef
  · have hG := map_affine_multivariateGaussian m hS (logisticNormalReferenceMatrix r s) 0
    simp only [toEuclideanLin_logisticNormalReferenceMatrix, LinearEquiv.coe_coe,
      add_zero] at hG
    have hB : Measurable (fun x ↦ logisticNormalReferenceEquiv r s x) :=
      (logisticNormalReferenceEquiv r s).toContinuousLinearEquiv.continuous.measurable
    rw [logisticNormalMeasure_def, logisticNormalMeasure_def, ← hG,
      Measure.map_map (measurable_logisticNormalChart s) hB]
    simp only [Function.comp_def, logisticNormalChart_reference]
  · rw [logisticNormalMeasure_of_not_posSemidef r m hS,
      logisticNormalMeasure_of_not_posSemidef s _
        (fun h ↦ hS ((posSemidef_logisticNormalReferenceMatrix_iff r s S).mp h)),
      logisticNormalChart_reference]

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Taking log ratios to any reference category of a logistic-normal vector gives the
Gaussian with the linearly transformed mean and covariance, including all fallbacks. -/
theorem logisticNormalLogRatio {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] {P : Measure Ω} {r : ι} {X : Ω → EuclideanSpace ℝ ι}
    {m : EuclideanSpace ℝ {i // i ≠ r}} {S : Matrix {i // i ≠ r} {i // i ≠ r} ℝ}
    (hX : HasLaw X (logisticNormalMeasure r m S) P) (s : ι) :
    HasLaw (fun ω ↦ logisticNormalLogRatio s (X ω))
      (multivariateGaussian (logisticNormalReferenceEquiv r s m)
        (logisticNormalReferenceMatrix r s * S *
          (logisticNormalReferenceMatrix r s).transpose)) P := by
  rw [logisticNormalMeasure_change_reference r s] at hX
  exact HasLaw.comp ⟨(measurable_logisticNormalLogRatio s).aemeasurable,
    map_logisticNormalLogRatio_logisticNormalMeasure s _ _⟩ hX

end ProbabilityTheory.HasLaw
