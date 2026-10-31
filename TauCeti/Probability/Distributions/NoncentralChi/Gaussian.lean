/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian
public import TauCeti.Probability.Distributions.NoncentralChi.PDF

/-!
# Gaussian constructions of noncentral chi laws

The Euclidean norm of a Gaussian vector with spherical covariance has a noncentral chi law.
For a vector with mean `s • m` and covariance `s ^ 2 • 1`, the degree is the dimension, the
noncentrality is `‖m‖`, and the scale is `s`. This includes dimension zero. In dimension two it
is the Gaussian construction of the Rice distribution.

The result follows from the corresponding squared-norm construction and the defining square-root
pushforward of the noncentral chi law. The scaled version is then obtained by transporting the
identity-covariance Gaussian along scalar multiplication.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The norm of an identity-covariance Gaussian vector has noncentral chi law with unit scale
and noncentrality equal to the norm of its mean. Dimension zero is included. -/
@[simp]
theorem map_norm_multivariateGaussian_noncentral [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) :
    (multivariateGaussian m (1 : Matrix ι ι ℝ)).map (fun x ↦ ‖x‖) =
      noncentralChiMeasure (Fintype.card ι) ‖m‖₊ 1 := by
  rw [noncentralChiMeasure_of_scale_pos one_pos,
    ← map_norm_sq_multivariateGaussian_noncentral m]
  simp only [one_mul]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact (sqrt_sq (norm_nonneg x)).symm

private theorem map_norm_smul_multivariateGaussian_noncentral [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) {s : ℝ} (hs : 0 < s) :
    (multivariateGaussian (s • m) (s ^ 2 • (1 : Matrix ι ι ℝ))).map (fun x ↦ ‖x‖) =
      noncentralChiMeasure (Fintype.card ι) ‖m‖₊ s := by
  have hgauss :
      (multivariateGaussian m (1 : Matrix ι ι ℝ)).map (fun z ↦ s • z) =
        multivariateGaussian (s • m) (s ^ 2 • (1 : Matrix ι ι ℝ)) := by
    simpa using map_add_smul_multivariateGaussian m Matrix.PosSemidef.one 0 s
  rw [← hgauss, Measure.map_map (by fun_prop) (by fun_prop)]
  have hnorm : (fun z : EuclideanSpace ℝ ι ↦ ‖s • z‖) = fun z ↦ s * ‖z‖ := by
    funext z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  change (multivariateGaussian m (1 : Matrix ι ι ℝ)).map (fun z ↦ ‖s • z‖) = _
  rw [hnorm]
  change (multivariateGaussian m (1 : Matrix ι ι ℝ)).map
    ((fun x : ℝ ↦ s * x) ∘ fun z ↦ ‖z‖) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop),
    map_norm_multivariateGaussian_noncentral m,
    noncentralChiMeasure_map_const_mul (s := 1) hs, mul_one]

/-- The norm of a Gaussian vector with mean `m` and spherical covariance `s ^ 2 • 1` has
noncentral chi law with noncentrality `‖m‖ / s` and scale `s`. -/
theorem map_norm_multivariateGaussian_noncentral_of_scale [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) {s : ℝ} (hs : 0 < s) :
    (multivariateGaussian m (s ^ 2 • (1 : Matrix ι ι ℝ))).map (fun x ↦ ‖x‖) =
      noncentralChiMeasure (Fintype.card ι) (‖m‖₊ / s.toNNReal) s := by
  have hmean : s • (s⁻¹ • m) = m := by
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  rw [← hmean, map_norm_smul_multivariateGaussian_noncentral (s⁻¹ • m) hs]
  congr 2
  apply NNReal.eq
  simp [norm_smul, Real.norm_eq_abs, abs_of_pos hs, Real.coe_toNNReal _ hs.le]
  field_simp [hs.ne']

/-- The planar specialization of the spherical Gaussian norm construction. This is the measure
identity underlying the Rice distribution. -/
theorem map_norm_multivariateGaussian_fin_two_noncentral
    (m : EuclideanSpace ℝ (Fin 2)) {s : ℝ} (hs : 0 < s) :
    (multivariateGaussian m (s ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ))).map (fun x ↦ ‖x‖) =
      noncentralChiMeasure 2 (‖m‖₊ / s.toNNReal) s := by
  simpa using map_norm_multivariateGaussian_noncentral_of_scale m hs

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The norm of an identity-covariance Gaussian random vector has noncentral chi law. -/
theorem HasLaw.norm_multivariateGaussian_noncentral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ ι}
    (hX : HasLaw X (multivariateGaussian m (1 : Matrix ι ι ℝ)) P) :
    HasLaw (fun ω ↦ ‖X ω‖) (noncentralChiMeasure (Fintype.card ι) ‖m‖₊ 1) P :=
  (HasLaw.mk (by fun_prop) (map_norm_multivariateGaussian_noncentral m)).fun_comp hX

/-- The norm of a spherical Gaussian random vector has noncentral chi law. -/
theorem HasLaw.norm_multivariateGaussian_noncentral_of_scale {ι : Type*} [Fintype ι]
    [DecidableEq ι] {X : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ ι} {s : ℝ}
    (hs : 0 < s)
    (hX : HasLaw X (multivariateGaussian m (s ^ 2 • (1 : Matrix ι ι ℝ))) P) :
    HasLaw (fun ω ↦ ‖X ω‖)
      (noncentralChiMeasure (Fintype.card ι) (‖m‖₊ / s.toNNReal) s) P :=
  (HasLaw.mk (by fun_prop)
    (map_norm_multivariateGaussian_noncentral_of_scale m hs)).fun_comp hX

/-- The norm of a planar spherical Gaussian random vector has the Rice law, expressed as the
degree-two noncentral chi law. -/
theorem HasLaw.norm_multivariateGaussian_fin_two_noncentral
    {X : Ω → EuclideanSpace ℝ (Fin 2)} {m : EuclideanSpace ℝ (Fin 2)} {s : ℝ}
    (hs : 0 < s)
    (hX : HasLaw X
      (multivariateGaussian m (s ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ))) P) :
    HasLaw (fun ω ↦ ‖X ω‖) (noncentralChiMeasure 2 (‖m‖₊ / s.toNNReal) s) P :=
  (HasLaw.mk (by fun_prop)
    (map_norm_multivariateGaussian_fin_two_noncentral m hs)).fun_comp hX

end ProbabilityTheory
