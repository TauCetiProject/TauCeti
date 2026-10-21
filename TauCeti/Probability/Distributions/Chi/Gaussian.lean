/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Chi.Basic
public import TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gaussian constructions of chi laws

The norm of a standard Gaussian vector in a finite-dimensional real inner product space has
the chi law with degrees of freedom equal to the dimension. Multiplying that norm by a positive
scale gives the corresponding scaled chi law. Dimension zero is included and gives a point mass
at zero.

For independent centered real Gaussians with common positive variance, the Euclidean norm has
scale equal to the square root of that variance. Dimensions one, two, and three give the
half-normal, Rayleigh, and Maxwell–Boltzmann constructions, respectively. The scalar
absolute-value identity is also provided directly. These identifications allow the density,
moments, and quantiles of chi laws to be used for Gaussian radii.

The proofs reuse `map_sum_sq_pi_gaussianReal` and Mathlib's orthonormal-basis representation
`stdGaussian_eq_map_pi_orthonormalBasis`.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  second edition, Wiley, 1994, chapter 18.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

section InnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The radius of a standard Gaussian vector has the unit-scale chi law, including in
dimension zero. -/
@[simp]
theorem stdGaussian_map_norm :
    (stdGaussian E).map (fun x ↦ ‖x‖) = chiMeasure (Module.finrank ℝ E) 1 := by
  let b := stdOrthonormalBasis ℝ E
  have hsq : (Measure.pi fun _ : Fin (Module.finrank ℝ E) ↦ gaussianReal 0 1).map
      (fun x ↦ ∑ i, x i ^ 2) = chiSquaredMeasure (Module.finrank ℝ E) := by
    simpa using map_sum_sq_pi_gaussianReal (ι := Fin (Module.finrank ℝ E)) 1
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    Measure.map_map (by fun_prop) (by fun_prop), chiMeasure_of_scale_pos zero_lt_one,
    ← hsq, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, one_mul]
  rw [b.sum_repr_symm (WithLp.toLp 2 x), b.repr.symm.norm_map,
    ← EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x), Real.sqrt_sq (norm_nonneg _)]

/-- A positive multiple of a standard Gaussian radius has the chi law with that scale. -/
@[simp]
theorem stdGaussian_map_const_mul_norm {s : ℝ} (hs : 0 < s) :
    (stdGaussian E).map (fun x ↦ s * ‖x‖) = chiMeasure (Module.finrank ℝ E) s := by
  have h := congrArg (fun μ : Measure ℝ ↦ μ.map (fun x ↦ s * x)) (stdGaussian_map_norm E)
  rw [Measure.map_map (by fun_prop) (by fun_prop), chiMeasure_map_const_mul hs, mul_one] at h
  exact h

end InnerProductSpace

variable {ι : Type*} [Fintype ι] {v : ℝ≥0}

/-- The Euclidean norm of independent centered Gaussians with common positive variance has
the chi law with one degree per coordinate and scale equal to the standard deviation.
In dimensions two and three this is the Rayleigh and Maxwell–Boltzmann construction. -/
@[simp]
theorem map_norm_pi_gaussianReal (hv : v ≠ 0) :
    (Measure.pi fun _ : ι ↦ gaussianReal 0 v).map
        (fun x ↦ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖) =
      chiMeasure (Fintype.card ι) (Real.sqrt v) := by
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  rw [chiMeasure_of_scale_pos hs]
  have h := congrArg (fun μ : Measure ℝ ↦ μ.map Real.sqrt)
    (map_sum_sq_pi_gaussianReal (ι := ι) v)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  simp only [Function.comp_def, Real.sqrt_mul v.coe_nonneg] at h
  convert h using 2
  funext x
  simpa using EuclideanSpace.norm_eq (WithLp.toLp 2 x : EuclideanSpace ℝ ι)

/-- The absolute value of a centered Gaussian with positive variance is half-normal:
it has the one-degree chi law with scale equal to the standard deviation. -/
@[simp]
theorem gaussianReal_map_abs (hv : v ≠ 0) :
    (gaussianReal 0 v).map (fun x ↦ |x|) = chiMeasure 1 (Real.sqrt v) := by
  have hnorm : (fun x : Unit → ℝ ↦ ‖(WithLp.toLp 2 x : EuclideanSpace ℝ Unit)‖) =
      fun x ↦ |x ()| := by
    funext x
    simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  have h := map_norm_pi_gaussianReal (ι := Unit) hv
  rw [hnorm] at h
  have hmap := Measure.map_map (μ := Measure.pi fun _ : Unit ↦ gaussianReal 0 v)
    (g := fun x : ℝ ↦ |x|) (f := fun x : Unit → ℝ ↦ x ()) (by fun_prop) (by fun_prop)
  rw [(measurePreserving_eval (fun _ : Unit ↦ gaussianReal 0 v) ()).map_eq] at hmap
  simpa only [Fintype.card_unit, Nat.cast_one] using hmap.trans h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {X : Ω → E}

/-- The norm of a standard Gaussian random vector has the unit-scale chi law. -/
theorem HasLaw.norm_stdGaussian (hX : HasLaw X (stdGaussian E) P) :
    HasLaw (fun ω ↦ ‖X ω‖) (chiMeasure (Module.finrank ℝ E) 1) P :=
  (HasLaw.mk (by fun_prop) (stdGaussian_map_norm E)).fun_comp hX

/-- A positive multiple of the norm of a standard Gaussian random vector has a scaled chi law. -/
theorem HasLaw.const_mul_norm_stdGaussian (hX : HasLaw X (stdGaussian E) P)
    {s : ℝ} (hs : 0 < s) :
    HasLaw (fun ω ↦ s * ‖X ω‖) (chiMeasure (Module.finrank ℝ E) s) P :=
  (HasLaw.mk (by fun_prop) (stdGaussian_map_const_mul_norm E hs)).fun_comp hX

/-- Independent centered Gaussian coordinates of a common positive variance have a chi radius. -/
theorem iIndepFun.hasLaw_norm_gaussianReal {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ}
    (hindep : iIndepFun Y P) {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : ∀ i, HasLaw (Y i) (gaussianReal 0 v) P) :
    HasLaw (fun ω ↦ ‖(WithLp.toLp 2 (fun i ↦ Y i ω) : EuclideanSpace ℝ ι)‖)
      (chiMeasure (Fintype.card ι) (Real.sqrt v)) P :=
  (HasLaw.mk (by fun_prop) (map_norm_pi_gaussianReal hv)).fun_comp (hindep.hasLaw_pi hlaw)

/-- Taking the absolute value of a centered positive-variance Gaussian gives a half-normal law. -/
theorem HasLaw.abs_gaussianReal {Y : Ω → ℝ} {v : ℝ≥0}
    (hY : HasLaw Y (gaussianReal 0 v) P) (hv : v ≠ 0) :
    HasLaw (fun ω ↦ |Y ω|) (chiMeasure 1 (Real.sqrt v)) P :=
  (HasLaw.mk (by fun_prop) (gaussianReal_map_abs hv)).fun_comp hY

end ProbabilityTheory
