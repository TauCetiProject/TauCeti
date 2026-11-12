/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Norm
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Coordinate flux for the ADM mass

The coordinate flux uses the Euclidean outward normal and Euclidean surface measure,
not the normal and area form of the metric being measured. The coefficients are allowed
to be arbitrary functions: symmetry and positive definiteness are not needed for the
linear flux calculation. Differentiability is stated in the lemmas using linearity of
`fderiv`.

`coordinateFluxIntegrand_diagonal` reduces the flux of `w δ` to the radial derivative
of `w`. For a radial factor this is constant on each coordinate sphere; the corresponding
integral is computed by `normalizedCoordinateFlux_radial`. These formulas fix the sign
and the factor `2(n - 1)` in the mass normalization, without asserting existence of a
mass limit.

## References

* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the
  spin setting*, arXiv:2108.11972v2, equation (2.1).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, §8, for the coordinate flux.
-/

public section

open MeasureTheory
open scoped BigOperators

namespace TauCeti

variable {n : ℕ}

/-- The ADM coordinate flux density at radius `r`, evaluated at `x`. On `‖x‖ = r > 0`,
`x / r` is the outward Euclidean unit normal. Coefficients are indexed by the standard
orthonormal basis of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def coordinateFluxIntegrand (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, (∑ i, (fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
    fderiv ℝ (fun y => g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))) * x j / r

/-- The coordinate-sphere flux divided by `2(n - 1)` times the Euclidean area of the
unit sphere. The ADM mass, when it exists, is its limit as `r → ∞`.

The integral is a Bochner integral; analytic applications must establish integrability.
The mass normalization is intended for `n ≥ 3`. -/
noncomputable def normalizedCoordinateFlux (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) : ℝ :=
  (∫ x in Metric.sphere 0 r, coordinateFluxIntegrand n g r x
    ∂Measure.euclideanHausdorffMeasure (n - 1)) /
      (2 * ((n : ℝ) - 1) *
        (Measure.euclideanHausdorffMeasure (n - 1)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)

/-- Constant coefficient matrices have zero coordinate flux, including the flat metric. -/
@[simp]
theorem coordinateFluxIntegrand_const (a : Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun _ => a) r x = 0 := by
  simp [coordinateFluxIntegrand]

/-- Constant coefficient matrices have zero normalized flux at every radius. -/
@[simp]
theorem normalizedCoordinateFlux_const (a : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun _ => a) r = 0 := by
  simp [normalizedCoordinateFlux]

/-- The coordinate flux is additive on differentiable coefficients. -/
theorem coordinateFluxIntegrand_add
    {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x) (r : ℝ) :
    coordinateFluxIntegrand n (fun y i j => g y i j + h y i j) r x =
      coordinateFluxIntegrand n g r x + coordinateFluxIntegrand n h r x := by
  have hsub (a b c d : ℝ) : a + b - (c + d) = (a - c) + (b - d) := by ring
  simp only [coordinateFluxIntegrand]
  simp_rw [fderiv_fun_add (hg _ _) (hh _ _), add_apply, hsub,
    Finset.sum_add_distrib, add_mul, add_div]
  exact Finset.sum_add_distrib

/-- Multiplication of coefficients by a constant multiplies the flux by that constant. -/
theorem coordinateFluxIntegrand_const_mul
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x) (c r : ℝ) :
    coordinateFluxIntegrand n (fun y i j => c * g y i j) r x =
      c * coordinateFluxIntegrand n g r x := by
  simp only [coordinateFluxIntegrand, fderiv_const_mul (hg _ _) c,
    smul_apply, smul_eq_mul, ← mul_sub, ← Finset.mul_sum,
    mul_assoc, mul_div_assoc]

/-- Adding a constant matrix does not change the coordinate flux. In particular, the
flux of a metric equals the flux of its perturbation from the Euclidean metric. -/
@[simp]
theorem coordinateFluxIntegrand_add_const
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (a : Fin n → Fin n → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => g y i j + a i j) r x =
      coordinateFluxIntegrand n g r x := by
  simp only [coordinateFluxIntegrand, fderiv_add_const]

/-- The normalized flux is unchanged by adding a constant matrix. -/
@[simp]
theorem normalizedCoordinateFlux_add_const
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (a : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => g y i j + a i j) r =
      normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux, coordinateFluxIntegrand_add_const]

/-- The normalized flux is additive when the two flux densities are integrable on the
coordinate sphere and all coefficients are differentiable there. -/
theorem normalizedCoordinateFlux_add
    {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hg : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x)
    (hgi : IntegrableOn (coordinateFluxIntegrand n g r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1)))
    (hhi : IntegrableOn (coordinateFluxIntegrand n h r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1))) :
    normalizedCoordinateFlux n (fun y i j => g y i j + h y i j) r =
      normalizedCoordinateFlux n g r + normalizedCoordinateFlux n h r := by
  unfold normalizedCoordinateFlux
  rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet
    (fun x hx => coordinateFluxIntegrand_add (hg x hx) (hh x hx) r),
    integral_add hgi hhi, add_div]

/-- Constant rescaling of differentiable coefficients rescales the normalized flux.
This is coefficientwise scaling in a fixed coordinate chart, not the geometric scaling
law for the mass in rescaled asymptotically Euclidean coordinates. -/
theorem normalizedCoordinateFlux_const_mul
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hg : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (c : ℝ) :
    normalizedCoordinateFlux n (fun y i j => c * g y i j) r =
      c * normalizedCoordinateFlux n g r := by
  unfold normalizedCoordinateFlux
  rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet
    (fun x hx => coordinateFluxIntegrand_const_mul (hg x hx) c r), integral_const_mul,
    mul_div_assoc]

/-- For the conformally Euclidean coefficient matrix `w δ`, the coordinate flux is
`-(n - 1) dw_x(x) / r`. This identity does not require `w` to be radial or positive. -/
theorem coordinateFluxIntegrand_diagonal
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (r : ℝ) :
    coordinateFluxIntegrand n (fun y i j => if i = j then w y else 0) r x =
      -((n : ℝ) - 1) * fderiv ℝ w x x / r := by
  classical
  have hd (i j k : Fin n) :
      fderiv ℝ (fun y => if i = j then w y else 0) x
          (EuclideanSpace.basisFun (Fin n) ℝ k) =
        if i = j then fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ k) else 0 := by
    split_ifs <;> simp
  have hsum : ∑ j, fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) * x j =
      fderiv ℝ w x x := by
    have h := congrArg (fderiv ℝ w x) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x)
    simpa [map_sum, map_smul, smul_eq_mul, mul_comm] using h
  simp only [coordinateFluxIntegrand]
  simp_rw [hd]
  simp only [ite_true, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hfactor (a : ℝ) : a - n * a = -((n : ℝ) - 1) * a := by ring
  simp_rw [hfactor, mul_assoc, mul_div_assoc, ← Finset.mul_sum]
  simp only [← mul_div_assoc, ← Finset.sum_div, hsum]

/-- For a radial conformally Euclidean matrix `f(‖x‖) δ`, the flux on the coordinate
sphere of positive radius `r` is the constant `-(n - 1) f'(r)`. -/
theorem coordinateFluxIntegrand_radial {f : ℝ → ℝ} {f' r : ℝ}
    (hf : HasDerivAt f f' r) (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere 0 r) :
    coordinateFluxIntegrand n (fun y i j => if i = j then f ‖y‖ else 0) r x =
      -((n : ℝ) - 1) * f' := by
  have hxr : ‖x‖ = r := by simpa using hx
  have hx0 : x ≠ 0 := by intro h; simp [h] at hxr; linarith
  have hn : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x :=
    (contDiffAt_id.norm ℝ hx0).differentiableAt one_ne_zero
  have hf' : HasDerivAt f f' ‖x‖ := hxr ▸ hf
  rw [coordinateFluxIntegrand_diagonal,
    fderiv_fun_comp x hf'.differentiableAt hn, hf'.hasFDerivAt.fderiv,
    ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    hn.fderiv_norm_self, hxr]
  field_simp

/-- The normalized flux of a radial conformally Euclidean matrix, expressed using the
areas of the radius-`r` and unit spheres. No mass limit or area-scaling formula is assumed. -/
theorem normalizedCoordinateFlux_radial {f : ℝ → ℝ} {f' r : ℝ}
    (hf : HasDerivAt f f' r) (hr : 0 < r) :
    normalizedCoordinateFlux n (fun y i j => if i = j then f ‖y‖ else 0) r =
      (-((n : ℝ) - 1) * f' *
        (Measure.euclideanHausdorffMeasure (n - 1)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r)).toReal) /
      (2 * ((n : ℝ) - 1) *
        (Measure.euclideanHausdorffMeasure (n - 1)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) := by
  unfold normalizedCoordinateFlux
  congr 1
  rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet
    (fun x hx => coordinateFluxIntegrand_radial hf hr hx), integral_const]
  simp [Measure.real, mul_comm]

end TauCeti
