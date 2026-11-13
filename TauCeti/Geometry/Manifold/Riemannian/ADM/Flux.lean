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
public import TauCeti.Geometry.Euclidean.Volume.Sphere

/-!
# Coordinate flux for the ADM mass

`coordinateFluxIntegrand` is the ADM coordinate flux density, and
`normalizedCoordinateFlux` is its normalized coordinate-sphere integral. They use the
Euclidean outward normal and Euclidean surface measure, not the normal and area form
of the metric being measured. Coefficients may be arbitrary functions: symmetry and
positive definiteness are not needed. Both quantities are unchanged by constant shifts
and commute with constant rescaling. Additivity assumes differentiable coefficients
(and integrable flux densities for the sphere integral). Continuous coefficient derivatives
on a positive-radius sphere suffice for integrability. `normalizedCoordinateFlux_of_eqOn_const`
evaluates any flux density constant on the sphere, without a conformal or radial hypothesis.

`coordinateFluxIntegrand_scalar` reduces the integrand of `w δ` to
`-(n - 1) dw_x(x) / r`, which is `-(n - 1)` times the radial derivative on `‖x‖ = r > 0`.
For a radial factor this is constant on each coordinate sphere;
`normalizedCoordinateFlux_scalar_radial` gives the closed radial reduction used to
check the mass normalization downstream, without asserting existence of a mass limit.

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

/-- Unfolding formula for the coordinate flux integrand. -/
theorem coordinateFluxIntegrand_def (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n g r x =
      ∑ j, (∑ i, (fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
        fderiv ℝ (fun y => g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))) * x j / r :=
  (rfl)

/-- Unfolding formula for the normalized coordinate-sphere flux. -/
theorem normalizedCoordinateFlux_def (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n g r =
      (∫ x in Metric.sphere 0 r, coordinateFluxIntegrand n g r x
        ∂Measure.euclideanHausdorffMeasure (n - 1)) /
        (2 * ((n : ℝ) - 1) *
          (Measure.euclideanHausdorffMeasure (n - 1)
            (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) :=
  (rfl)

/-- The flux density depends only on the germ of the coefficient matrix at the point. -/
theorem coordinateFluxIntegrand_congr
    {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hgh : g =ᶠ[nhds x] h) (r : ℝ) :
    coordinateFluxIntegrand n g r x = coordinateFluxIntegrand n h r x := by
  have hd (i j : Fin n) : fderiv ℝ (fun y => g y i j) x =
      fderiv ℝ (fun y => h y i j) x :=
    Filter.EventuallyEq.fderiv_eq
      (hgh.mono fun _ hy => congrFun (congrFun hy i) j)
  simp only [coordinateFluxIntegrand, hd]

/-- Equality of flux densities on a sphere implies equality of normalized fluxes. -/
theorem normalizedCoordinateFlux_congr
    {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hgh : Set.EqOn (coordinateFluxIntegrand n g r) (coordinateFluxIntegrand n h r)
      (Metric.sphere 0 r)) :
    normalizedCoordinateFlux n g r = normalizedCoordinateFlux n h r := by
  unfold normalizedCoordinateFlux
  rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet hgh]

/-- Agreement of coefficient germs at every point of a sphere preserves its normalized flux.
This applies, in particular, to coefficients agreeing on an open exterior domain. -/
theorem normalizedCoordinateFlux_congr_of_eventuallyEq
    {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hgh : ∀ x ∈ Metric.sphere 0 r, g =ᶠ[nhds x] h) :
    normalizedCoordinateFlux n g r = normalizedCoordinateFlux n h r :=
  normalizedCoordinateFlux_congr fun x hx => coordinateFluxIntegrand_congr (hgh x hx) r

/-- Continuous coefficient derivatives give a continuous coordinate flux density. -/
theorem continuousOn_coordinateFluxIntegrand
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {s : Set (EuclideanSpace ℝ (Fin n))}
    (hg : ∀ i j, ContinuousOn (fun x => fderiv ℝ (fun y => g y i j) x) s) (r : ℝ) :
    ContinuousOn (coordinateFluxIntegrand n g r) s := by
  unfold coordinateFluxIntegrand
  fun_prop

/-- Continuous coefficient derivatives on a positive-radius sphere give an integrable flux
density for codimension-one Euclidean Hausdorff measure. -/
theorem integrableOn_coordinateFluxIntegrand
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hg : ∀ i j, ContinuousOn (fun x => fderiv ℝ (fun y => g y i j) x)
      (Metric.sphere 0 r)) (hr : 0 < r) :
    IntegrableOn (coordinateFluxIntegrand n g r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1)) := by
  simpa only [finrank_euclideanSpace_fin] using
    (continuousOn_coordinateFluxIntegrand hg r).integrableOn_sphere hr

/-- A flux density constant on a positive-radius sphere is integrable there. -/
theorem integrableOn_coordinateFluxIntegrand_of_eqOn_const
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r c : ℝ} (hr : 0 < r)
    (hc : Set.EqOn (coordinateFluxIntegrand n g r) (fun _ => c) (Metric.sphere 0 r)) :
    IntegrableOn (coordinateFluxIntegrand n g r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1)) := by
  simpa only [finrank_euclideanSpace_fin] using
    (continuousOn_const.congr hc).integrableOn_sphere hr

/-- The normalization denominator is `2(n - 1)|Sⁿ⁻¹|` in positive dimension. -/
theorem normalizedCoordinateFlux_eq_div_roundSphereVolume
    (hn : 1 ≤ n) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n g r =
      (∫ x in Metric.sphere 0 r, coordinateFluxIntegrand n g r x
        ∂Measure.euclideanHausdorffMeasure (n - 1)) /
        (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1 := by
    simp only [finrank_euclideanSpace_fin]
    omega
  rw [normalizedCoordinateFlux_def,
    euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume hdim,
    ENNReal.toReal_ofReal (roundSphereVolume_pos _).le]

/-- A constant sphere flux density gives its value times the sphere measure, divided by
the normalization denominator. No dimension or radius restriction is needed. -/
theorem normalizedCoordinateFlux_eq_div_of_eqOn_const
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r c : ℝ}
    (hc : Set.EqOn (coordinateFluxIntegrand n g r) (fun _ => c) (Metric.sphere 0 r)) :
    normalizedCoordinateFlux n g r =
      (c * (Measure.euclideanHausdorffMeasure (n - 1)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r)).toReal) /
        (2 * ((n : ℝ) - 1) * (Measure.euclideanHausdorffMeasure (n - 1)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) := by
  rw [normalizedCoordinateFlux_def,
    setIntegral_congr_fun Metric.isClosed_sphere.measurableSet hc, integral_const]
  simp [Measure.real, mul_comm]

/-- The normalized flux of any coefficient field with constant sphere flux density,
with the sphere areas cancelled. -/
theorem normalizedCoordinateFlux_of_eqOn_const
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r c : ℝ}
    (hn : 1 ≤ n) (hr : 0 < r)
    (hc : Set.EqOn (coordinateFluxIntegrand n g r) (fun _ => c) (Metric.sphere 0 r)) :
    normalizedCoordinateFlux n g r = c * r ^ (n - 1) / (2 * ((n : ℝ) - 1)) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1 := by
    simp only [finrank_euclideanSpace_fin]
    omega
  have hscale := setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one
    (n - 1) (0 : EuclideanSpace ℝ (Fin n)) hr (fun _ => (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply_univ] at hscale
  rw [normalizedCoordinateFlux_eq_div_of_eqOn_const hc, hscale,
    euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume hdim,
    ENNReal.toReal_ofReal (roundSphereVolume_pos _).le]
  simpa only [mul_assoc] using
    mul_div_mul_right (c * r ^ (n - 1)) (2 * ((n : ℝ) - 1))
      (roundSphereVolume_pos (n - 1)).ne'

/-- Constant coefficient matrices have zero coordinate flux density, including the flat metric. -/
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

/-- The coordinate flux integrand is additive on differentiable coefficients. -/
theorem coordinateFluxIntegrand_add
    {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x) (r : ℝ) :
    coordinateFluxIntegrand n (g + h) r x =
      coordinateFluxIntegrand n g r x + coordinateFluxIntegrand n h r x := by
  have hsub (a b c d : ℝ) : a + b - (c + d) = (a - c) + (b - d) := by ring
  simp only [coordinateFluxIntegrand, Pi.add_apply]
  simp_rw [fderiv_fun_add (hg _ _) (hh _ _), add_apply, hsub,
    Finset.sum_add_distrib, add_mul, add_div]
  exact Finset.sum_add_distrib

/-- Multiplication of coefficients by a constant rescales the flux integrand. -/
@[simp]
theorem coordinateFluxIntegrand_const_mul
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (c r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => c * g y i j) r x =
      c * coordinateFluxIntegrand n g r x := by
  have hd (i j : Fin n) : fderiv ℝ (fun y => c * g y i j) x =
      c • fderiv ℝ (fun y => g y i j) x :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) c) x
  simp only [coordinateFluxIntegrand, hd, smul_apply, smul_eq_mul, ← mul_sub,
    ← Finset.mul_sum, mul_assoc, mul_div_assoc]

/-- Adding a constant matrix does not change the coordinate flux integrand. In particular,
a metric and its perturbation from the Euclidean metric have the same flux density. -/
@[simp]
theorem coordinateFluxIntegrand_fun_add_const
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (a : Fin n → Fin n → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => g y i j + a i j) r x =
      coordinateFluxIntegrand n g r x := by
  simp only [coordinateFluxIntegrand, fderiv_add_const]

/-- The normalized flux is unchanged by adding a constant matrix. -/
@[simp]
theorem normalizedCoordinateFlux_fun_add_const
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (a : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => g y i j + a i j) r =
      normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux, coordinateFluxIntegrand_fun_add_const]

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
    normalizedCoordinateFlux n (g + h) r =
      normalizedCoordinateFlux n g r + normalizedCoordinateFlux n h r := by
  unfold normalizedCoordinateFlux
  rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet
    (fun x hx => coordinateFluxIntegrand_add (hg x hx) (hh x hx) r),
    integral_add hgi hhi, add_div]

/-- Constant rescaling of coefficients rescales the normalized flux.
This is coefficientwise scaling in a fixed coordinate chart, not the geometric scaling
law for the mass in rescaled asymptotically Euclidean coordinates. -/
@[simp]
theorem normalizedCoordinateFlux_const_mul
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (c r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => c * g y i j) r =
      c * normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux, coordinateFluxIntegrand_const_mul,
    integral_const_mul, mul_div_assoc]

section Operations

variable (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
  (a : Fin n → Fin n → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n))

/-- The zero coefficient field has zero flux density. -/
@[simp]
theorem coordinateFluxIntegrand_zero : coordinateFluxIntegrand n 0 r x = 0 :=
  coordinateFluxIntegrand_const 0 r x

/-- The zero coefficient field has zero normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_zero : normalizedCoordinateFlux n 0 r = 0 :=
  normalizedCoordinateFlux_const 0 r

/-- Constant matrix shifts on the left preserve the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_fun_const_add :
    coordinateFluxIntegrand n (fun y i j => a i j + g y i j) r x =
      coordinateFluxIntegrand n g r x := by
  simpa only [add_comm] using coordinateFluxIntegrand_fun_add_const g a r x

/-- Constant matrix shifts on the left preserve the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_fun_const_add :
    normalizedCoordinateFlux n (fun y i j => a i j + g y i j) r =
      normalizedCoordinateFlux n g r := by
  simpa only [add_comm] using normalizedCoordinateFlux_fun_add_const g a r

/-- Subtracting a constant matrix preserves the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_fun_sub_const :
    coordinateFluxIntegrand n (fun y i j => g y i j - a i j) r x =
      coordinateFluxIntegrand n g r x := by
  simpa only [sub_eq_add_neg, Pi.neg_apply] using coordinateFluxIntegrand_fun_add_const g (-a) r x

/-- Subtracting a constant matrix preserves the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_fun_sub_const :
    normalizedCoordinateFlux n (fun y i j => g y i j - a i j) r =
      normalizedCoordinateFlux n g r := by
  simpa only [sub_eq_add_neg, Pi.neg_apply] using normalizedCoordinateFlux_fun_add_const g (-a) r

/-- Scalar multiplication of coefficient fields rescales the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_smul (c : ℝ) :
    coordinateFluxIntegrand n (c • g) r x = c * coordinateFluxIntegrand n g r x :=
  coordinateFluxIntegrand_const_mul g c r x

/-- Scalar multiplication of coefficient fields rescales the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_smul (c : ℝ) :
    normalizedCoordinateFlux n (c • g) r = c * normalizedCoordinateFlux n g r :=
  normalizedCoordinateFlux_const_mul g c r

/-- Negation of coefficient fields negates the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_neg :
    coordinateFluxIntegrand n (-g) r x = -coordinateFluxIntegrand n g r x := by
  simpa [Pi.neg_def] using coordinateFluxIntegrand_const_mul g (-1) r x

/-- Negation of coefficient fields negates the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_neg :
    normalizedCoordinateFlux n (-g) r = -normalizedCoordinateFlux n g r := by
  simpa [Pi.neg_def] using normalizedCoordinateFlux_const_mul g (-1) r

/-- Pointwise negation of coefficients negates the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_fun_neg :
    coordinateFluxIntegrand n (fun y i j => -g y i j) r x =
      -coordinateFluxIntegrand n g r x :=
  coordinateFluxIntegrand_neg g r x

/-- Pointwise negation of coefficients negates the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_fun_neg :
    normalizedCoordinateFlux n (fun y i j => -g y i j) r =
      -normalizedCoordinateFlux n g r :=
  normalizedCoordinateFlux_neg g r

/-- Subtracting coefficients from a constant matrix negates the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_fun_const_sub :
    coordinateFluxIntegrand n (fun y i j => a i j - g y i j) r x =
      -coordinateFluxIntegrand n g r x := by
  simp only [sub_eq_add_neg, coordinateFluxIntegrand_fun_const_add,
    coordinateFluxIntegrand_fun_neg]

/-- Subtracting coefficients from a constant matrix negates the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_fun_const_sub :
    normalizedCoordinateFlux n (fun y i j => a i j - g y i j) r =
      -normalizedCoordinateFlux n g r := by
  simp only [sub_eq_add_neg, normalizedCoordinateFlux_fun_const_add,
    normalizedCoordinateFlux_fun_neg]

/-- Adding a constant coefficient field preserves the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_add_const :
    coordinateFluxIntegrand n (g + fun _ => a) r x = coordinateFluxIntegrand n g r x :=
  coordinateFluxIntegrand_fun_add_const g a r x

/-- Adding a constant coefficient field preserves the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_add_const :
    normalizedCoordinateFlux n (g + fun _ => a) r = normalizedCoordinateFlux n g r :=
  normalizedCoordinateFlux_fun_add_const g a r

/-- Adding coefficients to a constant field preserves the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_const_add :
    coordinateFluxIntegrand n ((fun _ => a) + g) r x = coordinateFluxIntegrand n g r x :=
  coordinateFluxIntegrand_fun_const_add g a r x

/-- Adding coefficients to a constant field preserves the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_const_add :
    normalizedCoordinateFlux n ((fun _ => a) + g) r = normalizedCoordinateFlux n g r :=
  normalizedCoordinateFlux_fun_const_add g a r

/-- Subtracting a constant coefficient field preserves the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_sub_const :
    coordinateFluxIntegrand n (g - fun _ => a) r x = coordinateFluxIntegrand n g r x :=
  coordinateFluxIntegrand_fun_sub_const g a r x

/-- Subtracting a constant coefficient field preserves the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_sub_const :
    normalizedCoordinateFlux n (g - fun _ => a) r = normalizedCoordinateFlux n g r :=
  normalizedCoordinateFlux_fun_sub_const g a r

/-- Subtracting coefficients from a constant field negates the flux density. -/
@[simp]
theorem coordinateFluxIntegrand_const_sub :
    coordinateFluxIntegrand n ((fun _ => a) - g) r x = -coordinateFluxIntegrand n g r x :=
  coordinateFluxIntegrand_fun_const_sub g a r x

/-- Subtracting coefficients from a constant field negates the normalized flux. -/
@[simp]
theorem normalizedCoordinateFlux_const_sub :
    normalizedCoordinateFlux n ((fun _ => a) - g) r = -normalizedCoordinateFlux n g r :=
  normalizedCoordinateFlux_fun_const_sub g a r

end Operations

/-- The flux density is subtractive on differentiable coefficients. -/
theorem coordinateFluxIntegrand_sub
    {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x) (r : ℝ) :
    coordinateFluxIntegrand n (g - h) r x =
      coordinateFluxIntegrand n g r x - coordinateFluxIntegrand n h r x := by
  simpa only [sub_eq_add_neg, coordinateFluxIntegrand_neg] using
    coordinateFluxIntegrand_add (g := g) (h := -h) hg
      (fun i j => by simpa only [Pi.neg_def] using (hh i j).neg) r

/-- The normalized flux is subtractive for differentiable coefficients with integrable
flux densities on the coordinate sphere. -/
theorem normalizedCoordinateFlux_sub
    {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hg : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x)
    (hgi : IntegrableOn (coordinateFluxIntegrand n g r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1)))
    (hhi : IntegrableOn (coordinateFluxIntegrand n h r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1))) :
    normalizedCoordinateFlux n (g - h) r =
      normalizedCoordinateFlux n g r - normalizedCoordinateFlux n h r := by
  have hni : IntegrableOn (coordinateFluxIntegrand n (-h) r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1)) := by
    have heq : coordinateFluxIntegrand n (-h) r = -coordinateFluxIntegrand n h r :=
      funext (fun x => coordinateFluxIntegrand_neg h r x)
    rw [heq]
    exact hhi.neg
  simpa only [sub_eq_add_neg, normalizedCoordinateFlux_neg] using
    normalizedCoordinateFlux_add (g := g) (h := -h) hg
      (fun x hx i j => by simpa only [Pi.neg_def] using (hh x hx i j).neg) hgi hni

section Pointwise

variable {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
  {x : EuclideanSpace ℝ (Fin n)} {r : ℝ}

/-- Pointwise addition of differentiable coefficients adds the flux densities. -/
theorem coordinateFluxIntegrand_fun_add
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x) :
    coordinateFluxIntegrand n (fun y i j => g y i j + h y i j) r x =
      coordinateFluxIntegrand n g r x + coordinateFluxIntegrand n h r x :=
  coordinateFluxIntegrand_add hg hh r

/-- Pointwise subtraction of differentiable coefficients subtracts the flux densities. -/
theorem coordinateFluxIntegrand_fun_sub
    (hg : ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x) :
    coordinateFluxIntegrand n (fun y i j => g y i j - h y i j) r x =
      coordinateFluxIntegrand n g r x - coordinateFluxIntegrand n h r x :=
  coordinateFluxIntegrand_sub hg hh r

/-- Pointwise addition adds normalized fluxes when the coefficients are differentiable and
their flux densities are integrable on the sphere. -/
theorem normalizedCoordinateFlux_fun_add
    (hg : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x)
    (hgi : IntegrableOn (coordinateFluxIntegrand n g r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1)))
    (hhi : IntegrableOn (coordinateFluxIntegrand n h r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1))) :
    normalizedCoordinateFlux n (fun y i j => g y i j + h y i j) r =
      normalizedCoordinateFlux n g r + normalizedCoordinateFlux n h r :=
  normalizedCoordinateFlux_add hg hh hgi hhi

/-- Pointwise subtraction subtracts normalized fluxes when the coefficients are differentiable
and their flux densities are integrable on the sphere. -/
theorem normalizedCoordinateFlux_fun_sub
    (hg : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => g y i j) x)
    (hh : ∀ x ∈ Metric.sphere 0 r, ∀ i j, DifferentiableAt ℝ (fun y => h y i j) x)
    (hgi : IntegrableOn (coordinateFluxIntegrand n g r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1)))
    (hhi : IntegrableOn (coordinateFluxIntegrand n h r) (Metric.sphere 0 r)
      (Measure.euclideanHausdorffMeasure (n - 1))) :
    normalizedCoordinateFlux n (fun y i j => g y i j - h y i j) r =
      normalizedCoordinateFlux n g r - normalizedCoordinateFlux n h r :=
  normalizedCoordinateFlux_sub hg hh hgi hhi

end Pointwise

/-- For the conformally Euclidean coefficient matrix `w δ`, the coordinate flux integrand is
`-(n - 1) dw_x(x) / r`. This identity does not require `w` to be radial or positive. -/
theorem coordinateFluxIntegrand_scalar
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

/-- For a radial conformally Euclidean matrix `f(‖x‖) δ`, the flux integrand on the coordinate
sphere of positive radius `r` is the constant `-(n - 1) f'(r)`. -/
theorem coordinateFluxIntegrand_scalar_radial {f : ℝ → ℝ} {f' r : ℝ}
    (hf : HasDerivAt f f' r) (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.sphere 0 r) :
    coordinateFluxIntegrand n (fun y i j => if i = j then f ‖y‖ else 0) r x =
      -((n : ℝ) - 1) * f' := by
  have hxr : ‖x‖ = r := by simpa using hx
  have hx0 : x ≠ 0 := by intro h; simp [h] at hxr; linarith
  have hn : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x :=
    (contDiffAt_id.norm ℝ hx0).differentiableAt one_ne_zero
  have hf' : HasDerivAt f f' ‖x‖ := hxr ▸ hf
  rw [coordinateFluxIntegrand_scalar,
    fderiv_fun_comp x hf'.differentiableAt hn, hf'.hasFDerivAt.fderiv,
    ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    hn.fderiv_norm_self, hxr]
  field_simp

/-- Radial scalar coefficients have an integrable flux density on every positive-radius sphere. -/
theorem integrableOn_coordinateFluxIntegrand_scalar_radial {f : ℝ → ℝ} {f' r : ℝ}
    (hf : HasDerivAt f f' r) (hr : 0 < r) :
    IntegrableOn (coordinateFluxIntegrand n (fun y i j => if i = j then f ‖y‖ else 0) r)
      (Metric.sphere 0 r) (Measure.euclideanHausdorffMeasure (n - 1)) :=
  integrableOn_coordinateFluxIntegrand_of_eqOn_const hr
    (fun _ hx => coordinateFluxIntegrand_scalar_radial hf hr hx)

/-- The normalized flux of a radial conformally Euclidean matrix in dimension at least two,
with the sphere areas and dimension factors cancelled. -/
theorem normalizedCoordinateFlux_scalar_radial {f : ℝ → ℝ} {f' r : ℝ}
    (hn : 2 ≤ n) (hf : HasDerivAt f f' r) (hr : 0 < r) :
    normalizedCoordinateFlux n (fun y i j => if i = j then f ‖y‖ else 0) r =
      -f' * r ^ (n - 1) / 2 := by
  rw [normalizedCoordinateFlux_of_eqOn_const (by omega) hr
    (fun x hx => coordinateFluxIntegrand_scalar_radial hf hr hx)]
  have hn' : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  field_simp [hn']

end TauCeti
