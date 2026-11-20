/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# The coordinate ADM mass functional

On a coordinate end `ℝⁿ \ B_R` with metric coefficients `g_ij`, the Arnowitt-Deser-Misner (ADM)
flux integrand through the Euclidean coordinate sphere `{x : ‖x‖ = r}` is
`Σ_j (Σ_i (∂_i g_ij - ∂_j g_ii)) (x_j / r)`, integrated against `(n - 1)`-dimensional Euclidean
Hausdorff measure and normalized by `2 (n - 1) |S^(n - 1)|` (Cecchini-Zeidler, equation (2.1);
Lee-Parker, Definition 8.2 uses the same flux integral normalized by `|S^(n - 1)|` alone). Because
both the coordinate sphere of radius `r` and the unit sphere in the denominator are measured with
the same Hausdorff measure `μHE[n - 1]`, any overall normalization of Hausdorff measure cancels in
`normalizedCoordinateFlux`.

When `g_ij = w δ_ij` is conformally flat, the integrand collapses without any differentiability
hypothesis to `-((n - 1) / r) Dw_x(x)`. For a radial conformal factor `w(y) = F(‖y‖)` with
`HasDerivAt F d r` at `r > 0`, the normalized flux at radius `r` (`2 ≤ n`) equals
`-(1 / 2) d r ^ (n - 1)`. This yields closed-form evaluations and `r → ∞` limits across the
standard test families:

* flat `ℝⁿ` has identically zero flux for `1 < r`, hence mass `0`;
* the model conformal family `(1 + c ‖x‖ ^ (2 - n)) ^ (4 / (n - 2)) δ_ij` (`3 ≤ n`) has mass `2 c`,
  and spatial Schwarzschild (`c = m / 2`) has mass `m`;
* the non-conformal radial perturbation `δ_ij + ε x_i x_j ‖x‖ ^ (-n)` (`2 ≤ n`) has constant
  normalized flux `ε / 2` at every `r > 0`, confirming sensitivity to off-diagonal derivatives;
* in dimension `3`, `(1 + (1 + ‖x‖ ^ 2) ^ (-3 / 8)) ^ 4 δ_ij` (decay order `t = 3 / 4 > 1 / 2` with
  non-integrable scalar curvature) has normalized flux diverging to `+∞`.

## Main definitions

* `TauCeti.coordinateFluxIntegrand`: the coordinate ADM flux integrand on `{x : ‖x‖ = r}`.
* `TauCeti.normalizedCoordinateFlux`: the sphere integral of `coordinateFluxIntegrand` divided by
  `2 (n - 1)` times the `(n - 1)`-Hausdorff area of the unit sphere.

## Main results

* `TauCeti.coordinateFluxIntegrand_conformal`,
  `TauCeti.normalizedCoordinateFlux_radial_conformal`: reduction of the ADM flux for general and
  radial conformally flat metrics.
* `TauCeti.tendsto_normalizedCoordinateFlux_conformal_rpow` and
  `TauCeti.tendsto_normalizedCoordinateFlux_schwarzschildCoeff`: limits `2 c` and `m` for the
  conformal `r ^ (2 - n)` family and spatial Schwarzschild (`3 ≤ n`).
* `TauCeti.normalizedCoordinateFlux_radialTensor`: exact value `ε / 2` for the non-conformal
  perturbation `δ_ij + ε x_i x_j ‖x‖ ^ (-n)`.
* `TauCeti.tendsto_normalizedCoordinateFlux_slowConformalThree_atTop`: divergence of the ADM flux
  in dimension `3` at decay order `3 / 4 > 1 / 2` without scalar-curvature integrability.

## References

* R. Arnowitt, S. Deser, and C. W. Misner, *Coordinate invariance and energy expressions in general
  relativity*, Phys. Rev. 122 (1961), 997-1006.
* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  661-693.
* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271-5288 (arXiv:2108.11972), Section 2
  (equation (2.1) and Example 2.2).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37-91,
  Sections 8 and 9.
-/

public section

noncomputable section

open Bundle Filter Function MeasureTheory Measure Metric Module Set
open scoped ContDiff ENNReal Manifold RealInnerProductSpace Topology

namespace TauCeti

/-! ### The coordinate ADM flux integrand and normalized sphere flux -/

/-- The integrand of the coordinate ADM flux through the Euclidean sphere of radius `r`: for
coefficients `g y i j` on `ℝⁿ` it is `Σ_j (Σ_i (∂_i g_ij - ∂_j g_ii)) (x_j / r)`, where `x / r` is
the outward Euclidean unit normal on `{x : ‖x‖ = r}`. -/
def coordinateFluxIntegrand (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, (∑ i, (
    fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
      fderiv ℝ (fun y => g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))) *
        (x j / r)

/-- Unfolding lemma for `TauCeti.coordinateFluxIntegrand`. -/
theorem coordinateFluxIntegrand_def (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n g r x =
      ∑ j, (∑ i, (
        fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))) *
            (x j / r) :=
  (rfl)

/-- The normalized coordinate ADM flux at radius `r`: the flux integral over the coordinate sphere
of radius `r` divided by `2 (n - 1)` times the `(n - 1)`-Hausdorff area of the unit sphere
(Cecchini-Zeidler, equation (2.1)). Both spheres use `μHE[n - 1]`, so the Hausdorff normalization
constant cancels. The ADM mass of an end is the limit of this quantity as `r → ∞`. -/
def normalizedCoordinateFlux (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) : ℝ :=
  (∫ x in Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      coordinateFluxIntegrand n g r x
      ∂(Measure.euclideanHausdorffMeasure (n - 1))) /
    (2 * ((n : ℝ) - 1) *
      ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (EuclideanSpace ℝ (Fin n)))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)

/-- Unfolding lemma for `TauCeti.normalizedCoordinateFlux`. -/
theorem normalizedCoordinateFlux_def (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) :
    normalizedCoordinateFlux n g r =
      (∫ x in Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r,
          coordinateFluxIntegrand n g r x
          ∂(Measure.euclideanHausdorffMeasure (n - 1))) /
        (2 * ((n : ℝ) - 1) *
          ((Measure.euclideanHausdorffMeasure (n - 1) : Measure (EuclideanSpace ℝ (Fin n)))
            (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) :=
  (rfl)

/-- Rewriting `normalizedCoordinateFlux` in terms of `TauCeti.roundSphereVolume (n - 1)`. -/
theorem normalizedCoordinateFlux_eq_div_roundSphereVolume {n : ℕ} (hn : 1 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n g r =
      (∫ x in sphere (0 : EuclideanSpace ℝ (Fin n)) r,
          coordinateFluxIntegrand n g r x ∂μHE[n - 1]) /
        (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) := by
  rw [normalizedCoordinateFlux_def, toReal_euclideanHausdorffMeasure_unitSphere hn]

/-- When `coordinateFluxIntegrand n g r` takes a constant value `C` on `sphere 0 r` (`1 ≤ n`,
`0 < r`), the unit-sphere area `roundSphereVolume (n - 1)` cancels out of
`normalizedCoordinateFlux`. -/
theorem normalizedCoordinateFlux_eq_of_forall_mem_sphere_eq {n : ℕ} (hn : 1 ≤ n)
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r C : ℝ} (hr : 0 < r)
    (hC : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r, coordinateFluxIntegrand n g r x = C) :
    normalizedCoordinateFlux n g r = r ^ (n - 1) * C / (2 * ((n : ℝ) - 1)) := by
  have hvol : roundSphereVolume (n - 1) ≠ 0 := (roundSphereVolume_pos (n - 1)).ne'
  rw [normalizedCoordinateFlux_eq_div_roundSphereVolume hn,
    setIntegral_congr_fun isClosed_sphere.measurableSet hC,
    setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one (n - 1) 0 hr (fun _ ↦ C),
    setIntegral_const, Measure.real, toReal_euclideanHausdorffMeasure_unitSphere hn,
    smul_eq_mul, smul_eq_mul]
  calc (r ^ (n - 1) * (roundSphereVolume (n - 1) * C)) /
        (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1))
      = (roundSphereVolume (n - 1) * (r ^ (n - 1) * C)) /
          (roundSphereVolume (n - 1) * (2 * ((n : ℝ) - 1))) := by ring
    _ = r ^ (n - 1) * C / (2 * ((n : ℝ) - 1)) :=
        mul_div_mul_left _ _ hvol

/-! ### Germ locality and algebraic properties -/

/-- `coordinateFluxIntegrand` depends only on the germ of the coefficient matrix `g` at `x`. -/
theorem coordinateFluxIntegrand_congr_nhds {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (h : ∀ i j, (fun y ↦ g₁ y i j) =ᶠ[𝓝 x] (fun y ↦ g₂ y i j)) :
    coordinateFluxIntegrand n g₁ r x = coordinateFluxIntegrand n g₂ r x := by
  simp only [coordinateFluxIntegrand_def]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg (· * (x j / r)) <|
    Finset.sum_congr rfl fun i _ ↦ ?_
  rw [(h i j).fderiv_eq, (h i i).fderiv_eq]

/-- If `g₁` and `g₂` have the same germ at every point of `sphere 0 r`, then their normalized
coordinate fluxes at radius `r` agree. -/
theorem normalizedCoordinateFlux_congr_nhds {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (h : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, (fun y ↦ g₁ y i j) =ᶠ[𝓝 x] (fun y ↦ g₂ y i j)) :
    normalizedCoordinateFlux n g₁ r = normalizedCoordinateFlux n g₂ r := by
  rw [normalizedCoordinateFlux_def, normalizedCoordinateFlux_def]
  congr 1
  exact setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx ↦
    coordinateFluxIntegrand_congr_nhds (h x hx)

/-- If `g₁` and `g₂` agree on an open exterior `{x | R < ‖x‖}`, then their normalized coordinate
fluxes agree at every radius `r > R`. -/
theorem normalizedCoordinateFlux_congr_exterior {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {R r : ℝ} (hRr : R < r)
    (h : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j, g₁ x i j = g₂ x i j) :
    normalizedCoordinateFlux n g₁ r = normalizedCoordinateFlux n g₂ r := by
  have hU : IsOpen {x : EuclideanSpace ℝ (Fin n) | R < ‖x‖} :=
    isOpen_lt continuous_const continuous_norm
  refine normalizedCoordinateFlux_congr_nhds fun x hx i j ↦ ?_
  have hxU : x ∈ {y : EuclideanSpace ℝ (Fin n) | R < ‖y‖} := by
    simp only [mem_ofPred_eq]
    rwa [mem_sphere_zero_iff_norm.1 hx]
  exact Filter.eventuallyEq_of_mem (hU.mem_nhds hxU) fun y hy ↦ h y hy i j

/-- Two metric-coefficient families agreeing outside a ball have the same ADM mass limit behavior as
`r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_iff_of_eqOn_exterior {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {R : ℝ}
    (h : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ → ∀ i j, g₁ x i j = g₂ x i j)
    {l : Filter ℝ} :
    Tendsto (normalizedCoordinateFlux n g₁) atTop l ↔
      Tendsto (normalizedCoordinateFlux n g₂) atTop l :=
  tendsto_congr' <| (eventually_gt_atTop R).mono fun _ hr ↦
    normalizedCoordinateFlux_congr_exterior hr h

/-- A spatially constant coefficient matrix has zero coordinate ADM flux integrand everywhere. -/
@[simp]
theorem coordinateFluxIntegrand_const {n : ℕ} (g₀ : Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun _ ↦ g₀) r x = 0 := by
  simp [coordinateFluxIntegrand_def]

/-- A spatially constant coefficient matrix has zero normalized coordinate flux at every radius. -/
@[simp]
theorem normalizedCoordinateFlux_const {n : ℕ} (g₀ : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun _ ↦ g₀) r = 0 := by
  simp [normalizedCoordinateFlux_def]

/-- Scaling the metric coefficients by any real scalar `c` scales `coordinateFluxIntegrand` by `c`,
without any differentiability hypothesis. -/
theorem coordinateFluxIntegrand_const_mul {n : ℕ} (c : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j ↦ c * g y i j) r x =
      c * coordinateFluxIntegrand n g r x := by
  simp only [coordinateFluxIntegrand_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hsum : ∑ i, (fderiv ℝ (fun y ↦ c * g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
      fderiv ℝ (fun y ↦ c * g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      c * ∑ i, (fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
        fderiv ℝ (fun y ↦ g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h1 : (fun y ↦ c * g y i j) = c • fun y ↦ g y i j := rfl
    have h2 : (fun y ↦ c * g y i i) = c • fun y ↦ g y i i := rfl
    rw [h1, h2, fderiv_const_smul_field, fderiv_const_smul_field, Pi.smul_apply, Pi.smul_apply,
      smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [hsum]
  ring

/-- Scaling the metric coefficients by `c` scales `normalizedCoordinateFlux` by `c`. -/
theorem normalizedCoordinateFlux_const_mul {n : ℕ} (c : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j ↦ c * g y i j) r =
      c * normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_const_mul, integral_const_mul,
    mul_div_assoc]

/-- Adding a constant matrix `g₀` on the right leaves `coordinateFluxIntegrand` unchanged. -/
@[simp]
theorem coordinateFluxIntegrand_add_const {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (g₀ : Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j ↦ g y i j + g₀ i j) r x =
      coordinateFluxIntegrand n g r x := by
  simp only [coordinateFluxIntegrand_def, fderiv_add_const]

/-- Adding a constant matrix `g₀` on the left leaves `coordinateFluxIntegrand` unchanged. -/
@[simp]
theorem coordinateFluxIntegrand_const_add {n : ℕ} (g₀ : Fin n → Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j ↦ g₀ i j + g y i j) r x =
      coordinateFluxIntegrand n g r x := by
  simp_rw [add_comm (g₀ _ _)]; exact coordinateFluxIntegrand_add_const g g₀ r x

/-- Adding a constant matrix `g₀` on the right leaves `normalizedCoordinateFlux` unchanged. -/
@[simp]
theorem normalizedCoordinateFlux_add_const {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (g₀ : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j ↦ g y i j + g₀ i j) r =
      normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_add_const]

/-- Adding a constant matrix `g₀` on the left leaves `normalizedCoordinateFlux` unchanged. -/
@[simp]
theorem normalizedCoordinateFlux_const_add {n : ℕ} (g₀ : Fin n → Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j ↦ g₀ i j + g y i j) r =
      normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_const_add]

/-- **Flat Euclidean check.** On flat `ℝⁿ` in the standard end
`AsymptoticallyEuclideanEnd.euclidean`, the normalized coordinate flux vanishes identically at
every radius `r > 1`. -/
theorem normalizedCoordinateFlux_euclidean_eq_zero {n : ℕ} (t : ℝ) {r : ℝ} (hr : 1 < r) :
    normalizedCoordinateFlux n
      (pullbackMetricCoeff (AsymptoticallyEuclideanEnd.euclidean n t).toFun) r = 0 := by
  rw [normalizedCoordinateFlux_congr_exterior hr fun _ hx i j ↦
    AsymptoticallyEuclideanEnd.euclidean_pullbackMetricCoeff_of_lt t hx i j]
  exact normalizedCoordinateFlux_const _ r

/-- **Flat Euclidean mass check.** Flat `ℝⁿ` has ADM mass `0`. -/
theorem tendsto_normalizedCoordinateFlux_euclidean (n : ℕ) (t : ℝ) :
    Tendsto
      (normalizedCoordinateFlux n
        (pullbackMetricCoeff (AsymptoticallyEuclideanEnd.euclidean n t).toFun))
      atTop (𝓝 0) :=
  tendsto_const_nhds.congr' <| (eventually_gt_atTop 1).mono fun _ hr ↦
    (normalizedCoordinateFlux_euclidean_eq_zero t hr).symm

/-! ### Reduction of the ADM flux for conformally flat and radial metrics -/

/-- For any conformally flat coefficient matrix `g y i j = w y * δ_ij`, the coordinate ADM flux
integrand reduces to `-((n - 1) / r) * fderiv ℝ w x x`, with no differentiability assumption on
`w`. -/
theorem coordinateFluxIntegrand_conformal {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j ↦ w y * if i = j then 1 else 0) r x =
      -(((n : ℝ) - 1) / r) * fderiv ℝ w x x := by
  rw [coordinateFluxIntegrand_def]
  have hinner : ∀ j : Fin n,
      ∑ i : Fin n, (fderiv ℝ (fun y ↦ w y * if i = j then 1 else 0) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) -
        fderiv ℝ (fun y ↦ w y * if i = i then 1 else 0) x
          (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      -((n : ℝ) - 1) * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    intro j
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ i : Fin n, fderiv ℝ (fun y ↦ w y * if i = j then 1 else 0) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij; simp [hij]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    have h2 : ∑ i : Fin n, fderiv ℝ (fun y ↦ w y * if i = i then 1 else 0) x
        (EuclideanSpace.basisFun (Fin n) ℝ j) =
        (n : ℝ) * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) := by simp
    rw [h1, h2]; ring
  have hsum : ∑ j : Fin n, x j * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) =
      fderiv ℝ w x x := by
    have hx : ∑ j : Fin n, x j • EuclideanSpace.basisFun (Fin n) ℝ j = x := by
      simpa [EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x
    calc ∑ j : Fin n, x j * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)
        = ∑ j : Fin n, fderiv ℝ w x (x j • EuclideanSpace.basisFun (Fin n) ℝ j) :=
            Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul]
      _ = fderiv ℝ w x (∑ j : Fin n, x j • EuclideanSpace.basisFun (Fin n) ℝ j) :=
            (map_sum (fderiv ℝ w x) _ _).symm
      _ = fderiv ℝ w x x := congrArg (fderiv ℝ w x) hx
  calc ∑ j : Fin n, _
      = ∑ j : Fin n, (-((n : ℝ) - 1) * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) *
          (x j / r) := Finset.sum_congr rfl fun j _ ↦ by rw [hinner j]
    _ = -(((n : ℝ) - 1) / r) *
          ∑ j : Fin n, x j * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = -(((n : ℝ) - 1) / r) * fderiv ℝ w x x := by rw [hsum]

/-- For a radial conformal factor `w y = F ‖y‖` with `HasDerivAt F d r` (`0 < r`), the coordinate
ADM flux integrand is constant equal to `-((n - 1) * d)` on the sphere of radius `r`. -/
theorem coordinateFluxIntegrand_radial_conformal {n : ℕ} {F : ℝ → ℝ} {d r : ℝ} (hr : 0 < r)
    (hF : HasDerivAt F d r) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r) :
    coordinateFluxIntegrand n (fun y i j ↦ F ‖y‖ * if i = j then 1 else 0) r x =
      -((n : ℝ) - 1) * d := by
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.1 hx
  have hx0 : x ≠ 0 := norm_pos_iff.1 (hnorm.symm ▸ hr)
  have hd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) ↦ F ‖y‖)
      (d • (‖x‖⁻¹ • innerSL ℝ x)) x := by
    have hF' : HasDerivAt F d ‖x‖ := hnorm.symm ▸ hF
    exact hF'.comp_hasFDerivAt x (hasFDerivAt_norm_of_ne hx0)
  rw [coordinateFluxIntegrand_conformal, hd.fderiv]
  simp only [smul_apply, coe_innerSL_apply, smul_eq_mul, real_inner_self_eq_norm_sq, hnorm]
  field_simp [hr.ne']

/-- **Radial conformal ADM flux formula.** If `2 ≤ n`, `0 < r`, and `HasDerivAt F d r`, then the
normalized coordinate flux of `F ‖y‖ * δ_ij` at radius `r` equals `-(1 / 2) * d * r ^ (n - 1)`. -/
theorem normalizedCoordinateFlux_radial_conformal {n : ℕ} (hn : 2 ≤ n) {F : ℝ → ℝ} {d r : ℝ}
    (hr : 0 < r) (hF : HasDerivAt F d r) :
    normalizedCoordinateFlux n (fun y i j ↦ F ‖y‖ * if i = j then 1 else 0) r =
      -(1 / 2) * d * r ^ (n - 1) := by
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := Nat.ofNat_le_cast.2 hn
    linarith
  rw [normalizedCoordinateFlux_eq_of_forall_mem_sphere_eq (by omega) hr fun x hx ↦
    coordinateFluxIntegrand_radial_conformal hr hF hx]
  field_simp [hn1]

/-! ### Explicit ADM mass checks on conformal and non-conformal test families -/

/-- Exact normalized coordinate flux at radius `r > 0` for the conformal model
`g_ij(y) = (1 + c ‖y‖ ^ (2 - n)) ^ (4 / (n - 2)) δ_ij` in dimension `3 ≤ n`, at any radius where
`1 + c r ^ (2 - n) > 0`. -/
theorem normalizedCoordinateFlux_conformal_rpow {n : ℕ} (hn : 3 ≤ n) {c r : ℝ} (hr : 0 < r)
    (hpos : 0 < 1 + c * r ^ (2 - (n : ℝ))) :
    normalizedCoordinateFlux n
        (fun y i j ↦
          (1 + c * ‖y‖ ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2)) * if i = j then 1 else 0) r =
      2 * c * (1 + c * r ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2) - 1) := by
  have hn2 : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := Nat.ofNat_le_cast.2 hn
    linarith
  have hd_in : HasDerivAt (fun s : ℝ ↦ 1 + c * s ^ (2 - (n : ℝ)))
      (c * ((2 - (n : ℝ)) * r ^ (1 - (n : ℝ)))) r := by
    have hexp : (2 : ℝ) - n - 1 = 1 - n := by ring
    have hrp := (Real.hasDerivAt_rpow_const (x := r) (p := 2 - (n : ℝ)) (Or.inl hr.ne')).const_mul c
    exact (hrp.const_add 1).congr_deriv (by rw [hexp])
  have hd := hd_in.rpow_const (p := 4 / ((n : ℝ) - 2)) (Or.inl hpos.ne')
  rw [normalizedCoordinateFlux_radial_conformal (by omega) hr hd]
  have hrpow : r ^ (1 - (n : ℝ)) * r ^ (n - 1) = 1 := by
    have hn_le : 1 ≤ n := by omega
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn_le, Nat.cast_one]
    rw [← Real.rpow_natCast, hn1, ← Real.rpow_add hr]
    simp
  have hcancel : -(1 / 2) * ((4 / ((n : ℝ) - 2)) * (2 - (n : ℝ))) = 2 := by
    field_simp [hn2]
    ring
  calc -(1 / 2) * (c * ((2 - (n : ℝ)) * r ^ (1 - (n : ℝ))) * (4 / ((n : ℝ) - 2)) *
          (1 + c * r ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2) - 1)) * r ^ (n - 1)
      = (-(1 / 2) * ((4 / ((n : ℝ) - 2)) * (2 - (n : ℝ)))) * c *
          (1 + c * r ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2) - 1) *
          (r ^ (1 - (n : ℝ)) * r ^ (n - 1)) := by ring
    _ = 2 * c * (1 + c * r ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2) - 1) := by
          rw [hcancel, hrpow, mul_one]

/-- **Conformal `r ^ (2 - n)` check.** In dimension `3 ≤ n`, for every `c : ℝ` (positive, zero, or
negative), the coordinate ADM flux of `(1 + c ‖y‖ ^ (2 - n)) ^ (4 / (n - 2)) δ_ij` converges to
`2 c` as `r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_conformal_rpow {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    Tendsto
      (normalizedCoordinateFlux n
        (fun y i j ↦
          (1 + c * ‖y‖ ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2)) * if i = j then 1 else 0))
      atTop (𝓝 (2 * c)) := by
  have hneg : 0 < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := Nat.ofNat_le_cast.2 hn
    linarith
  have hu : Tendsto (fun r : ℝ ↦ 1 + c * r ^ (2 - (n : ℝ))) atTop (𝓝 1) := by
    have hexp : -((n : ℝ) - 2) = 2 - (n : ℝ) := by ring
    have hrp : Tendsto (fun r : ℝ ↦ r ^ (2 - (n : ℝ))) atTop (𝓝 0) :=
      hexp ▸ tendsto_rpow_neg_atTop hneg
    simpa using tendsto_const_nhds.add (hrp.const_mul c)
  have hlim : Tendsto
      (fun r : ℝ ↦ 2 * c * (1 + c * r ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2) - 1))
      atTop (𝓝 (2 * c)) := by
    have hrpow : ContinuousAt (fun z : ℝ ↦ z ^ (4 / ((n : ℝ) - 2) - 1)) 1 :=
      Real.continuousAt_rpow_const _ _ (Or.inl one_ne_zero)
    simpa using (hrpow.tendsto.comp hu).const_mul (2 * c)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hu.eventually (Ioi_mem_nhds zero_lt_one)] with r
    hr hp
  exact (normalizedCoordinateFlux_conformal_rpow hn hr hp).symm

/-- **Spatial Schwarzschild check** (Cecchini-Zeidler, Example 2.2). In dimension `3 ≤ n`, for
every mass parameter `m : ℝ`, the spatial Schwarzschild metric coefficients
`(1 + m / (2 ‖y‖ ^ (n - 2))) ^ (4 / (n - 2)) δ_ij` have ADM mass `m`. -/
theorem tendsto_normalizedCoordinateFlux_schwarzschildCoeff {n : ℕ} (hn : 3 ≤ n) (m : ℝ) :
    Tendsto
      (normalizedCoordinateFlux n
        (fun y i j ↦
          (1 + m / (2 * ‖y‖ ^ ((n : ℝ) - 2))) ^ (4 / ((n : ℝ) - 2)) * if i = j then 1 else 0))
      atTop (𝓝 m) := by
  have heq : ∀ y : EuclideanSpace ℝ (Fin n), 0 < ‖y‖ → ∀ i j : Fin n,
      (1 + m / (2 * ‖y‖ ^ ((n : ℝ) - 2))) ^ (4 / ((n : ℝ) - 2)) *
          (if i = j then (1 : ℝ) else 0) =
        (1 + (m / 2) * ‖y‖ ^ (2 - (n : ℝ))) ^ (4 / ((n : ℝ) - 2)) *
          (if i = j then (1 : ℝ) else 0) := by
    intro y hy i j
    have hexp : (2 : ℝ) - n = -((n : ℝ) - 2) := by ring
    have hbase : 1 + m / (2 * ‖y‖ ^ ((n : ℝ) - 2)) = 1 + (m / 2) * ‖y‖ ^ (2 - (n : ℝ)) := by
      rw [hexp, Real.rpow_neg hy.le]
      ring
    rw [hbase]
  have hm : (2 : ℝ) * (m / 2) = m := by ring
  have hlim := tendsto_normalizedCoordinateFlux_conformal_rpow hn (m / 2)
  rw [hm] at hlim
  exact (tendsto_normalizedCoordinateFlux_iff_of_eqOn_exterior heq).2 hlim

private theorem sum_fderiv_radialTensor_basis {n : ℕ} {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hnorm : ‖x‖ = r) (j : Fin n) :
    ∑ i : Fin n, (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y i * y j * ‖y‖ ^ (-(n : ℝ))) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) -
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y i * y i * ‖y‖ ^ (-(n : ℝ))) x
        (EuclideanSpace.basisFun (Fin n) ℝ j)) =
      ((n : ℝ) - 1) * x j * r ^ (-(n : ℝ)) := by
  have hx0 : x ≠ 0 := norm_pos_iff.1 (hnorm.symm ▸ hr)
  have hcoord (k : Fin n) : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) ↦ y k)
      (EuclideanSpace.proj (𝕜 := ℝ) k) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.congr_of_eventuallyEq <|
      Eventually.of_forall fun _ ↦ by simp only [PiLp.proj_apply]
  have hd (a b : Fin n) :=
    ((hcoord a).fun_mul (hcoord b)).fun_mul (hasFDerivAt_norm_rpow_of_ne (-(n : ℝ)) hx0)
  have hterm : ∀ i : Fin n,
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y i * y j * ‖y‖ ^ (-(n : ℝ))) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) -
        fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ y i * y i * ‖y‖ ^ (-(n : ℝ))) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
      r ^ (-(n : ℝ)) * (x j - x i * if i = j then 1 else 0) := by
    intro i
    rw [(hd i j).fderiv, (hd i i).fderiv]
    simp only [add_apply, smul_apply, coe_innerSL_apply, smul_eq_mul, PiLp.proj_apply,
      EuclideanSpace.inner_basisFun_real, hnorm]
    simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, ↓reduceIte, @eq_comm _ j i]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

private theorem coordinateFluxIntegrand_radialTensor_sphere {n : ℕ} (ε : ℝ) {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r) :
    coordinateFluxIntegrand n
        (fun y i j ↦ (if i = j then 1 else 0) + ε * y i * y j * ‖y‖ ^ (-(n : ℝ))) r x =
      ε * ((n : ℝ) - 1) * r ^ (1 - (n : ℝ)) := by
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.1 hx
  have hsq : ∑ k : Fin n, x k ^ 2 = r ^ 2 := by
    rw [← hnorm, EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  have hmul : (fun (y : EuclideanSpace ℝ (Fin n)) (i j : Fin n) ↦
      ε * y i * y j * ‖y‖ ^ (-(n : ℝ))) =
      fun y i j ↦ ε * (y i * y j * ‖y‖ ^ (-(n : ℝ))) := by
    ext y i j; ring
  have hr1 : r ^ (-(n : ℝ)) * (r ^ 2 / r) = r ^ (1 - (n : ℝ)) := by
    have hdiv : r ^ 2 / r = r ^ (1 : ℝ) := by rw [Real.rpow_one]; field_simp [hr.ne']
    rw [hdiv, ← Real.rpow_add hr]; congr 1; ring
  rw [coordinateFluxIntegrand_const_add, hmul, coordinateFluxIntegrand_const_mul,
    coordinateFluxIntegrand_def]
  calc ε * ∑ j : Fin n, _
      = ε * ∑ j : Fin n, (((n : ℝ) - 1) * x j * r ^ (-(n : ℝ))) * (x j / r) := by
          congr 1; exact Finset.sum_congr rfl fun j _ ↦ by
            rw [sum_fderiv_radialTensor_basis hr hnorm j]
    _ = ε * ((n : ℝ) - 1) * (r ^ (-(n : ℝ)) * ((∑ j : Fin n, x j ^ 2) / r)) := by
          rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ε * ((n : ℝ) - 1) * r ^ (1 - (n : ℝ)) := by rw [hsq, hr1]

/-- **Non-conformal radial tensor check.** In dimension `2 ≤ n`, the perturbation
`g_ij(y) = δ_ij + ε y_i y_j ‖y‖ ^ (-n)` has constant normalized coordinate flux `ε / 2` at every
radius `r > 0`. -/
theorem normalizedCoordinateFlux_radialTensor {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) {r : ℝ} (hr : 0 < r) :
    normalizedCoordinateFlux n
        (fun y i j ↦ (if i = j then 1 else 0) + ε * y i * y j * ‖y‖ ^ (-(n : ℝ))) r =
      ε / 2 := by
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ n := Nat.ofNat_le_cast.2 hn
    linarith
  have hrpow : r ^ (n - 1) * r ^ (1 - (n : ℝ)) = 1 := by
    have hn_le : 1 ≤ n := by omega
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn_le, Nat.cast_one]
    rw [← Real.rpow_natCast, hcast, ← Real.rpow_add hr]
    simp
  rw [normalizedCoordinateFlux_eq_of_forall_mem_sphere_eq (by omega) hr fun x hx ↦
    coordinateFluxIntegrand_radialTensor_sphere ε hr hx]
  calc r ^ (n - 1) * (ε * ((n : ℝ) - 1) * r ^ (1 - (n : ℝ))) / (2 * ((n : ℝ) - 1))
      = ε * ((n : ℝ) - 1) * (r ^ (n - 1) * r ^ (1 - (n : ℝ))) / (2 * ((n : ℝ) - 1)) := by ring
    _ = ε / 2 := by rw [hrpow, mul_one]; field_simp [hn1]

/-- Consequently, `δ_ij + ε y_i y_j ‖y‖ ^ (-n)` (`2 ≤ n`) has ADM mass `ε / 2`. -/
theorem tendsto_normalizedCoordinateFlux_radialTensor {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) :
    Tendsto
      (normalizedCoordinateFlux n
        (fun y i j ↦ (if i = j then 1 else 0) + ε * y i * y j * ‖y‖ ^ (-(n : ℝ))))
      atTop (𝓝 (ε / 2)) :=
  tendsto_const_nhds.congr' <| (eventually_gt_atTop 0).mono fun _ hr ↦
    (normalizedCoordinateFlux_radialTensor hn ε hr).symm

/-- Exact normalized coordinate flux in dimension `3` for the slow conformal decay model
`g_ij(y) = (1 + (1 + ‖y‖ ^ 2) ^ (-3 / 8)) ^ 4 δ_ij` (order `t = 3 / 4 > 1 / 2`, scalar curvature
`O(r ^ (-11 / 4))` not integrable on `ℝ³`). -/
theorem normalizedCoordinateFlux_slowConformalThree {r : ℝ} (hr : 0 < r) :
    normalizedCoordinateFlux 3
        (fun y i j ↦ (1 + (1 + ‖y‖ ^ 2) ^ (-3 / 8 : ℝ)) ^ 4 * if i = j then 1 else 0) r =
      (3 / 2 : ℝ) * (1 + (1 + r ^ 2) ^ (-3 / 8 : ℝ)) ^ 3 * r ^ 3 *
        (1 + r ^ 2) ^ (-11 / 8 : ℝ) := by
  have h1r : 0 < 1 + r ^ 2 := by positivity
  have hexp : (-3 / 8 : ℝ) - 1 = -11 / 8 := by norm_num
  have hd_sq : HasDerivAt (fun s : ℝ ↦ 1 + s ^ 2) (2 * r) r :=
    ((hasDerivAt_pow 2 r).const_add 1).congr_deriv (by ring)
  have hd_rpow : HasDerivAt (fun s : ℝ ↦ (1 + s ^ 2) ^ (-3 / 8 : ℝ))
      ((-3 / 8 : ℝ) * (1 + r ^ 2) ^ (-11 / 8 : ℝ) * (2 * r)) r :=
    (hd_sq.rpow_const (p := -3 / 8) (Or.inl h1r.ne')).congr_deriv (by rw [hexp]; ring)
  have hd : HasDerivAt (fun s : ℝ ↦ (1 + (1 + s ^ 2) ^ (-3 / 8 : ℝ)) ^ 4)
      ((4 : ℝ) * (1 + (1 + r ^ 2) ^ (-3 / 8 : ℝ)) ^ 3 *
        ((-3 / 8 : ℝ) * (1 + r ^ 2) ^ (-11 / 8 : ℝ) * (2 * r))) r := by
    have hpow := (hd_rpow.const_add 1).pow 4
    exact hpow.congr_deriv (by norm_num)
  rw [normalizedCoordinateFlux_radial_conformal (by omega) hr hd]
  ring

/-- **Divergent flux check without integrable scalar curvature.** For
`g_ij(y) = (1 + (1 + ‖y‖ ^ 2) ^ (-3 / 8)) ^ 4 δ_ij` on `ℝ³`, the normalized coordinate flux diverges
to `+∞` as `r → ∞`, showing that `t > (n - 2) / 2` alone does not make the ADM mass finite. -/
theorem tendsto_normalizedCoordinateFlux_slowConformalThree_atTop :
    Tendsto
      (normalizedCoordinateFlux 3
        (fun y i j ↦ (1 + (1 + ‖y‖ ^ 2) ^ (-3 / 8 : ℝ)) ^ 4 * if i = j then 1 else 0))
      atTop atTop := by
  let c₀ : ℝ := (3 / 2) * (2 : ℝ) ^ (-11 / 8 : ℝ)
  have hc₀ : 0 < c₀ := by positivity
  have hdiv : Tendsto (fun r : ℝ ↦ c₀ * r ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).const_mul_atTop' hc₀
  refine tendsto_atTop_mono' atTop ?_ hdiv
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  rw [normalizedCoordinateFlux_slowConformalThree hr0]
  have hcube : 1 ≤ (1 + (1 + r ^ 2) ^ (-3 / 8 : ℝ)) ^ 3 := by
    have hbase : 1 ≤ 1 + (1 + r ^ 2) ^ (-3 / 8 : ℝ) :=
      le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    nlinarith [sq_nonneg (1 + (1 + r ^ 2) ^ (-3 / 8 : ℝ))]
  have hrpow : (2 : ℝ) ^ (-11 / 8 : ℝ) * r ^ (-11 / 4 : ℝ) ≤ (1 + r ^ 2) ^ (-11 / 8 : ℝ) := by
    have hle : 1 + r ^ 2 ≤ 2 * r ^ 2 := by nlinarith
    have hanti := Real.rpow_le_rpow_of_nonpos (z := -11 / 8)
      (by positivity : 0 < 1 + r ^ 2) hle (by norm_num)
    have hmul : (2 * r ^ 2) ^ (-11 / 8 : ℝ) = (2 : ℝ) ^ (-11 / 8 : ℝ) * r ^ (-11 / 4 : ℝ) := by
      rw [Real.mul_rpow zero_le_two (sq_nonneg r), ← Real.rpow_natCast r 2,
        ← Real.rpow_mul hr0.le]
      norm_num
    exact hmul ▸ hanti
  have hexp : r ^ 3 * r ^ (-11 / 4 : ℝ) = r ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast r 3, ← Real.rpow_add hr0]
    norm_num
  calc c₀ * r ^ (1 / 4 : ℝ)
      = (3 / 2 : ℝ) * 1 * r ^ 3 * ((2 : ℝ) ^ (-11 / 8 : ℝ) * r ^ (-11 / 4 : ℝ)) := by
          simp only [c₀, ← hexp]; ring
    _ ≤ (3 / 2 : ℝ) * (1 + (1 + r ^ 2) ^ (-3 / 8 : ℝ)) ^ 3 * r ^ 3 *
          (1 + r ^ 2) ^ (-11 / 8 : ℝ) := by
          have h1 := mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ (3 / 2 : ℝ))
          have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hr0.le 3)
          exact mul_le_mul h2 hrpow (by positivity) (by positivity)

end TauCeti
