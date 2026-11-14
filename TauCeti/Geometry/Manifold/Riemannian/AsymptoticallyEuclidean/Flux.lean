/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic

import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# Coordinate ADM flux and model mass computations

For coordinate metric coefficients `g : ℝⁿ → Fin n → Fin n → ℝ`, the *coordinate ADM flux
integrand* at radius `r` is

`Σ_j (Σ_i (∂_i g_ij - ∂_j g_ii)) x_j / r`,

and the *normalized coordinate ADM flux* `normalizedCoordinateFlux n g r` integrates this density
over the Euclidean sphere `sphere 0 r` against normalized `(n - 1)`-dimensional Hausdorff measure
`μHE[n - 1]`, divided by `2 (n - 1)` times the `μHE[n - 1]`-area of the unit sphere
(Cecchini–Zeidler, equation (2.1)). Because the same Hausdorff measure appears in numerator and
denominator, any overall normalization constant cancels; in this normalization the conformally
flat harmonic model `(1 + c r ^ (2 - n)) ^ (4 / (n - 2)) δ` has asymptotic limit `2 c`, and the
spatial Schwarzschild metric `(1 + m / (2 r ^ (n - 2))) ^ (4 / (n - 2)) δ` has asymptotic limit
`m`.

On an `AsymptoticallyEuclideanEnd`, `normalizedCoordinateFlux` applied to `E.metricCoeff` agrees
at every radius `r > E.radius` with `normalizedCoordinateFlux` applied to `pullbackMetricCoeff φ`
for any ambient extension `φ : ℝⁿ → M` of `E.param`, and is invariant under `E.restrictRadius`.

## Main definitions

* `TauCeti.coordinateFluxIntegrand`: the coordinate ADM flux density on `sphere 0 r`.
* `TauCeti.normalizedCoordinateFlux`: the normalized coordinate ADM flux at radius `r`, whose
  `r → ∞` limit is the ADM mass of an asymptotically Euclidean end.
* `TauCeti.conformalFlatMetricCoeff`: conformally flat metric coefficients `w(x) δ_ij`.
* `TauCeti.harmonicConformalCoeff`, `TauCeti.schwarzschildMetricCoeff`, and
  `TauCeti.radialTensorPerturbCoeff`: the harmonic-conformal, spatial Schwarzschild, and
  non-conformal radial tensor model metrics on `ℝⁿ`.

## Main results

* `TauCeti.AsymptoticallyEuclideanEnd.normalizedCoordinateFlux_metricCoeff_eq` and
  `tendsto_normalizedCoordinateFlux_metricCoeff_iff`: agreement of `E.metricCoeff` flux with any
  ambient extension `pullbackMetricCoeff φ` for `r > E.radius`.
* `TauCeti.AsymptoticallyEuclideanEnd.exists_abs_normalizedCoordinateFlux_le` and
  `tendsto_normalizedCoordinateFlux_zero_of_sub_lt`: `O(r ^ (n - 2 - t))` flux bound on an AE end
  of order `t`, and vanishing ADM mass for faster-than-Newtonian decay `t > n - 2`.
* `TauCeti.normalizedCoordinateFlux_const_add`, `normalizedCoordinateFlux_const_smul`, and
  `normalizedCoordinateFlux_add`: invariance under constant metric shifts and linearity of the
  coordinate ADM flux.
* `TauCeti.coordinateFluxIntegrand_conformalFlat` and
  `TauCeti.normalizedCoordinateFlux_conformalFlat_radial`: closed-form flux formulas for general
  and radial conformally flat metrics (`-(r ^ (n - 1) * deriv ψ r) / 2`).
* `TauCeti.tendsto_normalizedCoordinateFlux_harmonicConformal`,
  `TauCeti.tendsto_normalizedCoordinateFlux_schwarzschild`, and
  `TauCeti.tendsto_normalizedCoordinateFlux_radialTensorPerturb`: explicit ADM mass limits `2 c`,
  `m`, and `ε / 2` for the three model families, together with vanishing flux on flat `ℝⁿ`.

## References

* S. Cecchini, R. Zeidler, *Scalar and mean curvature comparison via the Dirac operator*,
  Geom. Topol. 28 (2024), 1167–1212, §2, equation (2.1) and Example 2.2.
* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. (N.S.) 17 (1987), 37–91,
  §9.
-/

public section

noncomputable section

open Set Function Filter Metric MeasureTheory Bundle
open scoped Topology Manifold ContDiff RealInnerProductSpace

namespace TauCeti

/-! ### Coordinate ADM flux integrand and normalized flux -/

/-- The integrand of the coordinate ADM flux through the Euclidean sphere of radius `r`: for
metric coefficients `g i j` on `ℝⁿ`, it is `Σ_j (Σ_i (∂_i g_ij - ∂_j g_ii)) x_j / r`, where `x / r`
is the outward Euclidean unit normal on `sphere 0 r`. -/
def coordinateFluxIntegrand (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, (∑ i, (
    fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
      fderiv ℝ (fun y => g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))) *
        (x j / r)

theorem coordinateFluxIntegrand_def (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n g r x =
      ∑ j, (∑ i, (
        fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))) *
            (x j / r) := (rfl)

/-- The normalized coordinate ADM flux at radius `r`: the integral of `coordinateFluxIntegrand`
over `sphere 0 r` divided by `2 (n - 1)` times the `μHE[n - 1]`-area of the unit sphere
(Cecchini–Zeidler, equation (2.1)). -/
def normalizedCoordinateFlux (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) : ℝ :=
  (∫ x in sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      coordinateFluxIntegrand n g r x ∂μHE[n - 1]) /
    (2 * ((n : ℝ) - 1) *
      ((μHE[n - 1] : Measure (EuclideanSpace ℝ (Fin n)))
        (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)

theorem normalizedCoordinateFlux_def (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (r : ℝ) :
    normalizedCoordinateFlux n g r =
      (∫ x in sphere (0 : EuclideanSpace ℝ (Fin n)) r,
          coordinateFluxIntegrand n g r x ∂μHE[n - 1]) /
        (2 * ((n : ℝ) - 1) *
          ((μHE[n - 1] : Measure (EuclideanSpace ℝ (Fin n)))
            (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) := (rfl)

/-- In positive dimension, the denominator of `normalizedCoordinateFlux` is
`2 (n - 1) * roundSphereVolume (n - 1)`. -/
theorem normalizedCoordinateFlux_eq_div_roundSphereVolume {n : ℕ} (hn : 1 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n g r =
      (∫ x in sphere (0 : EuclideanSpace ℝ (Fin n)) r,
          coordinateFluxIntegrand n g r x ∂μHE[n - 1]) /
        (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1 := by
    rw [finrank_euclideanSpace_fin]; omega
  rw [normalizedCoordinateFlux_def,
    euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume hdim,
    ENNReal.toReal_ofReal (roundSphereVolume_pos (n - 1)).le]

/-- `coordinateFluxIntegrand` at `x` depends only on the germ of `g` at `x`. -/
theorem coordinateFluxIntegrand_congr_nhds {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (h : ∀ i j, (fun y => g₁ y i j) =ᶠ[𝓝 x] (fun y => g₂ y i j)) (r : ℝ) :
    coordinateFluxIntegrand n g₁ r x = coordinateFluxIntegrand n g₂ r x := by
  simp only [coordinateFluxIntegrand_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(h i j).fderiv_eq, (h i i).fderiv_eq]

/-- `normalizedCoordinateFlux` at radius `r` depends only on the germ of `g` at points of
`sphere 0 r`. -/
theorem normalizedCoordinateFlux_congr_sphere {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (h : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, (fun y => g₁ y i j) =ᶠ[𝓝 x] (fun y => g₂ y i j)) :
    normalizedCoordinateFlux n g₁ r = normalizedCoordinateFlux n g₂ r := by
  rw [normalizedCoordinateFlux_def, normalizedCoordinateFlux_def]
  congr 1
  exact setIntegral_congr_fun isClosed_sphere.measurableSet
    fun x hx => coordinateFluxIntegrand_congr_nhds (h x hx) r

namespace AsymptoticallyEuclideanEnd

section EndFlux

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- At every sphere radius `r > E.radius`, the coordinate ADM flux of `E.metricCoeff` agrees with
that of `pullbackMetricCoeff φ` for any ambient map `φ : ℝⁿ → M` extending `E.param`. -/
theorem normalizedCoordinateFlux_metricCoeff_eq (E : AsymptoticallyEuclideanEnd n M t)
    {φ : EuclideanSpace ℝ (Fin n) → M}
    (hφ : ∀ (y : EuclideanSpace ℝ (Fin n)) (hy : E.radius < ‖y‖),
      E.param ⟨y, mem_exteriorOpen.mpr hy⟩ = φ y)
    {r : ℝ} (hr : E.radius < r) :
    normalizedCoordinateFlux n E.metricCoeff r =
      normalizedCoordinateFlux n (pullbackMetricCoeff φ) r := by
  refine normalizedCoordinateFlux_congr_sphere fun x hx i j => ?_
  exact E.eventuallyEq_metricCoeff_pullbackMetricCoeff hφ
    (by rwa [mem_sphere_zero_iff_norm.mp hx]) i j

/-- Convergence of the coordinate ADM flux as `r → ∞` for `E.metricCoeff` is equivalent to
convergence for `pullbackMetricCoeff φ` for any ambient extension `φ` of `E.param`. -/
theorem tendsto_normalizedCoordinateFlux_metricCoeff_iff (E : AsymptoticallyEuclideanEnd n M t)
    {φ : EuclideanSpace ℝ (Fin n) → M}
    (hφ : ∀ (y : EuclideanSpace ℝ (Fin n)) (hy : E.radius < ‖y‖),
      E.param ⟨y, mem_exteriorOpen.mpr hy⟩ = φ y) (m : ℝ) :
    Tendsto (normalizedCoordinateFlux n E.metricCoeff) atTop (𝓝 m) ↔
      Tendsto (normalizedCoordinateFlux n (pullbackMetricCoeff φ)) atTop (𝓝 m) := by
  refine tendsto_congr' ?_
  filter_upwards [eventually_gt_atTop E.radius] with r hr
  exact E.normalizedCoordinateFlux_metricCoeff_eq hφ hr

/-- Shrinking an AE end on a smooth manifold to a larger excision radius `R' ≥ E.radius` leaves
`normalizedCoordinateFlux` unchanged for every `r > R'`. -/
theorem normalizedCoordinateFlux_restrictRadius [IsManifold (𝓡 n) ∞ M]
    (E : AsymptoticallyEuclideanEnd n M t) {R' : ℝ}
    (hR' : E.radius ≤ R') {r : ℝ} (hr : R' < r) :
    normalizedCoordinateFlux n (E.restrictRadius hR').metricCoeff r =
      normalizedCoordinateFlux n E.metricCoeff r := by
  refine normalizedCoordinateFlux_congr_sphere fun x hx i j => ?_
  have hxr : R' < ‖x‖ := by rwa [mem_sphere_zero_iff_norm.mp hx]
  filter_upwards [(exteriorOpen n R').isOpen.mem_nhds (mem_exteriorOpen.mpr hxr)] with y hy
  exact E.restrictRadius_metricCoeff_of_lt hR' (mem_exteriorOpen.mp hy) i j

/-- On any AE end `E` of order `t`, the coordinate ADM flux integrand on `sphere 0 r`
(`r > E.radius`) is uniformly `O(r ^ (-t - 1))`. -/
theorem exists_abs_coordinateFluxIntegrand_le (E : AsymptoticallyEuclideanEnd n M t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℝ}, E.radius < r →
      ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
        |coordinateFluxIntegrand n E.metricCoeff r x| ≤ C * r ^ (-t - 1) := by
  obtain ⟨C₀, hC₀⟩ := E.decay
  let C₁ : ℝ := max C₀ 0
  refine ⟨2 * (n : ℝ) ^ 2 * C₁, by positivity, fun {r} hr x hx => ?_⟩
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
  have hr0 : 0 < r := E.radius_pos.trans hr
  have hxr : E.radius < ‖x‖ := hnorm.symm ▸ hr
  have hderiv (i j k : Fin n) :
      |fderiv ℝ (fun y => E.metricCoeff y i j) x (EuclideanSpace.basisFun (Fin n) ℝ k)| ≤
        C₁ * r ^ (-t - 1) := by
    have hfun : (fun y => E.metricCoeff y i j) = (fun y => exteriorMetricCoeff E.param y i j) :=
      funext fun y => E.metricCoeff_def y i j
    rw [hfun, ← Real.norm_eq_abs]
    calc
      ‖fderiv ℝ (fun y => exteriorMetricCoeff E.param y i j) x
          (EuclideanSpace.basisFun (Fin n) ℝ k)‖
        ≤ ‖fderiv ℝ (fun y => exteriorMetricCoeff E.param y i j) x‖ *
            ‖EuclideanSpace.basisFun (Fin n) ℝ k‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fun y => exteriorMetricCoeff E.param y i j) x‖ := by
            rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 k, mul_one]
      _ ≤ C₀ * ‖x‖ ^ (-t - 1) := (hC₀ x hxr i j).2.1
      _ ≤ C₁ * r ^ (-t - 1) := by
            rw [hnorm]
            exact mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (Real.rpow_nonneg hr0.le _)
  have hxdiv (j : Fin n) : |x j / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr0, div_le_one hr0, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le x j).trans_eq hnorm
  rw [coordinateFluxIntegrand_def]
  calc
    |∑ j : Fin n, (∑ i : Fin n,
        (fderiv ℝ (fun y => E.metricCoeff y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => E.metricCoeff y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))) *
            (x j / r)|
      ≤ ∑ j : Fin n, ∑ i : Fin n, 2 * C₁ * r ^ (-t - 1) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          refine (mul_le_mul_of_nonneg_left (hxdiv j) (abs_nonneg _)).trans ?_
          rw [mul_one]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          have h1 := hderiv i j i
          have h2 := hderiv i i j
          have hsub := abs_sub
            (fderiv ℝ (fun y => E.metricCoeff y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i))
            (fderiv ℝ (fun y => E.metricCoeff y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))
          linarith
    _ = 2 * (n : ℝ) ^ 2 * C₁ * r ^ (-t - 1) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- In dimension `n ≥ 2`, the normalized coordinate ADM flux of an AE end `E` of order `t` is
`O(r ^ (n - 2 - t))` for `r > E.radius` (in particular bounded at the Newtonian decay order
`t = n - 2`). -/
theorem exists_abs_normalizedCoordinateFlux_le (E : AsymptoticallyEuclideanEnd n M t)
    (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℝ}, E.radius < r →
      |normalizedCoordinateFlux n E.metricCoeff r| ≤ C * r ^ ((n : ℝ) - 2 - t) := by
  obtain ⟨B, hB0, hB⟩ := E.exists_abs_coordinateFluxIntegrand_le
  have hn1_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    linarith
  have hvol_pos : 0 < roundSphereVolume (n - 1) := roundSphereVolume_pos (n - 1)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1 := by
    rw [finrank_euclideanSpace_fin]; omega
  have hmeas_eq : (μHE[n - 1] : Measure (EuclideanSpace ℝ (Fin n))) (sphere 0 1) =
      ENNReal.ofReal (roundSphereVolume (n - 1)) :=
    euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume hdim
  have hmeas_real : ((μHE[n - 1] : Measure (EuclideanSpace ℝ (Fin n))).real
      (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) = roundSphereVolume (n - 1) := by
    rw [Measure.real_def, hmeas_eq, ENNReal.toReal_ofReal hvol_pos.le]
  have hden_pos : 0 < 2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1) := by positivity
  refine ⟨B / (2 * ((n : ℝ) - 1)), by positivity, fun {r} hr => ?_⟩
  have hr0 : 0 < r := E.radius_pos.trans hr
  rw [normalizedCoordinateFlux_eq_div_roundSphereVolume (by omega),
    setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one (n - 1) 0 hr0, smul_eq_mul, abs_div,
    abs_mul, abs_of_pos (pow_pos hr0 _), abs_of_pos hden_pos, div_le_iff₀ hden_pos]
  have hint_le : |∫ u in sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      coordinateFluxIntegrand n E.metricCoeff r (0 + r • u) ∂μHE[n - 1]| ≤
        B * r ^ (-t - 1) * roundSphereVolume (n - 1) := by
    rw [← Real.norm_eq_abs, ← hmeas_real]
    refine norm_setIntegral_le_of_norm_le_const (by rw [hmeas_eq]; exact ENNReal.ofReal_lt_top)
      fun u hu => ?_
    rw [zero_add, Real.norm_eq_abs]
    refine hB hr (r • u) ?_
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg hr0.le,
      mem_sphere_zero_iff_norm.mp hu, mul_one]
  have hrpow : r ^ (n - 1) * r ^ (-t - 1) = r ^ ((n : ℝ) - 2 - t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr0, Nat.cast_sub (by omega), Nat.cast_one]
    congr 1; ring
  calc
    r ^ (n - 1) * |∫ u in sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        coordinateFluxIntegrand n E.metricCoeff r (0 + r • u) ∂μHE[n - 1]|
      ≤ r ^ (n - 1) * (B * r ^ (-t - 1) * roundSphereVolume (n - 1)) :=
          mul_le_mul_of_nonneg_left hint_le (pow_nonneg hr0.le _)
    _ = B * (r ^ (n - 1) * r ^ (-t - 1)) * roundSphereVolume (n - 1) := by ring
    _ = B / (2 * ((n : ℝ) - 1)) * r ^ ((n : ℝ) - 2 - t) *
          (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) := by
          rw [hrpow]; field_simp [hn1_pos.ne']

/-- **Faster-than-Newtonian decay implies zero ADM mass.** In dimension `n ≥ 2`, every AE end of
order `t > n - 2` has vanishing asymptotic coordinate ADM flux. -/
theorem tendsto_normalizedCoordinateFlux_zero_of_sub_lt (E : AsymptoticallyEuclideanEnd n M t)
    (hn : 2 ≤ n) (ht : (n : ℝ) - 2 < t) :
    Tendsto (normalizedCoordinateFlux n E.metricCoeff) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := E.exists_abs_normalizedCoordinateFlux_le hn
  have hexp : 0 < t - ((n : ℝ) - 2) := sub_pos.mpr ht
  have hrhs : Tendsto (fun r : ℝ => C * r ^ ((n : ℝ) - 2 - t)) atTop (𝓝 0) := by
    have hneg : (n : ℝ) - 2 - t = -(t - ((n : ℝ) - 2)) := by ring
    simp_rw [hneg]
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hexp).const_mul C
  refine squeeze_zero_norm' ?_ hrhs
  filter_upwards [eventually_gt_atTop E.radius] with r hr
  simpa only [Real.norm_eq_abs] using hC hr

end EndFlux

end AsymptoticallyEuclideanEnd

/-! ### Constant integrands, flat Euclidean space, and linearity -/

/-- When `coordinateFluxIntegrand n g r` takes a constant value `K` on `sphere 0 r` (`1 ≤ n`,
`0 < r`), the unit-sphere area cancels from `normalizedCoordinateFlux`, yielding
`r ^ (n - 1) * K / (2 (n - 1))`. -/
theorem normalizedCoordinateFlux_of_eqOn_const {n : ℕ} (hn : 1 ≤ n)
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r K : ℝ} (hr : 0 < r)
    (hK : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      coordinateFluxIntegrand n g r x = K) :
    normalizedCoordinateFlux n g r = r ^ (n - 1) * K / (2 * ((n : ℝ) - 1)) := by
  have hpos : roundSphereVolume (n - 1) ≠ 0 := (roundSphereVolume_pos (n - 1)).ne'
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1 := by
    rw [finrank_euclideanSpace_fin]; omega
  have hmeas :
      ((μHE[n - 1] : Measure (EuclideanSpace ℝ (Fin n))) (sphere 0 1)).toReal =
        roundSphereVolume (n - 1) := by
    rw [euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume hdim,
      ENNReal.toReal_ofReal (roundSphereVolume_pos (n - 1)).le]
  rw [normalizedCoordinateFlux_eq_div_roundSphereVolume hn,
    setIntegral_congr_fun isClosed_sphere.measurableSet (fun x hx => hK x hx),
    setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one (n - 1) 0 hr,
    setIntegral_const, Measure.real_def, hmeas, smul_eq_mul, smul_eq_mul]
  rw [show r ^ (n - 1) * (roundSphereVolume (n - 1) * K) =
      (r ^ (n - 1) * K) * roundSphereVolume (n - 1) by ring]
  exact mul_div_mul_right (r ^ (n - 1) * K) (2 * ((n : ℝ) - 1)) hpos

/-- Constant metric coefficients have zero coordinate ADM flux integrand everywhere. -/
@[simp] theorem coordinateFluxIntegrand_const (n : ℕ) (c : Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun _ => c) r x = 0 := by
  simp [coordinateFluxIntegrand_def, fderiv_const_apply]

/-- Constant metric coefficients have zero normalized coordinate ADM flux at every radius. -/
@[simp] theorem normalizedCoordinateFlux_const (n : ℕ) (c : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun _ => c) r = 0 := by
  simp [normalizedCoordinateFlux_def]

/-- On flat `EuclideanSpace ℝ (Fin n)`, the identity chart has identically zero coordinate ADM
flux. -/
@[simp] theorem normalizedCoordinateFlux_pullbackMetricCoeff_id (n : ℕ) (r : ℝ) :
    normalizedCoordinateFlux n
      (pullbackMetricCoeff (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) r = 0 := by
  have h : pullbackMetricCoeff (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      fun _ i j => if i = j then (1 : ℝ) else 0 :=
    funext₃ pullbackMetricCoeff_id
  rw [h, normalizedCoordinateFlux_const]

/-- Every linear isometry equivalence of flat `EuclideanSpace ℝ (Fin n)` has identically zero
coordinate ADM flux. -/
@[simp] theorem normalizedCoordinateFlux_pullbackMetricCoeff_linearIsometryEquiv (n : ℕ)
    (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    normalizedCoordinateFlux n
      (pullbackMetricCoeff (O : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) r = 0 := by
  have h : pullbackMetricCoeff (O : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      fun _ i j => if i = j then (1 : ℝ) else 0 :=
    funext₃ (pullbackMetricCoeff_linearIsometryEquiv O)
  rw [h, normalizedCoordinateFlux_const]

/-- On `AsymptoticallyEuclideanEnd.euclideanId`, the coordinate ADM flux vanishes for every
`r > R`. -/
@[simp] theorem AsymptoticallyEuclideanEnd.normalizedCoordinateFlux_euclideanId_of_lt (n : ℕ)
    {R : ℝ} (hR : 0 < R) (t : ℝ) {r : ℝ} (hr : R < r) :
    normalizedCoordinateFlux n (AsymptoticallyEuclideanEnd.euclideanId n hR t).metricCoeff r =
      0 := by
  let E := AsymptoticallyEuclideanEnd.euclideanId n hR t
  have hr' : E.radius < r := by simpa [E] using hr
  rw [E.normalizedCoordinateFlux_metricCoeff_eq (φ := id) (fun y _ => by simp [E]) hr',
    normalizedCoordinateFlux_pullbackMetricCoeff_id]

/-- **Flat Euclidean space has ADM mass zero.** The normalized coordinate ADM flux of
`AsymptoticallyEuclideanEnd.euclideanId` converges to `0` as `r → ∞`. -/
theorem AsymptoticallyEuclideanEnd.tendsto_normalizedCoordinateFlux_euclideanId (n : ℕ) {R : ℝ}
    (hR : 0 < R) (t : ℝ) :
    Tendsto (normalizedCoordinateFlux n
      (AsymptoticallyEuclideanEnd.euclideanId n hR t).metricCoeff) atTop (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop R] with r hr
  exact (AsymptoticallyEuclideanEnd.normalizedCoordinateFlux_euclideanId_of_lt n hR t hr).symm

/-- Adding a constant background metric tensor `g₀` leaves `coordinateFluxIntegrand` unchanged. -/
@[simp] theorem coordinateFluxIntegrand_const_add (n : ℕ) (g₀ : Fin n → Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => g₀ i j + g y i j) r x =
      coordinateFluxIntegrand n g r x := by
  have hadd (i j : Fin n) :
      fderiv ℝ (fun y => g₀ i j + g y i j) x = fderiv ℝ (fun y => g y i j) x := by
    simpa only [add_comm (g₀ i j)] using fderiv_add_const (g₀ i j)
  simp only [coordinateFluxIntegrand_def, hadd]

/-- Adding a constant background metric tensor `g₀` leaves `normalizedCoordinateFlux` unchanged. -/
@[simp] theorem normalizedCoordinateFlux_const_add (n : ℕ) (g₀ : Fin n → Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => g₀ i j + g y i j) r =
      normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_const_add]

/-- Scaling metric coefficients by a real constant `c` scales `coordinateFluxIntegrand` by `c`,
without any differentiability hypothesis. -/
theorem coordinateFluxIntegrand_const_smul (n : ℕ) (c : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => c * g y i j) r x =
      c * coordinateFluxIntegrand n g r x := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    exact coordinateFluxIntegrand_const n (fun _ _ => 0) r x
  · have : Invertible c := invertibleOfNonzero hc
    have hsmul (i j : Fin n) :
        fderiv ℝ (fun y => c * g y i j) x = c • fderiv ℝ (fun y => g y i j) x :=
      fderiv_const_smul_of_invertible c
    simp only [coordinateFluxIntegrand_def, hsmul, smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- Scaling metric coefficients by `c : ℝ` scales `normalizedCoordinateFlux` by `c`. -/
theorem normalizedCoordinateFlux_const_smul (n : ℕ) (c : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => c * g y i j) r =
      c * normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_const_smul, integral_const_mul,
    mul_div_assoc]

/-- Pointwise additivity of `coordinateFluxIntegrand` for metric coefficients differentiable at
`x`. -/
theorem coordinateFluxIntegrand_add {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg₁ : ∀ i j, DifferentiableAt ℝ (fun y => g₁ y i j) x)
    (hg₂ : ∀ i j, DifferentiableAt ℝ (fun y => g₂ y i j) x) (r : ℝ) :
    coordinateFluxIntegrand n (fun y i j => g₁ y i j + g₂ y i j) r x =
      coordinateFluxIntegrand n g₁ r x + coordinateFluxIntegrand n g₂ r x := by
  have hadd (i j : Fin n) :
      fderiv ℝ (fun y => g₁ y i j + g₂ y i j) x =
        fderiv ℝ (fun y => g₁ y i j) x + fderiv ℝ (fun y => g₂ y i j) x :=
    ((hg₁ i j).hasFDerivAt.add (hg₂ i j).hasFDerivAt).fderiv
  simp only [coordinateFluxIntegrand_def, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hadd i j, hadd i i, add_apply, add_apply]
  ring

/-- Additivity of `normalizedCoordinateFlux` on `sphere 0 r` when `g₁` and `g₂` are differentiable
at every point of `sphere 0 r` and their flux integrands are integrable there. -/
theorem normalizedCoordinateFlux_add {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hg₁ : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, DifferentiableAt ℝ (fun y => g₁ y i j) x)
    (hg₂ : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, DifferentiableAt ℝ (fun y => g₂ y i j) x)
    (hint₁ : IntegrableOn (coordinateFluxIntegrand n g₁ r)
      (sphere (0 : EuclideanSpace ℝ (Fin n)) r) μHE[n - 1])
    (hint₂ : IntegrableOn (coordinateFluxIntegrand n g₂ r)
      (sphere (0 : EuclideanSpace ℝ (Fin n)) r) μHE[n - 1]) :
    normalizedCoordinateFlux n (fun y i j => g₁ y i j + g₂ y i j) r =
      normalizedCoordinateFlux n g₁ r + normalizedCoordinateFlux n g₂ r := by
  rw [normalizedCoordinateFlux_def, normalizedCoordinateFlux_def, normalizedCoordinateFlux_def,
    ← add_div]
  congr 1
  rw [setIntegral_congr_fun isClosed_sphere.measurableSet
    (fun x hx => coordinateFluxIntegrand_add (hg₁ x hx) (hg₂ x hx) r)]
  exact integral_add hint₁ hint₂

/-! ### Conformally flat metrics and radial flux formula -/

/-- Conformally flat metric coefficients `g_ij(x) = w(x) δ_ij` on `EuclideanSpace ℝ (Fin n)`. -/
def conformalFlatMetricCoeff {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  if i = j then w x else 0

theorem conformalFlatMetricCoeff_def {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    conformalFlatMetricCoeff w x i j = if i = j then w x else 0 := (rfl)

@[simp] theorem conformalFlatMetricCoeff_diag {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    conformalFlatMetricCoeff w x i i = w x := by
  simp [conformalFlatMetricCoeff]

@[simp] theorem conformalFlatMetricCoeff_of_ne {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {i j : Fin n} (h : i ≠ j) :
    conformalFlatMetricCoeff w x i j = 0 := by
  simp [conformalFlatMetricCoeff, h]

/-- **Conformal-flat coordinate flux integrand.** For `g_ij = w δ_ij`, the coordinate ADM flux
integrand at `x` equals `-((n - 1) / r) * fderiv ℝ w x x`. -/
theorem coordinateFluxIntegrand_conformalFlat {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (conformalFlatMetricCoeff w) r x =
      -(((n : ℝ) - 1) / r) * fderiv ℝ w x x := by
  have hsum_i (j : Fin n) :
      ∑ i : Fin n,
        (fderiv ℝ (fun y => conformalFlatMetricCoeff w y i j) x
            (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => conformalFlatMetricCoeff w y i i) x
            (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        -((n : ℝ) - 1) * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    have hterm (i : Fin n) :
        fderiv ℝ (fun y => conformalFlatMetricCoeff w y i j) x
            (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => conformalFlatMetricCoeff w y i i) x
            (EuclideanSpace.basisFun (Fin n) ℝ j) =
          -fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) +
            if i = j then fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) else 0 := by
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, fderiv_const_apply]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_ite_eq' Finset.univ j]
    simp only [Finset.mem_univ, ↓reduceIte]
    ring
  rw [coordinateFluxIntegrand_def]
  simp_rw [hsum_i]
  have hlin : ∑ j : Fin n,
      (-((n : ℝ) - 1) * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * (x j / r) =
      -(((n : ℝ) - 1) / r) *
        ∑ j : Fin n, x j * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hlin]
  congr 1
  have hrepr : ∑ j : Fin n, x j • EuclideanSpace.basisFun (Fin n) ℝ j = x := by
    ext k
    simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
  calc
    ∑ j : Fin n, x j * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) =
      ∑ j : Fin n, fderiv ℝ w x (x j • EuclideanSpace.basisFun (Fin n) ℝ j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul]
    _ = fderiv ℝ w x (∑ j : Fin n, x j • EuclideanSpace.basisFun (Fin n) ℝ j) :=
        (map_sum (fderiv ℝ w x) _ _).symm
    _ = fderiv ℝ w x x := congrArg (fderiv ℝ w x) hrepr

/-- On `sphere 0 r` (`r > 0`), the radial conformally flat metric `g_ij(y) = ψ(‖y‖) δ_ij` has
constant coordinate flux integrand `-(n - 1) * deriv ψ r`. -/
theorem coordinateFluxIntegrand_conformalFlat_radial {n : ℕ} {ψ : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hψ : DifferentiableAt ℝ ψ r) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r) :
    coordinateFluxIntegrand n (conformalFlatMetricCoeff (fun y => ψ ‖y‖)) r x =
      -((n : ℝ) - 1) * deriv ψ r := by
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
  have hx_ne : x ≠ 0 := norm_pos_iff.mp (hnorm.symm ▸ hr)
  have hdn : DifferentiableAt ℝ (‖·‖) x := differentiableAt_id.norm ℝ hx_ne
  have hψx : DifferentiableAt ℝ ψ ‖x‖ := hnorm.symm ▸ hψ
  have hcomp : HasFDerivAt (ψ ∘ norm)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ ‖x‖)).comp (fderiv ℝ (‖·‖) x)) x :=
    hψx.hasDerivAt.hasFDerivAt.comp x hdn.hasFDerivAt
  change coordinateFluxIntegrand n (conformalFlatMetricCoeff (ψ ∘ norm)) r x = _
  rw [coordinateFluxIntegrand_conformalFlat, hcomp.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, hdn.fderiv_norm_self, hnorm, smul_eq_mul]
  field_simp [hr.ne']

/-- **Radial conformally flat ADM flux formula.** In dimension `n ≥ 2`, for `r > 0` and `ψ : ℝ → ℝ`
differentiable at `r`, the normalized coordinate ADM flux of `g_ij(y) = ψ(‖y‖) δ_ij` at radius `r`
equals `-(r ^ (n - 1) * deriv ψ r) / 2`. -/
theorem normalizedCoordinateFlux_conformalFlat_radial {n : ℕ} (hn : 2 ≤ n) {ψ : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hψ : DifferentiableAt ℝ ψ r) :
    normalizedCoordinateFlux n (conformalFlatMetricCoeff (fun y => ψ ‖y‖)) r =
      -(r ^ (n - 1) * deriv ψ r) / 2 := by
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    linarith
  rw [normalizedCoordinateFlux_of_eqOn_const (by omega) hr
    (fun x hx => coordinateFluxIntegrand_conformalFlat_radial hr hψ hx)]
  field_simp [hn1]

/-! ### Model metrics: harmonic-conformal, Schwarzschild, and radial tensor perturbation -/

/-- The harmonic-conformal model metric coefficients `(1 + c / ‖x‖ ^ (n - 2)) ^ (4 / (n - 2)) δ_ij`
on `EuclideanSpace ℝ (Fin n)`. -/
def harmonicConformalCoeff (n : ℕ) (c : ℝ) :
    EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ :=
  conformalFlatMetricCoeff (fun y => (1 + c / ‖y‖ ^ (n - 2)) ^ (4 / ((n : ℝ) - 2)))

theorem harmonicConformalCoeff_def (n : ℕ) (c : ℝ) :
    harmonicConformalCoeff n c =
      conformalFlatMetricCoeff (fun y => (1 + c / ‖y‖ ^ (n - 2)) ^ (4 / ((n : ℝ) - 2))) := (rfl)

/-- **Exact finite-radius coordinate ADM flux of the harmonic-conformal model.** For `3 ≤ n`,
`0 < r`, and `0 < 1 + c / r ^ (n - 2)`, the normalized coordinate ADM flux equals
`2 c (1 + c / r ^ (n - 2)) ^ (4 / (n - 2) - 1)`. -/
theorem normalizedCoordinateFlux_harmonicConformal {n : ℕ} (hn : 3 ≤ n) (c : ℝ) {r : ℝ}
    (hr : 0 < r) (hu : 0 < 1 + c / r ^ (n - 2)) :
    normalizedCoordinateFlux n (harmonicConformalCoeff n c) r =
      2 * c * (1 + c / r ^ (n - 2)) ^ (4 / ((n : ℝ) - 2) - 1) := by
  set k : ℕ := n - 2
  have hk_cast : (k : ℝ) = (n : ℝ) - 2 := Nat.cast_sub (by omega)
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrk : r ^ k ≠ 0 := pow_ne_zero k hr.ne'
  have hinner : HasDerivAt (fun s : ℝ => 1 + c / s ^ k)
      (-(c * ((k : ℝ) * r ^ (k - 1))) / (r ^ k) ^ 2) r := by
    have hp : HasDerivAt (fun s : ℝ => s ^ k) ((k : ℝ) * r ^ (k - 1)) r := hasDerivAt_pow k r
    have hdiv : HasDerivAt (fun s : ℝ => c / s ^ k)
        ((0 * r ^ k - c * ((k : ℝ) * r ^ (k - 1))) / (r ^ k) ^ 2) r :=
      (hasDerivAt_const r c).div hp hrk
    simpa only [zero_mul, zero_sub] using hdiv.const_add (1 : ℝ)
  have hψ : HasDerivAt (fun s : ℝ => (1 + c / s ^ k) ^ (4 / ((n : ℝ) - 2)))
      ((-(c * ((k : ℝ) * r ^ (k - 1))) / (r ^ k) ^ 2) * (4 / ((n : ℝ) - 2)) *
        (1 + c / r ^ k) ^ (4 / ((n : ℝ) - 2) - 1)) r :=
    hinner.rpow_const (Or.inl hu.ne')
  rw [harmonicConformalCoeff_def, show n - 2 = k from rfl,
    normalizedCoordinateFlux_conformalFlat_radial (by omega) hr hψ.differentiableAt, hψ.deriv]
  have hpow : r ^ (n - 1) * r ^ (k - 1) = (r ^ k) ^ 2 := by
    rw [← pow_add, ← pow_mul]
    congr 1; omega
  rw [← hk_cast]
  generalize (1 + c / r ^ k) ^ (4 / (k : ℝ) - 1) = w
  field_simp [hk_ne, hrk]
  calc
    r ^ (n - 1) * c * r ^ (k - 1) * 4 * w =
      c * (r ^ (n - 1) * r ^ (k - 1)) * w * 2 ^ 2 := by ring
    _ = c * (r ^ k) ^ 2 * w * 2 ^ 2 := by rw [hpow]

/-- **ADM mass of the harmonic-conformal model.** For `3 ≤ n` and any `c : ℝ`, the normalized
coordinate ADM flux of `(1 + c / ‖x‖ ^ (n - 2)) ^ (4 / (n - 2)) δ_ij` converges to `2 * c` as
`r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_harmonicConformal {n : ℕ} (hn : 3 ≤ n) (c : ℝ) :
    Tendsto (normalizedCoordinateFlux n (harmonicConformalCoeff n c)) atTop (𝓝 (2 * c)) := by
  have hk : n - 2 ≠ 0 := by omega
  have hdiv : Tendsto (fun r : ℝ => c / r ^ (n - 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop hk)
  have hu : Tendsto (fun r : ℝ => 1 + c / r ^ (n - 2)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hdiv
  let p : ℝ := 4 / ((n : ℝ) - 2) - 1
  have hrpow : Tendsto (fun r : ℝ => (1 + c / r ^ (n - 2)) ^ p) atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using hu.rpow_const (Or.inl one_ne_zero)
  have hrhs : Tendsto (fun r : ℝ => 2 * c * (1 + c / r ^ (n - 2)) ^ p) atTop (𝓝 (2 * c)) := by
    simpa only [mul_one] using tendsto_const_nhds.mul hrpow
  refine hrhs.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hu.eventually ((isOpen_lt continuous_const continuous_id).mem_nhds zero_lt_one)]
    with r hr hu_pos
  exact (normalizedCoordinateFlux_harmonicConformal hn c hr hu_pos).symm

/-- The spatial Schwarzschild metric coefficients
`(1 + m / (2 ‖x‖ ^ (n - 2))) ^ (4 / (n - 2)) δ_ij` of mass parameter `m` in dimension `n`
(Cecchini–Zeidler, Example 2.2). -/
def schwarzschildMetricCoeff (n : ℕ) (m : ℝ) :
    EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ :=
  conformalFlatMetricCoeff (fun y => (1 + m / (2 * ‖y‖ ^ (n - 2))) ^ (4 / ((n : ℝ) - 2)))

theorem schwarzschildMetricCoeff_def (n : ℕ) (m : ℝ) :
    schwarzschildMetricCoeff n m =
      conformalFlatMetricCoeff
        (fun y => (1 + m / (2 * ‖y‖ ^ (n - 2))) ^ (4 / ((n : ℝ) - 2))) := (rfl)

/-- The spatial Schwarzschild metric of mass `m` is the harmonic-conformal model with
`c = m / 2`. -/
theorem schwarzschildMetricCoeff_eq_harmonicConformalCoeff (n : ℕ) (m : ℝ) :
    schwarzschildMetricCoeff n m = harmonicConformalCoeff n (m / 2) := by
  ext y i j
  simp only [schwarzschildMetricCoeff_def, harmonicConformalCoeff_def, conformalFlatMetricCoeff_def,
    div_div]

/-- **Exact finite-radius coordinate ADM flux of the spatial Schwarzschild metric.** -/
theorem normalizedCoordinateFlux_schwarzschild {n : ℕ} (hn : 3 ≤ n) (m : ℝ) {r : ℝ}
    (hr : 0 < r) (hu : 0 < 1 + m / (2 * r ^ (n - 2))) :
    normalizedCoordinateFlux n (schwarzschildMetricCoeff n m) r =
      m * (1 + m / (2 * r ^ (n - 2))) ^ (4 / ((n : ℝ) - 2) - 1) := by
  have hu' : 0 < 1 + m / 2 / r ^ (n - 2) := by rwa [div_div]
  rw [schwarzschildMetricCoeff_eq_harmonicConformalCoeff,
    normalizedCoordinateFlux_harmonicConformal hn (m / 2) hr hu', div_div]
  ring

/-- **ADM mass of the spatial Schwarzschild metric** (Cecchini–Zeidler, Example 2.2). For `3 ≤ n`
and any `m : ℝ`, the normalized coordinate ADM flux of `schwarzschildMetricCoeff n m` converges to
`m` as `r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_schwarzschild {n : ℕ} (hn : 3 ≤ n) (m : ℝ) :
    Tendsto (normalizedCoordinateFlux n (schwarzschildMetricCoeff n m)) atTop (𝓝 m) := by
  rw [schwarzschildMetricCoeff_eq_harmonicConformalCoeff]
  simpa only [mul_div_cancel₀ m (two_ne_zero' ℝ)] using
    tendsto_normalizedCoordinateFlux_harmonicConformal hn (m / 2)

/-- The non-conformal radial tensor perturbation `g_ij(x) = δ_ij + ε x_i x_j / ‖x‖ ^ n` on
`EuclideanSpace ℝ (Fin n)`. -/
def radialTensorPerturbCoeff (n : ℕ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) : ℝ :=
  (if i = j then 1 else 0) + ε * (x i * x j / ‖x‖ ^ n)

theorem radialTensorPerturbCoeff_def (n : ℕ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    radialTensorPerturbCoeff n ε x i j =
      (if i = j then 1 else 0) + ε * (x i * x j / ‖x‖ ^ n) := (rfl)

private theorem fderiv_radialTensorQuotient_basisFun {n : ℕ} {x : EuclideanSpace ℝ (Fin n)}
    (hx_ne : x ≠ 0) (i j k : Fin n) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => y i * y j / ‖y‖ ^ n) x
        (EuclideanSpace.basisFun (Fin n) ℝ k) =
      ((if i = k then 1 else 0) * x j + x i * (if j = k then 1 else 0)) * ‖x‖ ^ (-(n : ℝ)) -
        (n : ℝ) * x i * x j * x k * ‖x‖ ^ (-(n : ℝ) - 2) := by
  have hq_eq : (fun y : EuclideanSpace ℝ (Fin n) => y i * y j / ‖y‖ ^ n) =
      ((fun y : EuclideanSpace ℝ (Fin n) => y i) *
        (fun y : EuclideanSpace ℝ (Fin n) => y j)) *
        (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (-(n : ℝ))) := by
    ext y
    simp only [Pi.mul_apply, Real.rpow_neg (norm_nonneg y), Real.rpow_natCast, div_eq_mul_inv]
  have hi : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y i)
      (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ => ℝ) i) x :=
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ => ℝ) i).hasFDerivAt
  have hj : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => y j)
      (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ => ℝ) j) x :=
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ => ℝ) j).hasFDerivAt
  have hrpow : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ (-(n : ℝ)))
      ((-(n : ℝ) * ‖x‖ ^ (-(n : ℝ) - 2)) • innerSL ℝ x) x :=
    hasFDerivAt_norm_rpow_of_ne (-(n : ℝ)) hx_ne
  rw [hq_eq, ((hi.mul hj).mul hrpow).fderiv]
  simp only [add_apply, smul_apply, Pi.mul_apply, PiLp.proj_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [EuclideanSpace.inner_basisFun_real]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  ring

/-- On `sphere 0 r` (`r > 0`), the non-conformal radial tensor perturbation
`δ_ij + ε x_i x_j / ‖x‖ ^ n` has constant coordinate flux integrand
`ε * (n - 1) / r ^ (n - 1)`. -/
theorem coordinateFluxIntegrand_radialTensorPerturb {n : ℕ} (ε : ℝ) {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r) :
    coordinateFluxIntegrand n (radialTensorPerturbCoeff n ε) r x =
      ε * ((n : ℝ) - 1) / r ^ (n - 1) := by
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
  have hx_ne : x ≠ 0 := norm_pos_iff.mp (hnorm.symm ▸ hr)
  have hn : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => hx_ne (by subst h0; exact Subsingleton.elim x 0)
  let q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ := fun y i j => y i * y j / ‖y‖ ^ n
  have hdecomp : radialTensorPerturbCoeff n ε =
      fun y i j => (if i = j then (1 : ℝ) else 0) + ε * q y i j := rfl
  rw [hdecomp, coordinateFluxIntegrand_const_add, coordinateFluxIntegrand_const_smul]
  have hsum_i (j : Fin n) :
      ∑ i : Fin n,
        (fderiv ℝ (fun y => q y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => q y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        ((n : ℝ) - 1) * x j * r ^ (-(n : ℝ)) := by
    have hsimp (i : Fin n) :
        fderiv ℝ (fun y => q y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => q y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j) =
          x j * r ^ (-(n : ℝ)) +
            (if j = i then x i * r ^ (-(n : ℝ)) else 0) -
            (if i = j then 2 * x i * r ^ (-(n : ℝ)) else 0) := by
      dsimp only [q]
      rw [fderiv_radialTensorQuotient_basisFun hx_ne i j i,
        fderiv_radialTensorQuotient_basisFun hx_ne i i j, hnorm]
      by_cases hij : i = j
      · subst hij; simp; ring
      · have hji : j ≠ i := Ne.symm hij
        simp [hij, hji]; ring
    simp_rw [hsimp, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq Finset.univ j, Finset.sum_ite_eq' Finset.univ j]
    simp only [Finset.mem_univ, ↓reduceIte]; ring
  rw [coordinateFluxIntegrand_def]; simp_rw [hsum_i]
  have hsum_j : ∑ j : Fin n, (((n : ℝ) - 1) * x j * r ^ (-(n : ℝ))) * (x j / r) =
      ((n : ℝ) - 1) * r ^ (-(n : ℝ)) / r * ∑ j : Fin n, x j ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
  have hsum_sq : ∑ i : Fin n, x i ^ 2 = r ^ 2 := by rw [← EuclideanSpace.real_norm_sq_eq, hnorm]
  have hpow : r ^ n = r ^ (n - 1) * r := by rw [← pow_succ]; congr 1; omega
  have hrn1 : r ^ (n - 1) ≠ 0 := pow_ne_zero (n - 1) hr.ne'
  rw [hsum_j, hsum_sq, Real.rpow_neg hr.le, Real.rpow_natCast, hpow]
  field_simp [hr.ne', hrn1]

/-- **Exact coordinate ADM flux of the non-conformal radial tensor perturbation.** In dimension
`n ≥ 2`, for every `ε : ℝ` and every `r > 0`, `normalizedCoordinateFlux` of
`δ_ij + ε x_i x_j / ‖x‖ ^ n` at radius `r` is identically `ε / 2`. -/
theorem normalizedCoordinateFlux_radialTensorPerturb {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) {r : ℝ}
    (hr : 0 < r) :
    normalizedCoordinateFlux n (radialTensorPerturbCoeff n ε) r = ε / 2 := by
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    linarith
  have hrn1 : r ^ (n - 1) ≠ 0 := pow_ne_zero (n - 1) hr.ne'
  rw [normalizedCoordinateFlux_of_eqOn_const (by omega) hr
    (fun x hx => coordinateFluxIntegrand_radialTensorPerturb ε hr hx)]
  field_simp [hn1, hrn1]

/-- **ADM mass of the non-conformal radial tensor perturbation.** For `2 ≤ n` and `ε : ℝ`, the
normalized coordinate ADM flux of `δ_ij + ε x_i x_j / ‖x‖ ^ n` converges to `ε / 2` as `r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_radialTensorPerturb {n : ℕ} (hn : 2 ≤ n) (ε : ℝ) :
    Tendsto (normalizedCoordinateFlux n (radialTensorPerturbCoeff n ε)) atTop (𝓝 (ε / 2)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (normalizedCoordinateFlux_radialTensorPerturb hn ε hr).symm

end TauCeti
