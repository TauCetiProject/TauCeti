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
* `TauCeti.conformallyFlatMetricCoeff`: conformally flat metric coefficients `w(x) δ_ij`.
* `TauCeti.harmonicConformalMetricCoeff`, `TauCeti.schwarzschildMetricCoeff`, and
  `TauCeti.radialTensorPerturbMetricCoeff`: the harmonic-conformal, spatial Schwarzschild, and
  non-conformal radial tensor model metrics on `ℝⁿ`.

## Main results

* `TauCeti.abs_coordinateFluxIntegrand_le_of_norm_fderiv_le`,
  `TauCeti.abs_normalizedCoordinateFlux_le_of_norm_fderiv_le`,
  `TauCeti.abs_normalizedCoordinateFlux_le_of_norm_fderiv_rpow_le`, and
  `TauCeti.tendsto_normalizedCoordinateFlux_zero_of_norm_fderiv_le`: general `O(r ^ (n - 2 - t))`
  coordinate flux bounds and vanishing limit for arbitrary metric-coefficient tensors whose first
  derivatives decay as `O(‖x‖ ^ (-t - 1))`.
* `TauCeti.AsymptoticallyEuclideanEnd.normalizedCoordinateFlux_metricCoeff_eq`,
  `tendsto_normalizedCoordinateFlux_metricCoeff_iff`, `normalizedCoordinateFlux_restrictRadius`,
  and `tendsto_normalizedCoordinateFlux_restrictRadius_iff`: local-germ agreement of `E.metricCoeff`
  flux with any ambient map `pullbackMetricCoeff φ` and invariance under `E.restrictRadius`.
* `TauCeti.AsymptoticallyEuclideanEnd.exists_abs_normalizedCoordinateFlux_le` and
  `tendsto_normalizedCoordinateFlux_zero_of_sub_lt`: `O(r ^ (n - 2 - t))` flux bound on an AE end
  of order `t`, and vanishing ADM mass for faster-than-Newtonian decay `t > n - 2`.
* `TauCeti.normalizedCoordinateFlux_const_add`, `normalizedCoordinateFlux_add_const`,
  `normalizedCoordinateFlux_sub_const`, `normalizedCoordinateFlux_const_mul`,
  `normalizedCoordinateFlux_neg`, `normalizedCoordinateFlux_add`, and
  `normalizedCoordinateFlux_sub`: invariance under constant metric shifts and linearity of the
  coordinate ADM flux.
* `TauCeti.coordinateFluxIntegrand_conformallyFlatMetricCoeff` and
  `TauCeti.normalizedCoordinateFlux_conformallyFlatMetricCoeff_radial`: closed-form flux formulas
  for general and radial conformally flat metrics (`-(r ^ (n - 1) * deriv ψ r) / 2`).
* `TauCeti.tendsto_normalizedCoordinateFlux_harmonicConformalMetricCoeff`,
  `TauCeti.tendsto_normalizedCoordinateFlux_schwarzschildMetricCoeff`, and
  `TauCeti.tendsto_normalizedCoordinateFlux_radialTensorPerturbMetricCoeff`: explicit ADM mass
  limits `2 c`, `m`, and `ε / 2` for the three model families, together with vanishing flux on flat
  `ℝⁿ`.

## References

* S. Cecchini, R. Zeidler, *The positive mass theorem and distance estimates in the spin setting*,
  Trans. Amer. Math. Soc. 377 (2024), 5271–5288 (arXiv:2108.11972v2), §2, equation (2.1) and
  Example 2.2.
* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. (N.S.) 17 (1987), 37–91,
  §§8–9.
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

private theorem sub_one_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 0 < (n : ℝ) - 1 := by
  have : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  linarith

/-- In positive dimension, the denominator of `normalizedCoordinateFlux` is
`2 (n - 1) * roundSphereVolume (n - 1)`. -/
theorem normalizedCoordinateFlux_eq_div_roundSphereVolume {n : ℕ} (hn : 1 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n g r =
      (∫ x in sphere (0 : EuclideanSpace ℝ (Fin n)) r,
          coordinateFluxIntegrand n g r x ∂μHE[n - 1]) /
        (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) := by
  rw [normalizedCoordinateFlux_def,
    toReal_euclideanHausdorffMeasure_euclideanSpace_sphere_zero_one hn]

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

/-- If every first derivative `fderiv ℝ (fun y => g y i j) x` has operator norm at most `B` at
`x ∈ sphere 0 r` (`r > 0`), then `|coordinateFluxIntegrand n g r x| ≤ 2 n² B`. -/
theorem abs_coordinateFluxIntegrand_le_of_norm_fderiv_le {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r B : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r)
    (hg : ∀ i j, ‖fderiv ℝ (fun y => g y i j) x‖ ≤ B) :
    |coordinateFluxIntegrand n g r x| ≤ 2 * (n : ℝ) ^ 2 * B := by
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
  have hderiv (i j k : Fin n) :
      |fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ k)| ≤ B := by
    rw [← Real.norm_eq_abs]
    calc
      ‖fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ k)‖
        ≤ ‖fderiv ℝ (fun y => g y i j) x‖ * ‖EuclideanSpace.basisFun (Fin n) ℝ k‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fun y => g y i j) x‖ := by
            rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 k, mul_one]
      _ ≤ B := hg i j
  have hxdiv (j : Fin n) : |x j / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le x j).trans_eq hnorm
  rw [coordinateFluxIntegrand_def]
  calc
    |∑ j : Fin n, (∑ i : Fin n,
        (fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))) *
            (x j / r)|
      ≤ ∑ j : Fin n, ∑ i : Fin n, 2 * B := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          refine (mul_le_mul_of_nonneg_left (hxdiv j) (abs_nonneg _)).trans ?_
          rw [mul_one]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          have h1 := hderiv i j i
          have h2 := hderiv i i j
          have hsub := abs_sub
            (fderiv ℝ (fun y => g y i j) x (EuclideanSpace.basisFun (Fin n) ℝ i))
            (fderiv ℝ (fun y => g y i i) x (EuclideanSpace.basisFun (Fin n) ℝ j))
          linarith
    _ = 2 * (n : ℝ) ^ 2 * B := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- In dimension `n ≥ 2`, if every first derivative `fderiv ℝ (fun y => g y i j) x` has operator
norm at most `B` on `sphere 0 r` (`r > 0`), then
`|normalizedCoordinateFlux n g r| ≤ (n² / (n - 1)) * B * r ^ (n - 1)`. -/
theorem abs_normalizedCoordinateFlux_le_of_norm_fderiv_le {n : ℕ} (hn : 2 ≤ n)
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r B : ℝ} (hr : 0 < r)
    (hg : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, ‖fderiv ℝ (fun y => g y i j) x‖ ≤ B) :
    |normalizedCoordinateFlux n g r| ≤ ((n : ℝ) ^ 2 / ((n : ℝ) - 1)) * B * r ^ (n - 1) := by
  have hn1_pos : 0 < (n : ℝ) - 1 := sub_one_pos_of_two_le hn
  have hvol_pos : 0 < roundSphereVolume (n - 1) := roundSphereVolume_pos (n - 1)
  have hden_pos : 0 < 2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1) := by positivity
  rw [normalizedCoordinateFlux_eq_div_roundSphereVolume (by omega),
    setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one (n - 1) 0 hr, smul_eq_mul, abs_div,
    abs_mul, abs_of_pos (pow_pos hr _), abs_of_pos hden_pos, div_le_iff₀ hden_pos]
  have hint_le : |∫ u in sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      coordinateFluxIntegrand n g r (0 + r • u) ∂μHE[n - 1]| ≤
        2 * (n : ℝ) ^ 2 * B * roundSphereVolume (n - 1) := by
    rw [← Real.norm_eq_abs,
      ← measureReal_euclideanHausdorffMeasure_euclideanSpace_sphere_zero_one (n := n) (by omega)]
    refine norm_setIntegral_le_of_norm_le_const
      (by
        rw [euclideanHausdorffMeasure_euclideanSpace_sphere_zero_one (by omega)]
        exact ENNReal.ofReal_lt_top)
      fun u hu => ?_
    rw [zero_add, Real.norm_eq_abs]
    have hru : r • u ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r := by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg hr.le,
        mem_sphere_zero_iff_norm.mp hu, mul_one]
    exact abs_coordinateFluxIntegrand_le_of_norm_fderiv_le hr hru (hg (r • u) hru)
  calc
    r ^ (n - 1) * |∫ u in sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        coordinateFluxIntegrand n g r (0 + r • u) ∂μHE[n - 1]|
      ≤ r ^ (n - 1) * (2 * (n : ℝ) ^ 2 * B * roundSphereVolume (n - 1)) :=
          mul_le_mul_of_nonneg_left hint_le (pow_nonneg hr.le _)
    _ = ((n : ℝ) ^ 2 / ((n : ℝ) - 1)) * B * r ^ (n - 1) *
          (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) := by
          field_simp [hn1_pos.ne']

/-- In dimension `n ≥ 2`, if every first derivative `fderiv ℝ (fun y => g y i j) x` satisfies
`‖fderiv ℝ (fun y => g y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1)` on `sphere 0 r` (`r > 0`), then
`|normalizedCoordinateFlux n g r| ≤ (n² * C / (n - 1)) * r ^ (n - 2 - t)`. -/
theorem abs_normalizedCoordinateFlux_le_of_norm_fderiv_rpow_le {n : ℕ} (hn : 2 ≤ n)
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r C t : ℝ} (hr : 0 < r)
    (hg : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, ‖fderiv ℝ (fun y => g y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1)) :
    |normalizedCoordinateFlux n g r| ≤
      ((n : ℝ) ^ 2 * C / ((n : ℝ) - 1)) * r ^ ((n : ℝ) - 2 - t) := by
  have hbound := abs_normalizedCoordinateFlux_le_of_norm_fderiv_le hn hr (B := C * r ^ (-t - 1))
    fun x hx i j => by simpa only [mem_sphere_zero_iff_norm.mp hx] using hg x hx i j
  have hrpow : r ^ (n - 1) * r ^ (-t - 1) = r ^ ((n : ℝ) - 2 - t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, Nat.cast_sub (by omega), Nat.cast_one]
    congr 1; ring
  refine hbound.trans_eq ?_
  calc
    ((n : ℝ) ^ 2 / ((n : ℝ) - 1)) * (C * r ^ (-t - 1)) * r ^ (n - 1) =
        ((n : ℝ) ^ 2 * C / ((n : ℝ) - 1)) * (r ^ (n - 1) * r ^ (-t - 1)) := by ring
    _ = ((n : ℝ) ^ 2 * C / ((n : ℝ) - 1)) * r ^ ((n : ℝ) - 2 - t) := by rw [hrpow]

/-- **Faster-than-Newtonian decay implies zero ADM flux limit.** In dimension `n ≥ 2`, if every
first derivative `fderiv ℝ (fun y => g y i j) x` is `O(‖x‖ ^ (-t - 1))` on `{‖x‖ > R}` with
`t > n - 2`, then `normalizedCoordinateFlux n g r → 0` as `r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_zero_of_norm_fderiv_le {n : ℕ} (hn : 2 ≤ n)
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {R C t : ℝ} (ht : (n : ℝ) - 2 < t)
    (hg : ∀ x : EuclideanSpace ℝ (Fin n), R < ‖x‖ →
      ∀ i j, ‖fderiv ℝ (fun y => g y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1)) :
    Tendsto (normalizedCoordinateFlux n g) atTop (𝓝 0) := by
  have hexp : 0 < t - ((n : ℝ) - 2) := sub_pos.mpr ht
  have hrhs : Tendsto (fun r : ℝ => ((n : ℝ) ^ 2 * C / ((n : ℝ) - 1)) * r ^ ((n : ℝ) - 2 - t))
      atTop (𝓝 0) := by
    have hneg : (n : ℝ) - 2 - t = -(t - ((n : ℝ) - 2)) := by ring
    simp_rw [hneg]
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hexp).const_mul _
  refine squeeze_zero_norm' ?_ hrhs
  filter_upwards [eventually_gt_atTop (max R 0)] with r hr
  have hrR : R < r := (le_max_left R 0).trans_lt hr
  have hr0 : 0 < r := (le_max_right R 0).trans_lt hr
  simpa only [Real.norm_eq_abs] using
    abs_normalizedCoordinateFlux_le_of_norm_fderiv_rpow_le hn hr0 fun x hx =>
      hg x (by rwa [mem_sphere_zero_iff_norm.mp hx])

namespace AsymptoticallyEuclideanEnd

section EndFlux

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- At any sphere radius `r > E.radius`, if an ambient map `φ : ℝⁿ → M` agrees with `E.param` on
a neighbourhood of every point of `sphere 0 r`, then the coordinate ADM flux of `E.metricCoeff`
agrees with that of `pullbackMetricCoeff φ`. -/
theorem normalizedCoordinateFlux_metricCoeff_eq (E : AsymptoticallyEuclideanEnd n M t)
    {φ : EuclideanSpace ℝ (Fin n) → M} {r : ℝ} (hr : E.radius < r)
    (hφ : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r),
      E.param =ᶠ[𝓝 (⟨x, mem_exteriorOpen.mpr (by rwa [mem_sphere_zero_iff_norm.mp hx])⟩ :
        exteriorOpen n E.radius)] φ ∘ Subtype.val) :
    normalizedCoordinateFlux n E.metricCoeff r =
      normalizedCoordinateFlux n (pullbackMetricCoeff φ) r := by
  refine normalizedCoordinateFlux_congr_sphere fun x hx i j => ?_
  exact E.eventuallyEq_metricCoeff_pullbackMetricCoeff
    (by rwa [mem_sphere_zero_iff_norm.mp hx]) (hφ x hx) i j

/-- Convergence of the coordinate ADM flux as `r → ∞` for `E.metricCoeff` is equivalent to
convergence for `pullbackMetricCoeff φ` for any ambient map `φ : ℝⁿ → M` that agrees with
`E.param` outside some ball `{y | ‖y‖ ≤ R}`. -/
theorem tendsto_normalizedCoordinateFlux_metricCoeff_iff (E : AsymptoticallyEuclideanEnd n M t)
    {φ : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hφ : ∀ (y : EuclideanSpace ℝ (Fin n)) (hy : E.radius < ‖y‖), R < ‖y‖ →
      E.param ⟨y, mem_exteriorOpen.mpr hy⟩ = φ y) (m : ℝ) :
    Tendsto (normalizedCoordinateFlux n E.metricCoeff) atTop (𝓝 m) ↔
      Tendsto (normalizedCoordinateFlux n (pullbackMetricCoeff φ)) atTop (𝓝 m) := by
  refine tendsto_congr' ?_
  filter_upwards [eventually_gt_atTop (max E.radius R)] with r hr
  have hrE : E.radius < r := (le_max_left _ _).trans_lt hr
  have hrR : R < r := (le_max_right _ _).trans_lt hr
  refine E.normalizedCoordinateFlux_metricCoeff_eq hrE fun x hx => ?_
  have hopen : IsOpen {y : exteriorOpen n E.radius | R < ‖(y : EuclideanSpace ℝ (Fin n))‖} :=
    isOpen_lt continuous_const continuous_subtype_val.norm
  have hxmem : (⟨x, mem_exteriorOpen.mpr (by rwa [mem_sphere_zero_iff_norm.mp hx])⟩ :
      exteriorOpen n E.radius) ∈
      {y : exteriorOpen n E.radius | R < ‖(y : EuclideanSpace ℝ (Fin n))‖} := by
    simpa [mem_sphere_zero_iff_norm.mp hx] using hrR
  filter_upwards [hopen.mem_nhds hxmem] with y hy
  exact hφ y.1 (mem_exteriorOpen.mp y.2) hy

/-- Shrinking an AE end on a `C¹` manifold to a larger excision radius `R' ≥ E.radius` leaves
`normalizedCoordinateFlux` unchanged for every `r > R'`. -/
@[simp] theorem normalizedCoordinateFlux_restrictRadius [IsManifold (𝓡 n) 1 M]
    (E : AsymptoticallyEuclideanEnd n M t) {R' : ℝ}
    (hR' : E.radius ≤ R') {r : ℝ} (hr : R' < r) :
    normalizedCoordinateFlux n (E.restrictRadius hR').metricCoeff r =
      normalizedCoordinateFlux n E.metricCoeff r := by
  refine normalizedCoordinateFlux_congr_sphere fun x hx i j => ?_
  have hxr : R' < ‖x‖ := by rwa [mem_sphere_zero_iff_norm.mp hx]
  filter_upwards [(exteriorOpen n R').isOpen.mem_nhds (mem_exteriorOpen.mpr hxr)] with y hy
  exact E.restrictRadius_metricCoeff_of_lt hR' (mem_exteriorOpen.mp hy) i j

/-- Shrinking an AE end on a `C¹` manifold to a larger excision radius `R' ≥ E.radius` does not
change convergence of `normalizedCoordinateFlux` as `r → ∞`. -/
@[simp] theorem tendsto_normalizedCoordinateFlux_restrictRadius_iff [IsManifold (𝓡 n) 1 M]
    (E : AsymptoticallyEuclideanEnd n M t) {R' : ℝ} (hR' : E.radius ≤ R') (m : ℝ) :
    Tendsto (normalizedCoordinateFlux n (E.restrictRadius hR').metricCoeff) atTop (𝓝 m) ↔
      Tendsto (normalizedCoordinateFlux n E.metricCoeff) atTop (𝓝 m) := by
  refine tendsto_congr' ?_
  filter_upwards [eventually_gt_atTop R'] with r hr
  exact E.normalizedCoordinateFlux_restrictRadius hR' hr

/-- On any AE end `E` of order `t`, the coordinate ADM flux integrand on `sphere 0 r`
(`r > E.radius`) is uniformly `O(r ^ (-t - 1))`. -/
theorem exists_abs_coordinateFluxIntegrand_le (E : AsymptoticallyEuclideanEnd n M t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℝ}, E.radius < r →
      ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
        |coordinateFluxIntegrand n E.metricCoeff r x| ≤ C * r ^ (-t - 1) := by
  obtain ⟨C₀, hC₀⟩ := E.decay_metricCoeff
  let C₁ : ℝ := max C₀ 0
  refine ⟨2 * (n : ℝ) ^ 2 * C₁, by positivity, fun {r} hr x hx => ?_⟩
  have hr0 : 0 < r := E.radius_pos.trans hr
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
  have hxr : E.radius < ‖x‖ := hnorm.symm ▸ hr
  simpa only [mul_assoc] using
    abs_coordinateFluxIntegrand_le_of_norm_fderiv_le hr0 hx (B := C₁ * r ^ (-t - 1))
      fun i j => (hC₀ x hxr i j).2.1.trans <| by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (Real.rpow_nonneg hr0.le _)

/-- In dimension `n ≥ 2`, the normalized coordinate ADM flux of an AE end `E` of order `t` is
`O(r ^ (n - 2 - t))` for `r > E.radius` (in particular bounded at the Newtonian decay order
`t = n - 2`). -/
theorem exists_abs_normalizedCoordinateFlux_le (E : AsymptoticallyEuclideanEnd n M t)
    (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r : ℝ}, E.radius < r →
      |normalizedCoordinateFlux n E.metricCoeff r| ≤ C * r ^ ((n : ℝ) - 2 - t) := by
  obtain ⟨C₀, hC₀⟩ := E.decay_metricCoeff
  let C₁ : ℝ := max C₀ 0
  have hn1_pos : 0 < (n : ℝ) - 1 := sub_one_pos_of_two_le hn
  refine ⟨(n : ℝ) ^ 2 * C₁ / ((n : ℝ) - 1), by positivity, fun {r} hr => ?_⟩
  have hr0 : 0 < r := E.radius_pos.trans hr
  exact abs_normalizedCoordinateFlux_le_of_norm_fderiv_rpow_le hn hr0 fun x hx i j =>
    (hC₀ x (by rwa [mem_sphere_zero_iff_norm.mp hx]) i j).2.1.trans <|
      mul_le_mul_of_nonneg_right (le_max_left C₀ 0) (Real.rpow_nonneg (norm_nonneg x) _)

/-- **Faster-than-Newtonian decay implies zero ADM mass.** In dimension `n ≥ 2`, every AE end of
order `t > n - 2` has vanishing asymptotic coordinate ADM flux. -/
theorem tendsto_normalizedCoordinateFlux_zero_of_sub_lt (E : AsymptoticallyEuclideanEnd n M t)
    (hn : 2 ≤ n) (ht : (n : ℝ) - 2 < t) :
    Tendsto (normalizedCoordinateFlux n E.metricCoeff) atTop (𝓝 0) :=
  let ⟨_, hC⟩ := E.decay_metricCoeff
  tendsto_normalizedCoordinateFlux_zero_of_norm_fderiv_le hn ht fun x hx i j => (hC x hx i j).2.1

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
  rw [normalizedCoordinateFlux_eq_div_roundSphereVolume hn,
    setIntegral_congr_fun isClosed_sphere.measurableSet (fun x hx => hK x hx),
    setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one (n - 1) 0 hr,
    setIntegral_const,
    measureReal_euclideanHausdorffMeasure_euclideanSpace_sphere_zero_one hn,
    smul_eq_mul, smul_eq_mul]
  rw [show r ^ (n - 1) * (roundSphereVolume (n - 1) * K) =
      (r ^ (n - 1) * K) * roundSphereVolume (n - 1) by ring]
  exact mul_div_mul_right (r ^ (n - 1) * K) (2 * ((n : ℝ) - 1)) (roundSphereVolume_pos (n - 1)).ne'

/-- Constant metric coefficients have zero coordinate ADM flux integrand everywhere. -/
@[simp] theorem coordinateFluxIntegrand_const (n : ℕ) (c : Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun _ => c) r x = 0 := by
  simp [coordinateFluxIntegrand_def, fderiv_const_apply]

/-- Constant metric coefficients have zero normalized coordinate ADM flux at every radius. -/
@[simp] theorem normalizedCoordinateFlux_const (n : ℕ) (c : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun _ => c) r = 0 := by
  simp [normalizedCoordinateFlux_def]

/-- Zero metric coefficients have zero coordinate ADM flux integrand everywhere. -/
@[simp] theorem coordinateFluxIntegrand_zero (n : ℕ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n 0 r x = 0 := by
  simpa only [Pi.zero_def] using coordinateFluxIntegrand_const n 0 r x

/-- Zero metric coefficients have zero normalized coordinate ADM flux at every radius. -/
@[simp] theorem normalizedCoordinateFlux_zero (n : ℕ) (r : ℝ) :
    normalizedCoordinateFlux n 0 r = 0 := by
  simp [normalizedCoordinateFlux_def]

/-- Every continuous linear self-map `L` of flat `EuclideanSpace ℝ (Fin n)` has identically zero
coordinate ADM flux. -/
@[simp] theorem normalizedCoordinateFlux_pullbackMetricCoeff_continuousLinearMap (n : ℕ)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    normalizedCoordinateFlux n
      (pullbackMetricCoeff (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) r = 0 := by
  have h : pullbackMetricCoeff (L : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      fun _ i j =>
        ⟪L (EuclideanSpace.basisFun (Fin n) ℝ i), L (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ :=
    funext₃ (pullbackMetricCoeff_continuousLinearMap L)
  rw [h, normalizedCoordinateFlux_const]

/-- On flat `EuclideanSpace ℝ (Fin n)`, the identity chart has identically zero coordinate ADM
flux. -/
@[simp] theorem normalizedCoordinateFlux_pullbackMetricCoeff_id (n : ℕ) (r : ℝ) :
    normalizedCoordinateFlux n
      (pullbackMetricCoeff (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) r = 0 := by
  simpa only [ContinuousLinearMap.coe_id'] using
    normalizedCoordinateFlux_pullbackMetricCoeff_continuousLinearMap n
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) r

/-- Every linear isometry equivalence of flat `EuclideanSpace ℝ (Fin n)` has identically zero
coordinate ADM flux. -/
@[simp] theorem normalizedCoordinateFlux_pullbackMetricCoeff_linearIsometryEquiv (n : ℕ)
    (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    normalizedCoordinateFlux n
      (pullbackMetricCoeff (O : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))) r = 0 := by
  simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe] using
    normalizedCoordinateFlux_pullbackMetricCoeff_continuousLinearMap n
      O.toContinuousLinearEquiv.toContinuousLinearMap r

/-- On `AsymptoticallyEuclideanEnd.euclideanId`, the coordinate ADM flux vanishes for every
`r > R`. -/
@[simp] theorem AsymptoticallyEuclideanEnd.normalizedCoordinateFlux_euclideanId_of_lt (n : ℕ)
    {R : ℝ} (hR : 0 < R) (t : ℝ) {r : ℝ} (hr : R < r) :
    normalizedCoordinateFlux n (AsymptoticallyEuclideanEnd.euclideanId n hR t).metricCoeff r =
      0 := by
  let E := AsymptoticallyEuclideanEnd.euclideanId n hR t
  have hr' : E.radius < r := by simpa [E] using hr
  rw [E.normalizedCoordinateFlux_metricCoeff_eq (φ := id) hr'
      (fun _ _ => Eventually.of_forall fun _ => by simp [E]),
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

/-- Adding a constant background metric tensor `g₀` on the right leaves `coordinateFluxIntegrand`
unchanged. -/
@[simp] theorem coordinateFluxIntegrand_add_const (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (g₀ : Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => g y i j + g₀ i j) r x =
      coordinateFluxIntegrand n g r x := by
  simpa only [add_comm (g₀ _ _)] using coordinateFluxIntegrand_const_add n g₀ g r x

/-- Adding a constant background metric tensor `g₀` on the right leaves `normalizedCoordinateFlux`
unchanged. -/
@[simp] theorem normalizedCoordinateFlux_add_const (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (g₀ : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => g y i j + g₀ i j) r =
      normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_add_const]

/-- Subtracting a constant background metric tensor `g₀` leaves `coordinateFluxIntegrand`
unchanged. -/
@[simp] theorem coordinateFluxIntegrand_sub_const (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (g₀ : Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => g y i j - g₀ i j) r x =
      coordinateFluxIntegrand n g r x := by
  simpa only [sub_eq_add_neg] using
    coordinateFluxIntegrand_add_const n g (fun i j => -g₀ i j) r x

/-- Subtracting a constant background metric tensor `g₀` leaves `normalizedCoordinateFlux`
unchanged. -/
@[simp] theorem normalizedCoordinateFlux_sub_const (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (g₀ : Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => g y i j - g₀ i j) r =
      normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_sub_const]

/-- Multiplying metric coefficients by a real constant `c` multiplies `coordinateFluxIntegrand` by
`c`, without any differentiability hypothesis. -/
@[simp] theorem coordinateFluxIntegrand_const_mul (n : ℕ) (c : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => c * g y i j) r x =
      c * coordinateFluxIntegrand n g r x := by
  have hsmul (i j : Fin n) :
      fderiv ℝ (fun y => c * g y i j) x = c • fderiv ℝ (fun y => g y i j) x :=
    congrFun (fderiv_const_smul_field (f := fun y => g y i j) c) x
  simp only [coordinateFluxIntegrand_def, hsmul, smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Multiplying metric coefficients by `c : ℝ` multiplies `normalizedCoordinateFlux` by `c`. -/
@[simp] theorem normalizedCoordinateFlux_const_mul (n : ℕ) (c : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => c * g y i j) r =
      c * normalizedCoordinateFlux n g r := by
  simp only [normalizedCoordinateFlux_def, coordinateFluxIntegrand_const_mul, integral_const_mul,
    mul_div_assoc]

/-- Negating metric coefficients negates `coordinateFluxIntegrand`, without any differentiability
hypothesis. -/
@[simp] theorem coordinateFluxIntegrand_neg (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (fun y i j => -g y i j) r x =
      -coordinateFluxIntegrand n g r x := by
  simpa only [neg_one_mul] using coordinateFluxIntegrand_const_mul n (-1) g r x

/-- Negating metric coefficients negates `normalizedCoordinateFlux`. -/
@[simp] theorem normalizedCoordinateFlux_neg (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (r : ℝ) :
    normalizedCoordinateFlux n (fun y i j => -g y i j) r =
      -normalizedCoordinateFlux n g r := by
  simpa only [neg_one_mul] using normalizedCoordinateFlux_const_mul n (-1) g r

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

/-- Pointwise subtraction of `coordinateFluxIntegrand` for metric coefficients differentiable at
`x`. -/
theorem coordinateFluxIntegrand_sub {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg₁ : ∀ i j, DifferentiableAt ℝ (fun y => g₁ y i j) x)
    (hg₂ : ∀ i j, DifferentiableAt ℝ (fun y => g₂ y i j) x) (r : ℝ) :
    coordinateFluxIntegrand n (fun y i j => g₁ y i j - g₂ y i j) r x =
      coordinateFluxIntegrand n g₁ r x - coordinateFluxIntegrand n g₂ r x := by
  have hg₂' : ∀ i j, DifferentiableAt ℝ (fun y => -g₂ y i j) x := fun i j => (hg₂ i j).neg
  simpa only [sub_eq_add_neg, coordinateFluxIntegrand_neg] using
    coordinateFluxIntegrand_add (g₂ := fun y i j => -g₂ y i j) hg₁ hg₂' r

/-- Subtraction of `normalizedCoordinateFlux` on `sphere 0 r` when `g₁` and `g₂` are
differentiable at every point of `sphere 0 r` and their flux integrands are integrable there. -/
theorem normalizedCoordinateFlux_sub {n : ℕ}
    {g₁ g₂ : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r : ℝ}
    (hg₁ : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, DifferentiableAt ℝ (fun y => g₁ y i j) x)
    (hg₂ : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, DifferentiableAt ℝ (fun y => g₂ y i j) x)
    (hint₁ : IntegrableOn (coordinateFluxIntegrand n g₁ r)
      (sphere (0 : EuclideanSpace ℝ (Fin n)) r) μHE[n - 1])
    (hint₂ : IntegrableOn (coordinateFluxIntegrand n g₂ r)
      (sphere (0 : EuclideanSpace ℝ (Fin n)) r) μHE[n - 1]) :
    normalizedCoordinateFlux n (fun y i j => g₁ y i j - g₂ y i j) r =
      normalizedCoordinateFlux n g₁ r - normalizedCoordinateFlux n g₂ r := by
  have hg₂' : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r,
      ∀ i j, DifferentiableAt ℝ (fun y => -g₂ y i j) x := fun x hx i j => (hg₂ x hx i j).neg
  have hint₂' : IntegrableOn (coordinateFluxIntegrand n (fun y i j => -g₂ y i j) r)
      (sphere (0 : EuclideanSpace ℝ (Fin n)) r) μHE[n - 1] := by
    have hfun : coordinateFluxIntegrand n (fun y i j => -g₂ y i j) r =
        -coordinateFluxIntegrand n g₂ r := funext fun x => coordinateFluxIntegrand_neg n g₂ r x
    rw [hfun]
    exact hint₂.neg
  simpa only [sub_eq_add_neg, normalizedCoordinateFlux_neg] using
    normalizedCoordinateFlux_add (g₂ := fun y i j => -g₂ y i j) hg₁ hg₂' hint₁ hint₂'

/-! ### Conformally flat metrics and radial flux formula -/

/-- Conformally flat metric coefficients `g_ij(x) = w(x) δ_ij` on `EuclideanSpace ℝ (Fin n)`. -/
def conformallyFlatMetricCoeff {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) : ℝ :=
  if i = j then w x else 0

theorem conformallyFlatMetricCoeff_def {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n) :
    conformallyFlatMetricCoeff w x i j = if i = j then w x else 0 := (rfl)

@[simp] theorem conformallyFlatMetricCoeff_diag {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    conformallyFlatMetricCoeff w x i i = w x := by
  simp [conformallyFlatMetricCoeff]

@[simp] theorem conformallyFlatMetricCoeff_of_ne {n : ℕ} (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) {i j : Fin n} (h : i ≠ j) :
    conformallyFlatMetricCoeff w x i j = 0 := by
  simp [conformallyFlatMetricCoeff, h]

/-- **Conformally flat coordinate flux integrand.** For `g_ij = w δ_ij`, the coordinate ADM flux
integrand at `x` equals `-((n - 1) / r) * fderiv ℝ w x x`. -/
theorem coordinateFluxIntegrand_conformallyFlatMetricCoeff {n : ℕ}
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand n (conformallyFlatMetricCoeff w) r x =
      -(((n : ℝ) - 1) / r) * fderiv ℝ w x x := by
  have hsum_i (j : Fin n) :
      ∑ i : Fin n,
        (fderiv ℝ (fun y => conformallyFlatMetricCoeff w y i j) x
            (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => conformallyFlatMetricCoeff w y i i) x
            (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        -((n : ℝ) - 1) * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j) := by
    have hterm (i : Fin n) :
        fderiv ℝ (fun y => conformallyFlatMetricCoeff w y i j) x
            (EuclideanSpace.basisFun (Fin n) ℝ i) -
          fderiv ℝ (fun y => conformallyFlatMetricCoeff w y i i) x
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
  simpa only [EuclideanSpace.basisFun_repr, map_sum, map_smul, smul_eq_mul] using
    congrArg (fderiv ℝ w x) ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x)

/-- On `sphere 0 r` (`r > 0`), the radial conformally flat metric `g_ij(y) = ψ(‖y‖) δ_ij` has
constant coordinate flux integrand `-(n - 1) * deriv ψ r`. -/
theorem coordinateFluxIntegrand_conformallyFlatMetricCoeff_radial {n : ℕ} {ψ : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hψ : DifferentiableAt ℝ ψ r) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r) :
    coordinateFluxIntegrand n (conformallyFlatMetricCoeff (fun y => ψ ‖y‖)) r x =
      -((n : ℝ) - 1) * deriv ψ r := by
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
  have hx_ne : x ≠ 0 := norm_pos_iff.mp (hnorm.symm ▸ hr)
  have hdn : DifferentiableAt ℝ (‖·‖) x := differentiableAt_id.norm ℝ hx_ne
  have hψx : DifferentiableAt ℝ ψ ‖x‖ := hnorm.symm ▸ hψ
  have hcomp : HasFDerivAt (ψ ∘ norm)
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv ψ ‖x‖)).comp (fderiv ℝ (‖·‖) x)) x :=
    hψx.hasDerivAt.hasFDerivAt.comp x hdn.hasFDerivAt
  rw [← Function.comp_def ψ norm, coordinateFluxIntegrand_conformallyFlatMetricCoeff, hcomp.fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    hdn.fderiv_norm_self, hnorm, smul_eq_mul]
  field_simp [hr.ne']

/-- **Radial conformally flat ADM flux formula.** In dimension `n ≥ 2`, for `r > 0` and `ψ : ℝ → ℝ`
differentiable at `r`, the normalized coordinate ADM flux of `g_ij(y) = ψ(‖y‖) δ_ij` at radius `r`
equals `-(r ^ (n - 1) * deriv ψ r) / 2`. -/
theorem normalizedCoordinateFlux_conformallyFlatMetricCoeff_radial {n : ℕ} (hn : 2 ≤ n)
    {ψ : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hψ : DifferentiableAt ℝ ψ r) :
    normalizedCoordinateFlux n (conformallyFlatMetricCoeff (fun y => ψ ‖y‖)) r =
      -(r ^ (n - 1) * deriv ψ r) / 2 := by
  rw [normalizedCoordinateFlux_of_eqOn_const (by omega) hr
    (fun x hx => coordinateFluxIntegrand_conformallyFlatMetricCoeff_radial hr hψ hx)]
  field_simp [(sub_one_pos_of_two_le hn).ne']

/-! ### Model metrics: harmonic-conformal, Schwarzschild, and radial tensor perturbation -/

/-- The harmonic-conformal model metric coefficients `(1 + c / ‖x‖ ^ (n - 2)) ^ (4 / (n - 2)) δ_ij`
on `EuclideanSpace ℝ (Fin n)`. -/
def harmonicConformalMetricCoeff (n : ℕ) (c : ℝ) :
    EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ :=
  conformallyFlatMetricCoeff (fun y => (1 + c / ‖y‖ ^ (n - 2)) ^ (4 / ((n : ℝ) - 2)))

theorem harmonicConformalMetricCoeff_def (n : ℕ) (c : ℝ) :
    harmonicConformalMetricCoeff n c =
      conformallyFlatMetricCoeff (fun y => (1 + c / ‖y‖ ^ (n - 2)) ^ (4 / ((n : ℝ) - 2))) := (rfl)

/-- **Exact finite-radius coordinate ADM flux of the harmonic-conformal model.** For `3 ≤ n`,
`0 < r`, and `0 < 1 + c / r ^ (n - 2)`, the normalized coordinate ADM flux equals
`2 c (1 + c / r ^ (n - 2)) ^ (4 / (n - 2) - 1)`. -/
theorem normalizedCoordinateFlux_harmonicConformalMetricCoeff {n : ℕ} (hn : 3 ≤ n) (c : ℝ) {r : ℝ}
    (hr : 0 < r) (hu : 0 < 1 + c / r ^ (n - 2)) :
    normalizedCoordinateFlux n (harmonicConformalMetricCoeff n c) r =
      2 * c * (1 + c / r ^ (n - 2)) ^ (4 / ((n : ℝ) - 2) - 1) := by
  set k : ℕ := n - 2 with hk_def
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
  rw [harmonicConformalMetricCoeff_def, ← hk_def,
    normalizedCoordinateFlux_conformallyFlatMetricCoeff_radial (by omega) hr hψ.differentiableAt,
    hψ.deriv]
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
theorem tendsto_normalizedCoordinateFlux_harmonicConformalMetricCoeff {n : ℕ} (hn : 3 ≤ n)
    (c : ℝ) :
    Tendsto (normalizedCoordinateFlux n (harmonicConformalMetricCoeff n c)) atTop (𝓝 (2 * c)) := by
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
  exact (normalizedCoordinateFlux_harmonicConformalMetricCoeff hn c hr hu_pos).symm

/-- The spatial Schwarzschild metric coefficients
`(1 + m / (2 ‖x‖ ^ (n - 2))) ^ (4 / (n - 2)) δ_ij` of mass parameter `m` in dimension `n`
(Cecchini–Zeidler, Example 2.2). -/
def schwarzschildMetricCoeff (n : ℕ) (m : ℝ) :
    EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ :=
  conformallyFlatMetricCoeff (fun y => (1 + m / (2 * ‖y‖ ^ (n - 2))) ^ (4 / ((n : ℝ) - 2)))

theorem schwarzschildMetricCoeff_def (n : ℕ) (m : ℝ) :
    schwarzschildMetricCoeff n m =
      conformallyFlatMetricCoeff
        (fun y => (1 + m / (2 * ‖y‖ ^ (n - 2))) ^ (4 / ((n : ℝ) - 2))) := (rfl)

/-- The spatial Schwarzschild metric of mass `m` is the harmonic-conformal model with
`c = m / 2`. -/
theorem schwarzschildMetricCoeff_eq_harmonicConformalMetricCoeff (n : ℕ) (m : ℝ) :
    schwarzschildMetricCoeff n m = harmonicConformalMetricCoeff n (m / 2) := by
  ext y i j
  simp only [schwarzschildMetricCoeff_def, harmonicConformalMetricCoeff_def,
    conformallyFlatMetricCoeff_def, div_div]

/-- **Exact finite-radius coordinate ADM flux of the spatial Schwarzschild metric.** -/
theorem normalizedCoordinateFlux_schwarzschildMetricCoeff {n : ℕ} (hn : 3 ≤ n) (m : ℝ) {r : ℝ}
    (hr : 0 < r) (hu : 0 < 1 + m / (2 * r ^ (n - 2))) :
    normalizedCoordinateFlux n (schwarzschildMetricCoeff n m) r =
      m * (1 + m / (2 * r ^ (n - 2))) ^ (4 / ((n : ℝ) - 2) - 1) := by
  have hu' : 0 < 1 + m / 2 / r ^ (n - 2) := by rwa [div_div]
  rw [schwarzschildMetricCoeff_eq_harmonicConformalMetricCoeff,
    normalizedCoordinateFlux_harmonicConformalMetricCoeff hn (m / 2) hr hu', div_div]
  ring

/-- **ADM mass of the spatial Schwarzschild metric** (Cecchini–Zeidler, Example 2.2). For `3 ≤ n`
and any `m : ℝ`, the normalized coordinate ADM flux of `schwarzschildMetricCoeff n m` converges to
`m` as `r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_schwarzschildMetricCoeff {n : ℕ} (hn : 3 ≤ n) (m : ℝ) :
    Tendsto (normalizedCoordinateFlux n (schwarzschildMetricCoeff n m)) atTop (𝓝 m) := by
  rw [schwarzschildMetricCoeff_eq_harmonicConformalMetricCoeff]
  simpa only [mul_div_cancel₀ m (two_ne_zero' ℝ)] using
    tendsto_normalizedCoordinateFlux_harmonicConformalMetricCoeff hn (m / 2)

/-- The non-conformal radial tensor perturbation `g_ij(x) = δ_ij + ε x_i x_j / ‖x‖ ^ n` on
`EuclideanSpace ℝ (Fin n)`. -/
def radialTensorPerturbMetricCoeff (n : ℕ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) : ℝ :=
  (if i = j then 1 else 0) + ε * (x i * x j / ‖x‖ ^ n)

theorem radialTensorPerturbMetricCoeff_def (n : ℕ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    radialTensorPerturbMetricCoeff n ε x i j =
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
theorem coordinateFluxIntegrand_radialTensorPerturbMetricCoeff {n : ℕ} (ε : ℝ) {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) r) :
    coordinateFluxIntegrand n (radialTensorPerturbMetricCoeff n ε) r x =
      ε * ((n : ℝ) - 1) / r ^ (n - 1) := by
  have hnorm : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
  have hx_ne : x ≠ 0 := norm_pos_iff.mp (hnorm.symm ▸ hr)
  have hn : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => hx_ne (by subst h0; exact Subsingleton.elim x 0)
  let q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ := fun y i j => y i * y j / ‖y‖ ^ n
  have hdecomp : radialTensorPerturbMetricCoeff n ε =
      fun y i j => (if i = j then (1 : ℝ) else 0) + ε * q y i j :=
    funext₃ (radialTensorPerturbMetricCoeff_def n ε)
  rw [hdecomp, coordinateFluxIntegrand_const_add, coordinateFluxIntegrand_const_mul]
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
theorem normalizedCoordinateFlux_radialTensorPerturbMetricCoeff {n : ℕ} (hn : 2 ≤ n) (ε : ℝ)
    {r : ℝ} (hr : 0 < r) :
    normalizedCoordinateFlux n (radialTensorPerturbMetricCoeff n ε) r = ε / 2 := by
  have hrn1 : r ^ (n - 1) ≠ 0 := pow_ne_zero (n - 1) hr.ne'
  rw [normalizedCoordinateFlux_of_eqOn_const (by omega) hr
    (fun x hx => coordinateFluxIntegrand_radialTensorPerturbMetricCoeff ε hr hx)]
  field_simp [(sub_one_pos_of_two_le hn).ne', hrn1]

/-- **ADM mass of the non-conformal radial tensor perturbation.** For `2 ≤ n` and `ε : ℝ`, the
normalized coordinate ADM flux of `δ_ij + ε x_i x_j / ‖x‖ ^ n` converges to `ε / 2` as `r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_radialTensorPerturbMetricCoeff {n : ℕ} (hn : 2 ≤ n)
    (ε : ℝ) :
    Tendsto (normalizedCoordinateFlux n (radialTensorPerturbMetricCoeff n ε)) atTop
      (𝓝 (ε / 2)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (normalizedCoordinateFlux_radialTensorPerturbMetricCoeff hn ε hr).symm

end TauCeti
