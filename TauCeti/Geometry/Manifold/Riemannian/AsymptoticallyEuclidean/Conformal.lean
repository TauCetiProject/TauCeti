/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Flux
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The ADM flux under a conformal change

Let `g_ij` be the metric coefficients of an asymptotically Euclidean end of an `n`-dimensional
Riemannian manifold, `n ≥ 3`, and let `u` be a function on the end with

`u = 1 + c |x| ^ (2 - n) + o(|x| ^ (2 - n))`, `∇u = c ∇(|x| ^ (2 - n)) + o(|x| ^ (1 - n))`

as `|x| → ∞`. The conformal metric `u ^ (4 / (n - 2)) g` has coefficients
`u ^ (4 / (n - 2)) g_ij`. This file proves that the normalized coordinate fluxes
(`TauCeti.normalizedCoordinateFlux`) of these coefficients and of `g_ij` at radius `r` differ by
`2 c + o(1)` as `r → ∞`. In particular, if `g` has mass `m` at the end, then
`u ^ (4 / (n - 2)) g` has mass `m + 2 c` there. Of the expansion of `u` itself only
`u - 1 = O(|x| ^ (2 - n))` is used. For `g` Euclidean and `u = 1 + c |x| ^ (2 - n)` this is the
mass `2 c` of the metric `(1 + c |x| ^ (2 - n)) ^ (4 / (n - 2)) δ`
(`TauCeti.tendsto_normalizedCoordinateFlux_conformal_one_add_mul_rpow`). In particular the limit
`u → 1` alone does not determine the change of the mass: these factors all tend to `1`, and the
change `2 c` is read off from the coefficient of `|x| ^ (2 - n)`.

The computation is carried out for a general factor `w`. By the product rule
(`TauCeti.coordinateFluxIntegrand_mul`), the flux density of `w g_ij` is `w` times that of `g`
plus `Σ_j (Σ_i (∂_i w g_ij - ∂_j w g_ii)) x_j / |x|`. As `g_ij → δ_ij`, the second term is the
radial derivative `(1 - n) ∂_r w` up to `o(|x| ^ (1 - n))`. If `w - 1 = O(|x| ^ (2 - n))` and
`∇w = a ∇(|x| ^ (2 - n)) + o(|x| ^ (1 - n))`, the flux densities therefore differ by
`(n - 1)(n - 2) a |x| ^ (1 - n) + o(|x| ^ (1 - n))`, and the normalized fluxes by
`(n - 2) a / 2 + o(1)`. For `w = u ^ p` one has `a = p c`, and `p = 4 / (n - 2)` gives `2 c`.

All asymptotic hypotheses are stated along `Bornology.cobounded`, that is as `|x| → ∞`. On the
coefficients `g_ij` they ask that `g_ij → δ_ij` and `∂g_ij = o(|x|⁻¹)`, which holds on an
asymptotically Euclidean end of any positive order
(`TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_pullbackMetricCoeff` and
`TauCeti.IsAsymptoticallyEuclideanEnd.isLittleO_fderiv_pullbackMetricCoeff`).

## Main results

* `TauCeti.isLittleO_coordinateFluxIntegrand_mul_sub`: the flux densities of `w g_ij` and `g_ij`
  differ by `(n - 1)(n - 2) a |x| ^ (1 - n) + o(|x| ^ (1 - n))`.
* `TauCeti.tendsto_normalizedCoordinateFlux_mul_sub`: their normalized fluxes differ by
  `(n - 2) a / 2 + o(1)`.
* `TauCeti.tendsto_normalizedCoordinateFlux_rpow_mul_sub`: for the factor `u ^ p`, the normalized
  fluxes differ by `(n - 2) p c / 2 + o(1)`.
* `TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_normalizedCoordinateFlux_rpow_mul_sub` and
  `TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_normalizedCoordinateFlux_rpow_mul`: on an
  asymptotically Euclidean end of positive order, the conformal factor `u ^ (4 / (n - 2))` changes
  the normalized flux by `2 c + o(1)`, and a mass `m` into the mass `m + 2 c`.

## References

* S. Cecchini, R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, arXiv:2108.11972, equation (2.1) and Example 2.2.
* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §8 and §9.
* R. Schoen, S.-T. Yau, *Positive scalar curvature and minimal hypersurface singularities*,
  arXiv:1704.05490, §5.
-/

public section

noncomputable section

open MeasureTheory Measure Metric Set Filter Asymptotics Bornology Module Bundle
open scoped Topology Manifold

namespace TauCeti

variable {n : ℕ}

/-! ### Asymptotic estimates -/

/-- A function whose derivative is `a ∇(|x| ^ (2 - n)) + o(|x| ^ (1 - n))` has derivative
`O(|x| ^ (1 - n))`. -/
private theorem isBigO_fderiv_of_isLittleO {w : EuclideanSpace ℝ (Fin n) → ℝ} {a : ℝ}
    (hw : (fun x ↦ fderiv ℝ w x - a • fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x) =o[cobounded _]
      fun x ↦ ‖x‖ ^ (1 - n : ℝ)) :
    (fun x ↦ fderiv ℝ w x) =O[cobounded _] fun x ↦ ‖x‖ ^ (1 - n : ℝ) :=
  (hw.isBigO.add (((isBigO_fderiv_norm_rpow_cobounded (2 - n : ℝ)).congr_right fun x ↦ by
    ring_nf).const_smul_left a)).congr_left fun x ↦ by simp

/-- The flux density of the conformally changed coefficients `w g_ij`, minus that of `g` and the
leading term `(n - 1)(n - 2) a |x| ^ (1 - n)`, split into three error terms. -/
private theorem coordinateFluxIntegrand_mul_sub_eq {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)} (a : ℝ)
    (hw : DifferentiableAt ℝ w x) (hg : ∀ i j, DifferentiableAt ℝ (fun y ↦ g y i j) x)
    (hx : x ≠ 0) :
    coordinateFluxIntegrand (fun y i j ↦ w y * g y i j) x - coordinateFluxIntegrand g x -
        (n - 1) * (n - 2) * a * ‖x‖ ^ (1 - n : ℝ) =
      (w x - 1) * coordinateFluxIntegrand g x +
        ∑ j, (∑ i, (fderiv ℝ w x (EuclideanSpace.single i 1) * (g x i j - if i = j then 1 else 0) -
          fderiv ℝ w x (EuclideanSpace.single j 1) * (g x i i - 1))) * (x j / ‖x‖) +
        (1 - n) * ((fderiv ℝ w x - a • fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x) x / ‖x‖) := by
  set L := fderiv ℝ w x
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  -- The radial derivative of `|x| ^ (2 - n)` is `(2 - n) |x| ^ (1 - n)`.
  have hP : fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x x / ‖x‖ = (2 - n) * ‖x‖ ^ (1 - n : ℝ) := by
    rw [fderiv_norm_rpow_of_ne _ hx, smul_apply, innerSL_apply_apply, real_inner_self_eq_norm_sq,
      smul_eq_mul, div_eq_iff hx'.ne', mul_assoc, mul_assoc, ← Real.rpow_natCast,
      ← Real.rpow_add hx', ← Real.rpow_add_one hx'.ne']
    ring_nf
  -- The product-rule term of `w δ_ij` is `(1 - n) ∂_r w`.
  have hδ : ∑ j, (∑ i, ((if i = j then L (EuclideanSpace.single i 1) else 0) -
      L (EuclideanSpace.single j 1))) * (x j / ‖x‖) = (1 - n) * (L x / ‖x‖) := by
    have h := coordinateFluxIntegrand_mul (g := fun _ i j ↦ if i = j then 1 else 0) hw
      fun _ _ ↦ differentiableAt_const _
    simp only [coordinateFluxIntegrand_const, mul_zero, zero_add, mul_ite, mul_one,
      ↓reduceIte, coordinateFluxIntegrand_conformal] at h
    exact h.symm
  -- Splitting `g_ij = δ_ij + (g_ij - δ_ij)` in the product-rule term leaves `(1 - n) ∂_r w`.
  have hS : ∑ j, (∑ i, (L (EuclideanSpace.single i 1) * g x i j -
      L (EuclideanSpace.single j 1) * g x i i)) * (x j / ‖x‖) -
      ∑ j, (∑ i, (L (EuclideanSpace.single i 1) * (g x i j - if i = j then 1 else 0) -
        L (EuclideanSpace.single j 1) * (g x i i - 1))) * (x j / ‖x‖) =
      (1 - n) * (L x / ‖x‖) := by
    rw [← hδ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> ring
  rw [coordinateFluxIntegrand_mul hw hg, _root_.sub_apply, smul_apply, smul_eq_mul, sub_div,
    mul_div_assoc, hP]
  linear_combination hS

/-! ### The flux under a conformal change -/

/-- **The flux density under a conformal change.** Let `g` be coefficients with `g_ij → δ_ij` and
`∂g_ij = o(|x|⁻¹)` at infinity, and let `w` be a factor with `w - 1 = O(|x| ^ (2 - n))` and
`∇w = a ∇(|x| ^ (2 - n)) + o(|x| ^ (1 - n))`. Then the flux densities of `w g_ij` and of `g_ij`
differ by `(n - 1)(n - 2) a |x| ^ (1 - n) + o(|x| ^ (1 - n))`. -/
theorem isLittleO_coordinateFluxIntegrand_mul_sub {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {a : ℝ}
    (hgd : ∀ᶠ x in cobounded _, ∀ i j, DifferentiableAt ℝ (fun y ↦ g y i j) x)
    (hg0 : ∀ i j, Tendsto (fun x ↦ g x i j) (cobounded _) (𝓝 (if i = j then 1 else 0)))
    (hg1 : ∀ i j, (fun x ↦ fderiv ℝ (fun y ↦ g y i j) x) =o[cobounded _] fun x ↦ ‖x‖⁻¹)
    (hwd : ∀ᶠ x in cobounded _, DifferentiableAt ℝ w x)
    (hw0 : (fun x ↦ w x - 1) =O[cobounded _] fun x ↦ ‖x‖ ^ (2 - n : ℝ))
    (hw1 : (fun x ↦ fderiv ℝ w x - a • fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x) =o[cobounded _]
      fun x ↦ ‖x‖ ^ (1 - n : ℝ)) :
    (fun x ↦ coordinateFluxIntegrand (fun y i j ↦ w y * g y i j) x - coordinateFluxIntegrand g x -
      (n - 1) * (n - 2) * a * ‖x‖ ^ (1 - n : ℝ)) =o[cobounded _] fun x ↦ ‖x‖ ^ (1 - n : ℝ) := by
  have hx0 : ∀ᶠ x : EuclideanSpace ℝ (Fin n) in cobounded _, 0 < ‖x‖ :=
    tendsto_norm_cobounded_atTop.eventually_gt_atTop 0
  -- `(w - 1) · (flux density of g)` is `O(|x| ^ (2 - n)) · o(|x|⁻¹)`.
  have h1 : (fun x ↦ (w x - 1) * coordinateFluxIntegrand g x) =o[cobounded _]
      fun x ↦ ‖x‖ ^ (1 - n : ℝ) := by
    refine (hw0.mul_isLittleO (isLittleO_coordinateFluxIntegrand hg1)).congr' EventuallyEq.rfl ?_
    filter_upwards [hx0] with x hx
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
    ring_nf
  -- The terms with `g_ij - δ_ij` are `O(|x| ^ (1 - n)) · o(1)`.
  have hh (i j : Fin n) : (fun x ↦ g x i j - if i = j then 1 else 0) =o[cobounded _]
      fun _ ↦ (1 : ℝ) :=
    (isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 (hg0 i j))
  have hDe (k : Fin n) : (fun x ↦ fderiv ℝ w x (EuclideanSpace.single k 1)) =O[cobounded _]
      fun x ↦ ‖x‖ ^ (1 - n : ℝ) :=
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k 1)).isBigO_comp _ _).trans
      (isBigO_fderiv_of_isLittleO hw1)
  have h2 : (fun x ↦ ∑ j, (∑ i, (fderiv ℝ w x (EuclideanSpace.single i 1) *
      (g x i j - if i = j then 1 else 0) - fderiv ℝ w x (EuclideanSpace.single j 1) *
        (g x i i - 1))) * (x j / ‖x‖)) =o[cobounded _] fun x ↦ ‖x‖ ^ (1 - n : ℝ) := by
    refine IsLittleO.fun_sum fun j _ ↦ ?_
    simpa using (IsLittleO.fun_sum fun i _ ↦ ((hDe i).mul_isLittleO (hh i j)).sub
      ((hDe j).mul_isLittleO ((hh i i).congr_left fun x ↦ by simp))).mul_isBigO
        (isBigO_apply_div_norm _ j)
  -- The radial derivative of `w - a |x| ^ (2 - n)` is `o(|x| ^ (1 - n))`.
  have h3 : (fun x ↦ (1 - n : ℝ) * ((fderiv ℝ w x - a • fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x) x /
      ‖x‖)) =o[cobounded _] fun x ↦ ‖x‖ ^ (1 - n : ℝ) :=
    (((isBigO_inv_norm_smul_apply _ _ id).trans_isLittleO hw1).congr_left fun x ↦ by
      rw [id, smul_eq_mul, inv_mul_eq_div]).const_mul_left _
  refine ((h1.add h2).add h3).congr' ?_ EventuallyEq.rfl
  filter_upwards [hgd, hwd, hx0] with x hg hw hx
  exact (coordinateFluxIntegrand_mul_sub_eq a hw hg (norm_pos_iff.1 hx)).symm

/-- At a radius `r > 0` where the flux densities are integrable on the sphere, the normalized
fluxes of `w g_ij` and of `g_ij` differ by `(n - 2) a / 2` plus the normalized sphere integral of
the error term of `TauCeti.isLittleO_coordinateFluxIntegrand_mul_sub`. -/
private theorem normalizedCoordinateFlux_mul_sub_eq (hn : 2 ≤ n) {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} (a : ℝ) {r : ℝ} (hr : 0 < r)
    (hig : IntegrableOn (coordinateFluxIntegrand g) (sphere 0 r) μHE[n - 1])
    (hiF : IntegrableOn (fun x ↦ coordinateFluxIntegrand (fun y i j ↦ w y * g y i j) x -
      coordinateFluxIntegrand g x - (n - 1) * (n - 2) * a * ‖x‖ ^ (1 - n : ℝ)) (sphere 0 r)
        μHE[n - 1]) :
    normalizedCoordinateFlux (fun y i j ↦ w y * g y i j) r - normalizedCoordinateFlux g r =
      (∫ x in sphere 0 r, (coordinateFluxIntegrand (fun y i j ↦ w y * g y i j) x -
        coordinateFluxIntegrand g x - (n - 1) * (n - 2) * a * ‖x‖ ^ (1 - n : ℝ)) ∂μHE[n - 1]) /
          (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) + (n - 2) * a / 2 := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hS := roundSphereVolume_pos (n - 1)
  have hE : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n - 1 + 1 := by
    rw [finrank_euclideanSpace_fin]
    omega
  set K : ℝ := (n - 1) * (n - 2) * a
  have hμ := euclideanHausdorffMeasure_sphere_eq_ofReal_pow_mul_roundSphereVolume hE 0 hr
  -- On the sphere of radius `r` the leading term is the constant `K r ^ (1 - n)`.
  have hK : EqOn (fun x : EuclideanSpace ℝ (Fin n) ↦ K * ‖x‖ ^ (1 - n : ℝ))
      (fun _ ↦ K * r ^ (1 - n : ℝ)) (sphere 0 r) := fun x hx ↦ by
    simp only [mem_sphere_zero_iff_norm.1 hx]
  have hiK : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) ↦ K * ‖x‖ ^ (1 - n : ℝ))
      (sphere 0 r) μHE[n - 1] :=
    (integrableOn_const (by rw [hμ]; exact ENNReal.ofReal_ne_top)).congr_fun hK.symm
      isClosed_sphere.measurableSet
  have hiW : IntegrableOn (coordinateFluxIntegrand fun y i j ↦ w y * g y i j) (sphere 0 r)
      μHE[n - 1] :=
    ((hiF.add hig).add hiK).congr_fun (fun x _ ↦ by simp only [Pi.add_apply]; ring)
      isClosed_sphere.measurableSet
  have hKint : ∫ x in sphere (0 : EuclideanSpace ℝ (Fin n)) r, K * ‖x‖ ^ (1 - n : ℝ) ∂μHE[n - 1] =
      K * r ^ (1 - n : ℝ) * (r ^ (n - 1) * roundSphereVolume (n - 1)) := by
    rw [setIntegral_congr_fun isClosed_sphere.measurableSet hK, setIntegral_const,
      measureReal_def, hμ, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, mul_comm]
  have hpow : r ^ (1 - n : ℝ) * r ^ (n - 1) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hr, Nat.cast_sub (by omega), Nat.cast_one]
    simp
  have hsplit : ∫ x in sphere 0 r, (coordinateFluxIntegrand (fun y i j ↦ w y * g y i j) x -
      coordinateFluxIntegrand g x) ∂μHE[n - 1] =
      (∫ x in sphere 0 r, (coordinateFluxIntegrand (fun y i j ↦ w y * g y i j) x -
        coordinateFluxIntegrand g x - K * ‖x‖ ^ (1 - n : ℝ)) ∂μHE[n - 1]) +
          K * roundSphereVolume (n - 1) := by
    have hKS : K * r ^ (1 - n : ℝ) * (r ^ (n - 1) * roundSphereVolume (n - 1)) =
        K * roundSphereVolume (n - 1) := by
      rw [← mul_assoc, mul_assoc K, hpow, mul_one]
    rw [← hKS, ← hKint, ← integral_add hiF hiK]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ by ring)
  rw [normalizedCoordinateFlux_def, normalizedCoordinateFlux_def, ← sub_div, ← integral_sub hiW hig,
    hsplit]
  field_simp
  ring

/-- **The flux under a conformal change.** For `n ≥ 2`, let `g` be coefficients with
`g_ij → δ_ij` and `∂g_ij = o(|x|⁻¹)` at infinity, and let `w` be a factor with
`w - 1 = O(|x| ^ (2 - n))` and `∇w = a ∇(|x| ^ (2 - n)) + o(|x| ^ (1 - n))`. Then the normalized
fluxes of `w g_ij` and of `g_ij` at radius `r` differ by `(n - 2) a / 2 + o(1)` as `r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_mul_sub (hn : 2 ≤ n) {w : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {a : ℝ}
    (hgd : ∀ᶠ x in cobounded _, ∀ i j, DifferentiableAt ℝ (fun y ↦ g y i j) x)
    (hg0 : ∀ i j, Tendsto (fun x ↦ g x i j) (cobounded _) (𝓝 (if i = j then 1 else 0)))
    (hg1 : ∀ i j, (fun x ↦ fderiv ℝ (fun y ↦ g y i j) x) =o[cobounded _] fun x ↦ ‖x‖⁻¹)
    (hwd : ∀ᶠ x in cobounded _, DifferentiableAt ℝ w x)
    (hw0 : (fun x ↦ w x - 1) =O[cobounded _] fun x ↦ ‖x‖ ^ (2 - n : ℝ))
    (hw1 : (fun x ↦ fderiv ℝ w x - a • fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x) =o[cobounded _]
      fun x ↦ ‖x‖ ^ (1 - n : ℝ)) :
    Tendsto (fun r ↦ normalizedCoordinateFlux (fun y i j ↦ w y * g y i j) r -
      normalizedCoordinateFlux g r) atTop (𝓝 ((n - 2) * a / 2)) := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hE : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n - 1 + 1 := by
    rw [finrank_euclideanSpace_fin]
    omega
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ coordinateFluxIntegrand
    (fun y i j ↦ w y * g y i j) x - coordinateFluxIntegrand g x -
      (n - 1) * (n - 2) * a * ‖x‖ ^ (1 - n : ℝ)
  have hF : F =o[cobounded _] fun x ↦ ‖x‖ ^ (1 - n : ℝ) :=
    isLittleO_coordinateFluxIntegrand_mul_sub hgd hg0 hg1 hwd hw0 hw1
  -- The sphere integral of the error `F` tends to `0`.
  have hlim := tendsto_setIntegral_sphere_of_isLittleO hE (f := F) (by
    rwa [Nat.cast_sub (by omega), Nat.cast_one, neg_sub])
  -- The flux densities are bounded at infinity, hence integrable on large spheres.
  have hg : coordinateFluxIntegrand g =O[cobounded _] fun _ ↦ (1 : ℝ) :=
    (isLittleO_coordinateFluxIntegrand hg1).isBigO.trans
      ((tendsto_norm_cobounded_atTop.inv_tendsto_atTop).isBigO_one ℝ)
  have hmF : Measurable F := ((measurable_coordinateFluxIntegrand _).sub
    (measurable_coordinateFluxIntegrand _)).sub (measurable_const.mul (measurable_norm.pow_const _))
  have h := (hlim.div_const (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1))).add_const
    ((n - 2) * a / 2)
  rw [zero_div, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_integrableOn_sphere_of_isBigO_one hE
      (measurable_coordinateFluxIntegrand g).aestronglyMeasurable hg,
    eventually_integrableOn_sphere_of_isBigO_one hE hmF.aestronglyMeasurable
      (hF.isBigO.trans ((tendsto_norm_rpow_cobounded (by linarith)).isBigO_one ℝ)),
    eventually_gt_atTop 0] with r hig hiF hr
  exact (normalizedCoordinateFlux_mul_sub_eq hn a hr hig hiF).symm

/-- **The flux under the conformal factor `u ^ p`.** For `n ≥ 3`, let `g` be coefficients with
`g_ij → δ_ij` and `∂g_ij = o(|x|⁻¹)` at infinity, and let `u` be a function with
`u - 1 = O(|x| ^ (2 - n))` and `∇u = c ∇(|x| ^ (2 - n)) + o(|x| ^ (1 - n))`, as for
`u = 1 + c |x| ^ (2 - n) + o(|x| ^ (2 - n))` with differentiated remainder. Then the normalized
fluxes of `u ^ p g_ij` and of `g_ij` at radius `r` differ by `(n - 2) p c / 2 + o(1)`. -/
theorem tendsto_normalizedCoordinateFlux_rpow_mul_sub (hn : 3 ≤ n) (p : ℝ)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {c : ℝ}
    (hgd : ∀ᶠ x in cobounded _, ∀ i j, DifferentiableAt ℝ (fun y ↦ g y i j) x)
    (hg0 : ∀ i j, Tendsto (fun x ↦ g x i j) (cobounded _) (𝓝 (if i = j then 1 else 0)))
    (hg1 : ∀ i j, (fun x ↦ fderiv ℝ (fun y ↦ g y i j) x) =o[cobounded _] fun x ↦ ‖x‖⁻¹)
    (hud : ∀ᶠ x in cobounded _, DifferentiableAt ℝ u x)
    (hu0 : (fun x ↦ u x - 1) =O[cobounded _] fun x ↦ ‖x‖ ^ (2 - n : ℝ))
    (hu1 : (fun x ↦ fderiv ℝ u x - c • fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x) =o[cobounded _]
      fun x ↦ ‖x‖ ^ (1 - n : ℝ)) :
    Tendsto (fun r ↦ normalizedCoordinateFlux (fun y i j ↦ u y ^ p * g y i j) r -
      normalizedCoordinateFlux g r) atTop (𝓝 ((n - 2) * (p * c) / 2)) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  -- `u → 1` at infinity, since `|x| ^ (2 - n) → 0`.
  have hu : Tendsto u (cobounded _) (𝓝 1) :=
    tendsto_sub_nhds_zero_iff.1 (hu0.trans_tendsto (tendsto_norm_rpow_cobounded (by linarith)))
  have hpos : ∀ᶠ x in cobounded _, 0 < u x := hu.eventually_const_lt one_pos
  refine tendsto_normalizedCoordinateFlux_mul_sub (by omega) hgd hg0 hg1
    (hud.and hpos |>.mono fun x hx ↦ hx.1.rpow_const (Or.inl hx.2.ne')) ?_ ?_
  -- `u ^ p - 1 = O(u - 1)`, since `s ↦ s ^ p` is differentiable at `1`.
  · refine (((Real.hasDerivAt_rpow_const (p := p) (Or.inl one_ne_zero)).isBigO_sub.comp_tendsto
      hu).trans hu0).congr_left fun x ↦ ?_
    simp
  -- `∇(u ^ p) - p c ∇(|x| ^ (2 - n)) = p (∇u - c ∇(|x| ^ (2 - n))) + p (u ^ (p - 1) - 1) ∇u`.
  · have hk : (fun x ↦ p * (u x ^ (p - 1) - 1)) =o[cobounded _] fun _ ↦ (1 : ℝ) := by
      refine (isLittleO_one_iff ℝ).2 ?_
      simpa using ((hu.rpow_const (p := p - 1) (Or.inl one_ne_zero)).sub_const 1).const_mul p
    have hk' := (hk.smul_isBigO (isBigO_fderiv_of_isLittleO hu1)).congr_right
      fun x ↦ one_smul ℝ (‖x‖ ^ (1 - n : ℝ))
    refine ((hu1.const_smul_left p).add hk').congr' ?_ EventuallyEq.rfl
    filter_upwards [hud, hpos] with x hd hx
    rw [(hd.hasFDerivAt.rpow_const (p := p) (Or.inl hx.ne')).fderiv, Pi.smul_apply]
    module

/-! ### Conformal changes on an asymptotically Euclidean end -/

namespace IsAsymptoticallyEuclideanEnd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}

/-- **The flux of an end under a conformal change.** Let `φ` be an asymptotically Euclidean end of
order `t > 0` in dimension `n ≥ 3`, with metric coefficients `g_ij`, and let `u` be a function
with `u - 1 = O(|x| ^ (2 - n))` and `∇u = c ∇(|x| ^ (2 - n)) + o(|x| ^ (1 - n))` at infinity, as
for `u = 1 + c |x| ^ (2 - n) + o(|x| ^ (2 - n))` with differentiated remainder. Then the
normalized fluxes of the coefficients `u ^ (4 / (n - 2)) g_ij` of the conformal metric
`u ^ (4 / (n - 2)) g` and of `g_ij` at radius `r` differ by `2 c + o(1)` as `r → ∞`. -/
theorem tendsto_normalizedCoordinateFlux_rpow_mul_sub (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) (hn : 3 ≤ n) {u : EuclideanSpace ℝ (Fin n) → ℝ} {c : ℝ}
    (hud : ∀ᶠ x in cobounded _, DifferentiableAt ℝ u x)
    (hu0 : (fun x ↦ u x - 1) =O[cobounded _] fun x ↦ ‖x‖ ^ (2 - n : ℝ))
    (hu1 : (fun x ↦ fderiv ℝ u x - c • fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x) =o[cobounded _]
      fun x ↦ ‖x‖ ^ (1 - n : ℝ)) :
    Tendsto (fun r ↦ normalizedCoordinateFlux
      (fun y i j ↦ u y ^ (4 / (n - 2 : ℝ)) * pullbackMetricCoeff I φ y i j) r -
        normalizedCoordinateFlux (pullbackMetricCoeff I φ) r) atTop (𝓝 (2 * c)) := by
  have hn' : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  convert TauCeti.tendsto_normalizedCoordinateFlux_rpow_mul_sub hn _
    h.eventually_differentiableAt_pullbackMetricCoeff (h.tendsto_pullbackMetricCoeff ht)
    (h.isLittleO_fderiv_pullbackMetricCoeff ht) hud hu0 hu1 using 2
  field_simp
  ring

/-- **The mass of an end under a conformal change.** If the asymptotically Euclidean end `φ` of
order `t > 0` in dimension `n ≥ 3` has mass `m`, and `u` is a function with
`u - 1 = O(|x| ^ (2 - n))` and `∇u = c ∇(|x| ^ (2 - n)) + o(|x| ^ (1 - n))` at infinity, then the
coefficients `u ^ (4 / (n - 2)) g_ij` of the conformal metric `u ^ (4 / (n - 2)) g` have
mass `m + 2 c`. -/
theorem tendsto_normalizedCoordinateFlux_rpow_mul (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) (hn : 3 ≤ n) {u : EuclideanSpace ℝ (Fin n) → ℝ} {c m : ℝ}
    (hm : Tendsto (normalizedCoordinateFlux (pullbackMetricCoeff I φ)) atTop (𝓝 m))
    (hud : ∀ᶠ x in cobounded _, DifferentiableAt ℝ u x)
    (hu0 : (fun x ↦ u x - 1) =O[cobounded _] fun x ↦ ‖x‖ ^ (2 - n : ℝ))
    (hu1 : (fun x ↦ fderiv ℝ u x - c • fderiv ℝ (fun y ↦ ‖y‖ ^ (2 - n : ℝ)) x) =o[cobounded _]
      fun x ↦ ‖x‖ ^ (1 - n : ℝ)) :
    Tendsto (normalizedCoordinateFlux
      fun y i j ↦ u y ^ (4 / (n - 2 : ℝ)) * pullbackMetricCoeff I φ y i j) atTop
        (𝓝 (m + 2 * c)) :=
  (hm.add (h.tendsto_normalizedCoordinateFlux_rpow_mul_sub ht hn hud hu0 hu1)).congr
    fun _ ↦ add_sub_cancel _ _

end IsAsymptoticallyEuclideanEnd

end TauCeti
