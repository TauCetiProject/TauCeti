/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Flux
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.Geometry.Euclidean.Volume.Divergence

/-!
# The divergence form of the ADM flux

Let `g : ℝⁿ → (Fin n → Fin n → ℝ)` be metric coefficients in a coordinate system on the exterior
of a ball. The ADM flux density `TauCeti.coordinateFluxIntegrand g` at `x` is `⟪U x, x / |x|⟫`
for the vector field `U_j = Σ_i (∂_i g_ij - ∂_j g_ii)`, whose divergence is the
**linearized scalar curvature**

`TauCeti.linearizedScalarCurvature g = Σ_j Σ_i (∂_j ∂_i g_ij - ∂_j ∂_j g_ii)
  = Σ_{i,j} ∂_i ∂_j g_ij - Δ (tr g)`,

the derivative at the Euclidean metric `δ` of the coordinate expression of the scalar curvature,
in the direction `g - δ`. By the divergence theorem on spherical shells
(`TauCeti.integral_divergence_ball_sdiff_closedBall`), for `C²` coefficients the normalized flux
at two radii `0 ≤ r₁ ≤ r₂` differs by the integral of the linearized scalar curvature over the
shell between them, divided by `2 (n - 1) |Sⁿ⁻¹|`
(`TauCeti.normalizedCoordinateFlux_sub_eq_setIntegral_linearizedScalarCurvature`).

Consequently, if the coefficients are `C²` on the exterior `‖x‖ > R` and the linearized scalar
curvature is integrable there, the flux converges as `r → ∞`, to its value at any radius `r > R`
plus the normalized integral of the linearized scalar curvature over `‖x‖ > r`
(`TauCeti.tendsto_normalizedCoordinateFlux_of_integrableOn`): the ADM mass exists
(`TauCeti.exists_tendsto_normalizedCoordinateFlux_of_integrableOn`). This is the analytic half of
the existence of the mass of an asymptotically Euclidean end of order `t > (n - 2) / 2`: there the
scalar curvature differs from its linearization by terms quadratic in `g - δ` and its derivatives,
which are `O(|x|^(-2t-2))` and so integrable since `2t + 2 > n`, so that integrability of the
scalar curvature gives integrability of the linearized scalar curvature. That comparison is not
part of this file.

## Main declarations

* `TauCeti.linearizedScalarCurvature`: the linearized scalar curvature
  `Σ_{i,j} ∂_i ∂_j g_ij - Δ (tr g)` of metric coefficients, with its basic API: it is measurable
  (`TauCeti.measurable_linearizedScalarCurvature`), local
  (`TauCeti.linearizedScalarCurvature_congr_of_eventuallyEq`) and linear in the coefficients
  (`TauCeti.linearizedScalarCurvature_smul`, `TauCeti.linearizedScalarCurvature_add`).
* `TauCeti.normalizedCoordinateFlux_sub_eq_setIntegral_linearizedScalarCurvature`: the flux
  difference between two radii is the integral of the linearized scalar curvature over the shell.
* `TauCeti.tendsto_normalizedCoordinateFlux_of_integrableOn`,
  `TauCeti.exists_tendsto_normalizedCoordinateFlux_of_integrableOn`: integrability of the
  linearized scalar curvature on an exterior region gives convergence of the flux.

## References

* J. M. Lee, T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Definition 8.2
  and §9 (existence of the mass).
* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  §4.
-/

public section

noncomputable section

open MeasureTheory Measure Metric Set Filter Module
open scoped Topology InnerProductSpace

namespace TauCeti

variable {n : ℕ}

/-- The **linearized scalar curvature** of metric coefficients `g i j` on `ℝⁿ`:
`Σ_j Σ_i (∂_j ∂_i g_ij - ∂_j ∂_j g_ii)`, that is, `Σ_{i,j} ∂_i ∂_j g_ij - Δ (tr g)`. It is the
derivative at the Euclidean metric of the coordinate expression of the scalar curvature, in the
direction `g - δ`, and the divergence of the vector field `Σ_i (∂_i g_ij - ∂_j g_ii)` whose
radial component is the ADM flux density `TauCeti.coordinateFluxIntegrand g`. -/
def linearizedScalarCurvature (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j, ∑ i,
    (fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single j 1) -
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i i) y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single j 1))

/-- Unfolding lemma for `TauCeti.linearizedScalarCurvature`. -/
theorem linearizedScalarCurvature_def (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    linearizedScalarCurvature g x =
      ∑ j, ∑ i,
        (fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1) -
          fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i i) y (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single j 1)) :=
  (rfl)

/-- Constant coefficients, such as those of the Euclidean metric `δ_ij`, have vanishing linearized
scalar curvature. -/
@[simp]
theorem linearizedScalarCurvature_const (a : Fin n → Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    linearizedScalarCurvature (fun _ ↦ a) x = 0 := by
  simp [linearizedScalarCurvature_def]

/-- Adding constant coefficients, such as those of the Euclidean metric `δ_ij`, does not change
the linearized scalar curvature. -/
@[simp]
theorem linearizedScalarCurvature_const_add (a : Fin n → Fin n → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    linearizedScalarCurvature (fun y i j ↦ a i j + g y i j) x = linearizedScalarCurvature g x := by
  simp [linearizedScalarCurvature_def]

/-- The linearized scalar curvature is measurable, whatever the regularity of the coefficients. -/
theorem measurable_linearizedScalarCurvature
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) :
    Measurable (linearizedScalarCurvature g) := by
  rw [funext (linearizedScalarCurvature_def g)]
  fun_prop

/-- The linearized scalar curvature at `x` only depends on the coefficients near `x`. -/
theorem linearizedScalarCurvature_congr_of_eventuallyEq
    {g g' : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (h : g =ᶠ[𝓝 x] g') :
    linearizedScalarCurvature g x = linearizedScalarCurvature g' x := by
  -- The first partial derivatives agree near `x`, hence so do their derivatives at `x`.
  have hd (i j k : Fin n) :
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x =
        fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g' z i j) y (EuclideanSpace.single k 1)) x :=
    EventuallyEq.fderiv_eq <| h.eventuallyEq_nhds.mono fun y hy ↦ by
      have hy' : fderiv ℝ (fun z ↦ g z i j) y = fderiv ℝ (fun z ↦ g' z i j) y :=
        (hy.fun_comp fun a ↦ a i j).fderiv_eq
      simp only [hy']
  simp only [linearizedScalarCurvature_def, hd]

/-- The linearized scalar curvature is homogeneous in the coefficients. -/
@[simp]
theorem linearizedScalarCurvature_smul (c : ℝ)
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    linearizedScalarCurvature (c • g) x = c * linearizedScalarCurvature g x := by
  have hd (f : EuclideanSpace ℝ (Fin n) → ℝ) :
      fderiv ℝ (fun y ↦ c * f y) = c • fderiv ℝ f := by
    rw [← fderiv_const_smul_field, Pi.smul_def]
    simp only [smul_eq_mul]
  simp only [linearizedScalarCurvature_def, Pi.smul_apply, smul_eq_mul, hd, FunLike.coe_smul,
    ← mul_sub, ← Finset.mul_sum]

/-- For `C²` coefficients, the first partial derivatives of the coefficients are `C¹`. -/
private lemma contDiffAt_fderiv_apply_single
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y ↦ g y i j) x) (i j k : Fin n) :
    ContDiffAt ℝ 1 (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x :=
  ((hg i j).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

/-- The linearized scalar curvature is additive in coefficients of class `C²` at the point. -/
theorem linearizedScalarCurvature_add {g h : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hg : ∀ i j, ContDiffAt ℝ 2 (fun y ↦ g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y ↦ h y i j) x) :
    linearizedScalarCurvature (g + h) x =
      linearizedScalarCurvature g x + linearizedScalarCurvature h x := by
  -- Near `x` the first partial derivatives of `g + h` are the sums of those of `g` and `h`; the
  -- sums are differentiable at `x`, so their derivatives at `x` add too.
  have hd (i j k : Fin n) :
      fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ (g + h) z i j) y (EuclideanSpace.single k 1)) x =
        fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x +
          fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ h z i j) y (EuclideanSpace.single k 1)) x := by
    have hev : (fun y ↦ fderiv ℝ (fun z ↦ (g + h) z i j) y (EuclideanSpace.single k 1)) =ᶠ[𝓝 x]
        fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1) +
          fderiv ℝ (fun z ↦ h z i j) y (EuclideanSpace.single k 1) := by
      filter_upwards [((hg i j).eventually (by simp)), ((hh i j).eventually (by simp))]
        with y hgy hhy
      simp only [Pi.add_apply]
      rw [fderiv_fun_add (hgy.differentiableAt two_ne_zero) (hhy.differentiableAt two_ne_zero),
        add_apply]
    rw [hev.fderiv_eq, fderiv_fun_add
      ((contDiffAt_fderiv_apply_single hg i j k).differentiableAt one_ne_zero)
      ((contDiffAt_fderiv_apply_single hh i j k).differentiableAt one_ne_zero)]
  simp only [linearizedScalarCurvature_def, hd, add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

/-- The vector field `U_j = Σ_i (∂_i g_ij - ∂_j g_ii)` whose radial component is the ADM flux
density. -/
private def coordinateFluxField (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j ↦ ∑ i, (fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.single i 1) -
    fderiv ℝ (fun y ↦ g y i i) x (EuclideanSpace.single j 1))

private lemma coordinateFluxField_apply (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    coordinateFluxField g x j = ∑ i, (fderiv ℝ (fun y ↦ g y i j) x (EuclideanSpace.single i 1) -
      fderiv ℝ (fun y ↦ g y i i) x (EuclideanSpace.single j 1)) := by
  simp only [coordinateFluxField, PiLp.toLp_apply]

/-- The flux density is the radial component of `coordinateFluxField`. -/
private lemma coordinateFluxIntegrand_eq_inner_div_norm
    (g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    coordinateFluxIntegrand g x = ⟪coordinateFluxField g x, x⟫_ℝ / ‖x‖ := by
  simp only [coordinateFluxIntegrand_def, PiLp.inner_apply, coordinateFluxField_apply,
    Finset.sum_div, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- For `C²` coefficients, `coordinateFluxField` is `C¹`. -/
private lemma contDiffAt_coordinateFluxField {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hg : ∀ i j, ContDiffAt ℝ 2 (fun y ↦ g y i j) x) :
    ContDiffAt ℝ 1 (coordinateFluxField g) x := by
  have hD := contDiffAt_fderiv_apply_single hg
  refine contDiffAt_piLp' 2 fun j ↦ ?_
  simp only [coordinateFluxField_apply]
  exact ContDiffAt.sum fun i _ ↦ (hD i j i).sub (hD i i j)

/-- For `C²` coefficients, the divergence of `coordinateFluxField` is the linearized scalar
curvature. -/
private lemma trace_fderiv_coordinateFluxField
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y ↦ g y i j) x) :
    LinearMap.trace ℝ _ (fderiv ℝ (coordinateFluxField g) x :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      linearizedScalarCurvature g x := by
  have hD (i j k : Fin n) :
      DifferentiableAt ℝ (fun y ↦ fderiv ℝ (fun z ↦ g z i j) y (EuclideanSpace.single k 1)) x :=
    (contDiffAt_fderiv_apply_single hg i j k).differentiableAt one_ne_zero
  rw [trace_fderiv_eq_sum_fderiv_apply_single
    ((contDiffAt_coordinateFluxField hg).differentiableAt one_ne_zero),
    linearizedScalarCurvature_def]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [coordinateFluxField_apply]
  rw [fderiv_fun_sum fun i _ ↦ (hD i j i).fun_sub (hD i i j), sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [fderiv_fun_sub (hD i j i) (hD i i j), _root_.sub_apply]

/-- **The flux identity.** For metric coefficients of class `C²` near the closed shell
`r₁ ≤ ‖x‖ ≤ r₂`, `0 ≤ r₁ ≤ r₂`, the normalized ADM flux at radius `r₂` minus that at radius `r₁`
is the integral of the linearized scalar curvature over the open shell between them, divided by
`2 (n - 1) |Sⁿ⁻¹|`. -/
theorem normalizedCoordinateFlux_sub_eq_setIntegral_linearizedScalarCurvature
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr : r₁ ≤ r₂)
    (hg : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) r₂ \ ball 0 r₁, ∀ i j,
      ContDiffAt ℝ 2 (fun y ↦ g y i j) x) :
    normalizedCoordinateFlux g r₂ - normalizedCoordinateFlux g r₁ =
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) r₂ \ closedBall 0 r₁,
          linearizedScalarCurvature g x) /
        (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)) := by
  have hdiv := integral_divergence_ball_sdiff_closedBall (c := 0) hr₁ hr
    fun x hx ↦ contDiffAt_coordinateFluxField (hg x hx)
  simp only [finrank_euclideanSpace_fin, sub_zero] at hdiv
  rw [normalizedCoordinateFlux_def, normalizedCoordinateFlux_def, ← sub_div,
    ← setIntegral_congr_fun (measurableSet_ball.diff measurableSet_closedBall) fun x hx ↦
      trace_fderiv_coordinateFluxField
        (hg x (sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall hx)),
    hdiv]
  simp only [coordinateFluxIntegrand_eq_inner_div_norm]

/-- **Convergence of the flux.** If the metric coefficients are `C²` on the exterior `‖x‖ > R`
and their linearized scalar curvature is integrable there, then for every radius `r > R`, `r ≥ 0`,
the normalized ADM flux converges as the radius tends to infinity, to its value at `r` plus the
integral of the linearized scalar curvature over `‖x‖ > r` divided by `2 (n - 1) |Sⁿ⁻¹|`. -/
theorem tendsto_normalizedCoordinateFlux_of_integrableOn
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {R r : ℝ} (hr : 0 ≤ r) (hRr : R < r)
    (hg : ∀ i j, ContDiffOn ℝ 2 (fun y ↦ g y i j) (closedBall 0 R)ᶜ)
    (hL : IntegrableOn (linearizedScalarCurvature g) (closedBall 0 R)ᶜ) :
    Tendsto (normalizedCoordinateFlux g) atTop
      (𝓝 (normalizedCoordinateFlux g r +
        (∫ x in (closedBall (0 : EuclideanSpace ℝ (Fin n)) r)ᶜ, linearizedScalarCurvature g x) /
          (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)))) := by
  -- Beyond `r`, the flux is its value at `r` plus the normalized integral over a shell.
  have hshell : (fun ρ ↦ normalizedCoordinateFlux g r +
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin n)) ρ \ closedBall 0 r,
        linearizedScalarCurvature g x) / (2 * ((n : ℝ) - 1) * roundSphereVolume (n - 1)))
        =ᶠ[atTop] normalizedCoordinateFlux g := by
    filter_upwards [eventually_ge_atTop r] with ρ hρ
    refine (eq_add_of_sub_eq'
      (normalizedCoordinateFlux_sub_eq_setIntegral_linearizedScalarCurvature hr hρ
        fun x hx i j ↦ (hg i j).contDiffAt (isClosed_closedBall.isOpen_compl.mem_nhds ?_))).symm
    rw [mem_compl_iff, mem_closedBall_zero_iff, not_le]
    exact hRr.trans_le (not_lt.mp (mt mem_ball_zero_iff.mpr hx.2))
  -- The shells exhaust the exterior `‖x‖ > r`.
  have hU : (⋃ ρ : ℝ, ball (0 : EuclideanSpace ℝ (Fin n)) ρ \ closedBall 0 r) =
      (closedBall 0 r)ᶜ := by
    ext x
    simp only [mem_iUnion, Set.mem_sdiff, mem_ball_zero_iff, mem_compl_iff]
    exact ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨‖x‖ + 1, lt_add_one _, h⟩⟩
  have hlim := tendsto_setIntegral_of_monotone
    (fun ρ ↦ measurableSet_ball.diff measurableSet_closedBall)
    (fun _ _ hρ ↦ sdiff_subset_sdiff_left (ball_subset_ball hρ))
    (hU ▸ hL.mono_set (compl_subset_compl.2 (closedBall_subset_closedBall hRr.le)))
  rw [hU] at hlim
  exact (tendsto_const_nhds.add (hlim.div_const _)).congr' hshell

/-- **Existence of the mass.** If the metric coefficients are `C²` on the exterior `‖x‖ > R` and
their linearized scalar curvature is integrable there, then the normalized ADM flux converges as
the radius tends to infinity. -/
theorem exists_tendsto_normalizedCoordinateFlux_of_integrableOn
    {g : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ} {R : ℝ}
    (hg : ∀ i j, ContDiffOn ℝ 2 (fun y ↦ g y i j) (closedBall 0 R)ᶜ)
    (hL : IntegrableOn (linearizedScalarCurvature g) (closedBall 0 R)ᶜ) :
    ∃ m, Tendsto (normalizedCoordinateFlux g) atTop (𝓝 m) :=
  ⟨_, tendsto_normalizedCoordinateFlux_of_integrableOn (r := max R 0 + 1) (by positivity)
    ((le_max_left R 0).trans_lt (lt_add_one _)) hg hL⟩

end TauCeti
