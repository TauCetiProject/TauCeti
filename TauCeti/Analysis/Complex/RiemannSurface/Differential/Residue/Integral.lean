/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Residue.Basic
public import TauCeti.Analysis.Contour.Residue.Cutoff

/-!
# The residue of a meromorphic `1`-form as an integral in a chart

Let `ω` be a `1`-form on a Riemann surface `X`, meromorphic at `x`, and let `e` be a chart of the
maximal atlas at `x` whose target contains a closed disc `|z - c| ≤ R` with `e x` in its interior,
such that `ω` is holomorphic at every other point over that disc. Writing `ω = f(z) dz` in the
chart, the residue of `ω` at `x` is computed by integrals of `f` in the chart:

* `∮_{|z - c| = R} f dz = 2πi · Res_x ω`
  (`TauCeti.RiemannSurface.OneForm.circleIntegral_coeff_eq_residue`); this only needs `ω` to be
  meromorphic over the disc with nonnegative order away from `x`
  (`TauCeti.RiemannSurface.OneForm.circleIntegral_coeff_eq_residue_of_order_nonneg`);
* for a real cutoff `χ`, `C¹` at every point of the closed disc, equal to `1` near `e x` and
  vanishing on the boundary circle,
  `∫_{|z - c| ≤ R} d((1 - χ) f dz) = 2πi · Res_x ω`
  (`TauCeti.RiemannSurface.OneForm.integral_extDeriv_one_sub_mul_coeff_smul_dzForm_eq_residue`) and
  `∫_{|z - c| ≤ R} f · (i ∂ₓχ - ∂_yχ) = -2πi · Res_x ω`
  (`TauCeti.RiemannSurface.OneForm.integral_coeff_mul_fderiv_sub_fderiv_eq_neg_residue`).

The left-hand sides are computed in an arbitrary chart of the maximal atlas, the right-hand sides
do not depend on it (`TauCeti.RiemannSurface.OneForm.residue_eq_of_mem_maximalAtlas`). On a compact
Riemann surface the sum of the residues of a `1`-form meromorphic everywhere is a finite sum
(`TauCeti.RiemannSurface.OneForm.finite_support_residue`).

These are the local ingredients of the residue theorem on a compact Riemann surface proved by
Stokes' theorem (Forster, Theorem 10.21): with cutoffs `χᵢ` in coordinate discs about the poles,
`(1 - Σ χᵢ) ω` is a smooth compactly supported `1`-form, the integral of its exterior derivative
over `X` vanishes, and the contribution of the `i`-th disc is `2πi` times the residue at the `i`-th
pole.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §9 and Theorem 10.21.
-/

public section

noncomputable section

open Complex Filter Function IsManifold Metric Set
open scoped Manifold Real Topology

namespace TauCeti.RiemannSurface.OneForm

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {ω : OneForm X} {x : X}

variable {e : OpenPartialHomeomorph X ℂ} {c : ℂ} {R : ℝ}

/-- In a chart of the maximal atlas whose target contains the closed disc of radius `R` about
`c`, the hypotheses on `ω` translate into the hypotheses of the planar residue computations on
its coefficient. -/
private theorem coeff_hypotheses (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source)
    (hsub : closedBall c R ⊆ e.target) (hω : ω.MeromorphicAt x)
    (hhol : ∀ y ∈ e.source, e y ∈ closedBall c R → y ≠ x → ω.HolomorphicAt y) :
    _root_.MeromorphicAt (ω.coeff e) (e x) ∧
      ∀ z ∈ closedBall c R, z ≠ e x → AnalyticAt ℂ (ω.coeff e) z := by
  refine ⟨(meromorphicAt_iff_of_mem_maximalAtlas he hx).1 hω, fun z hz hzx ↦ ?_⟩
  have hzt := hsub hz
  refine (holomorphicAt_symm_iff_of_mem_maximalAtlas he hzt).1
    (hhol _ (e.map_target hzt) (by rwa [e.right_inv hzt]) fun h ↦ hzx ?_)
  rw [← e.right_inv hzt, h]

/-- **The residue as a circle integral in a chart.** If `ω` is meromorphic at every point over the
closed disc of radius `R` about `c`, contained in the target of a chart `e` of the maximal atlas and
containing `e x` in its interior, and has nonnegative order at every such point other than `x`,
then the circle integral of the coefficient of `ω` in `e` is `2πi · Res_x ω`. -/
theorem circleIntegral_coeff_eq_residue_of_order_nonneg (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (hx : x ∈ e.source) (hc : e x ∈ ball c R) (hsub : closedBall c R ⊆ e.target)
    (hω : ∀ y ∈ e.source, e y ∈ closedBall c R → ω.MeromorphicAt y)
    (hord : ∀ y ∈ e.source, e y ∈ closedBall c R → y ≠ x → 0 ≤ ω.order y) :
    circleIntegral (ω.coeff e) c R = 2 * π * I * ω.residue x := by
  rw [residue_eq_of_mem_maximalAtlas he hx]
  refine Contour.circleIntegral_eq_residue_of_meromorphicOrderAt_nonneg hc (fun z hz ↦ ?_)
    fun z hz hzx ↦ ?_ <;> have hzt := hsub hz
  · have h := hω _ (e.map_target hzt) (by rwa [e.right_inv hzt])
    rwa [meromorphicAt_iff_of_mem_maximalAtlas he (e.map_target hzt), e.right_inv hzt] at h
  · have h := hord _ (e.map_target hzt) (by rwa [e.right_inv hzt]) fun h ↦ hzx (by
      rw [← e.right_inv hzt, h])
    rwa [order_eq_of_mem_maximalAtlas he (e.map_target hzt), e.right_inv hzt] at h

/-- **The residue as a circle integral in a chart**, holomorphic form. If `ω` is meromorphic at `x`
and holomorphic at every other point over the closed disc of radius `R` about `c`, contained in the
target of a chart `e` of the maximal atlas and containing `e x` in its interior, then the circle
integral of the coefficient of `ω` in `e` is `2πi · Res_x ω`. -/
theorem circleIntegral_coeff_eq_residue (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source)
    (hc : e x ∈ ball c R) (hsub : closedBall c R ⊆ e.target) (hω : ω.MeromorphicAt x)
    (hhol : ∀ y ∈ e.source, e y ∈ closedBall c R → y ≠ x → ω.HolomorphicAt y) :
    circleIntegral (ω.coeff e) c R = 2 * π * I * ω.residue x :=
  circleIntegral_coeff_eq_residue_of_order_nonneg he hx hc hsub
    (fun y hy hyc ↦ by
      by_cases hyx : y = x
      · exact hyx ▸ hω
      · exact (hhol y hy hyc hyx).meromorphicAt)
    fun y hy hyc hyx ↦ (hhol y hy hyc hyx).order_nonneg

variable {χ : ℂ → ℝ}

/-- **The residue as the integral of the exterior derivative of a cutoff `1`-form in a chart.**
Under the hypotheses of `TauCeti.RiemannSurface.OneForm.circleIntegral_coeff_eq_residue`, for a
real function `χ`, `C¹` at every point of the closed disc, equal to `1` near `e x` and vanishing
on the boundary circle, the integral of `d((1 - χ) f dz)` over the disc, where `f` is the
coefficient of `ω` in `e`, is `2πi · Res_x ω`. -/
theorem integral_extDeriv_one_sub_mul_coeff_smul_dzForm_eq_residue
    (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source) (hc : e x ∈ ball c R)
    (hsub : closedBall c R ⊆ e.target)
    (hω : ω.MeromorphicAt x)
    (hhol : ∀ y ∈ e.source, e y ∈ closedBall c R → y ≠ x → ω.HolomorphicAt y)
    (hχ : ∀ z ∈ closedBall c R, ContDiffAt ℝ 1 χ z) (hχc : χ =ᶠ[𝓝 (e x)] 1)
    (hχR : ∀ z ∈ sphere c R, χ z = 0) :
    (∫ z in closedBall c R,
      extDeriv (fun y ↦ (((1 - χ y : ℝ) : ℂ) * ω.coeff e y) • dzForm) z ![1, I]) =
        2 * π * I * ω.residue x := by
  obtain ⟨hf, hfa⟩ := coeff_hypotheses he hx hsub hω hhol
  rw [residue_eq_of_mem_maximalAtlas he hx]
  exact Contour.integral_extDeriv_one_sub_mul_smul_dzForm_closedBall_eq_residue hc hf hfa hχ hχc
    hχR

/-- **The residue as a cutoff integral in a chart.** Under the hypotheses of
`TauCeti.RiemannSurface.OneForm.integral_extDeriv_one_sub_mul_coeff_smul_dzForm_eq_residue`,
`∫_{|z - c| ≤ R} f · (i ∂ₓχ - ∂_yχ) = -2πi · Res_x ω`, where `f` is the coefficient of `ω` in
`e`. -/
theorem integral_coeff_mul_fderiv_sub_fderiv_eq_neg_residue (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (hx : x ∈ e.source) (hc : e x ∈ ball c R) (hsub : closedBall c R ⊆ e.target)
    (hω : ω.MeromorphicAt x)
    (hhol : ∀ y ∈ e.source, e y ∈ closedBall c R → y ≠ x → ω.HolomorphicAt y)
    (hχ : ∀ z ∈ closedBall c R, ContDiffAt ℝ 1 χ z) (hχc : χ =ᶠ[𝓝 (e x)] 1)
    (hχR : ∀ z ∈ sphere c R, χ z = 0) :
    (∫ z in closedBall c R, ω.coeff e z * (I * fderiv ℝ χ z 1 - fderiv ℝ χ z I)) =
      -(2 * π * I * ω.residue x) := by
  obtain ⟨hf, hfa⟩ := coeff_hypotheses he hx hsub hω hhol
  rw [residue_eq_of_mem_maximalAtlas he hx]
  exact Contour.integral_mul_fderiv_sub_fderiv_closedBall_eq_neg_residue hc hf hfa hχ hχc hχR

end TauCeti.RiemannSurface.OneForm
