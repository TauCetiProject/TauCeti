/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
public import TauCeti.Geometry.Euclidean.Volume.Polar
import TauCeti.Analysis.Calculus.LineDeriv.Basic
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval

/-!
# The divergence theorem on spherical shells

Let `E` be a finite-dimensional real inner product space of dimension `n`, and let `V : E → E` be
a vector field of class `C¹` near the closed shell `r₁ ≤ ‖x - c‖ ≤ r₂`, `0 < r₁ ≤ r₂`. This file
proves the **divergence theorem** on the open shell `ball c r₂ \ closedBall c r₁`:

`∫_{r₁ < ‖x - c‖ < r₂} div V = ∫_{‖x - c‖ = r₂} ⟪V, ν⟫ dS - ∫_{‖x - c‖ = r₁} ⟪V, ν⟫ dS`,

where `div V x = tr (DV x)`, `ν x = (x - c) / ‖x - c‖` is the outward radial unit normal of the
spheres, and `dS` is the `(n - 1)`-dimensional Hausdorff measure `μHE[n - 1]`. Both boundary
spheres are oriented by the radial normal, so the inner sphere enters with a minus sign. The
spheres are boundaries of the shells exhausting an exterior region, which is how flux
integrals at infinity are compared: the difference of the fluxes of `V` through two large spheres
is the integral of `div V` over the shell between them.

## The argument

Write `F s` for the flux of `V` through the sphere of radius `s` about `c`, and `G s` for the
integral of `div V` over that sphere. Both depend continuously on `s ∈ [r₁, r₂]`
(`TauCeti.continuousOn_setIntegral_sphere`). For a test function `ψ` on `(r₁, r₂)`, the radial
function `χ x = ψ ‖x - c‖` is a test function on the open shell, with gradient
`ψ' (‖x - c‖) (x - c) / ‖x - c‖`. The weak form of the divergence,
`∫ ⟪∇χ, V⟫ = -∫ χ div V`
(`TauCeti.HasWeakFDerivOn.integral_inner_gradient_eq_neg_integral_smul_trace`), read in polar
coordinates (`TauCeti.integral_eq_integral_Ioi_setIntegral_sphere`), says `∫ ψ' F = -∫ ψ G`:
`G` is the weak derivative of `F` on `(r₁, r₂)`. Since `F` is continuous on the closed interval,
`F r₂ - F r₁ = ∫_{r₁}^{r₂} G` (`TauCeti.HasWeakLineDerivOn.integral_eq_sub`), and polar
coordinates over the shell
(`TauCeti.setIntegral_ball_sdiff_closedBall_eq_integral_Ioo_setIntegral_sphere`) identify
`∫_{r₁}^{r₂} G` with the integral of `div V` over the shell. No parametrization of the boundary
and no general Gauss–Green theorem is needed.

## Main results

* `TauCeti.integral_divergence_ball_sdiff_closedBall`: **the divergence theorem on a spherical
  shell**.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.2 (the Gauss–Green theorem)
  and Appendix C.3 (polar coordinates).
-/

public section

open MeasureTheory Measure Metric Set Filter Module InnerProductSpace TopologicalSpace
open scoped ContDiff Gradient Distributions InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {c : E} {r₁ r₂ : ℝ}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The gradient of the radial function `y ↦ ψ ‖y - c‖`, for `ψ` vanishing near `0`, is
`ψ' (‖x - c‖) (x - c) / ‖x - c‖`: its pairing with `v` is `ψ' (‖x - c‖) ⟪v, x - c⟫ / ‖x - c‖`,
also at `x = c`, where both sides vanish. -/
private lemma inner_gradient_comp_norm_sub {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ)
    (hψ0 : (0 : ℝ) ∉ tsupport ψ) (x v : E) :
    ⟪∇ (fun y ↦ ψ ‖y - c‖) x, v⟫_ℝ = deriv ψ ‖x - c‖ * (⟪v, x - c⟫_ℝ / ‖x - c‖) := by
  have hd : HasFDerivAt (fun y ↦ ψ ‖y - c‖)
      ((deriv ψ ‖x - c‖ / ‖x - c‖) • innerSL ℝ (x - c)) x := by
    refine (((hψ ‖x - c‖).hasFDerivAt_comp_norm (E := E) hψ0).comp x
      ((hasFDerivAt_id x).sub_const c)).congr_fderiv ?_
    ext w
    simp
  rw [inner_gradient_left, hd.fderiv, smul_apply, innerSL_apply_apply, smul_eq_mul,
    real_inner_comm, mul_div_assoc', div_mul_eq_mul_div]

/-- **The weak divergence identity against a radial test function.** Let `V` be `C¹` near the
closed shell `r₁ ≤ ‖x - c‖ ≤ r₂`, `0 < r₁`, and let `ψ` be a test function on `(r₁, r₂)`. Then
`x ↦ ψ' (‖x - c‖) ⟪V x, x - c⟫ / ‖x - c‖` and `x ↦ ψ (‖x - c‖) tr (DV x)` are integrable, and the
first integrates to minus the second: this is `∫ ⟪∇χ, V⟫ = -∫ χ div V` for `χ x = ψ ‖x - c‖`. -/
private lemma integral_deriv_mul_inner_eq_neg_integral_mul_trace {V : E → E} (hr₁ : 0 < r₁)
    (hV : ∀ x ∈ closedBall c r₂ \ ball c r₁, ContDiffAt ℝ 1 V x) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo r₁ r₂) :
    Integrable (fun x ↦ deriv ψ ‖x - c‖ * (⟪V x, x - c⟫_ℝ / ‖x - c‖)) ∧
      Integrable (fun x ↦ ψ ‖x - c‖ * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E)) ∧
      ∫ x, deriv ψ ‖x - c‖ * (⟪V x, x - c⟫_ℝ / ‖x - c‖) =
        -∫ x, ψ ‖x - c‖ * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) := by
  set Ω : Opens E := ⟨ball c r₂ \ closedBall c r₁, isOpen_ball.sdiff isClosed_closedBall⟩
  have hΩ : (Ω : Set E) ⊆ closedBall c r₂ \ ball c r₁ := fun x hx ↦
    ⟨ball_subset_closedBall hx.1, fun h ↦ hx.2 (ball_subset_closedBall h)⟩
  have hVΩ : ContDiffOn ℝ 1 V Ω := fun x hx ↦ (hV x (hΩ hx)).contDiffWithinAt
  -- The radial test function `χ x = ψ ‖x - c‖` is supported in the compact set `K ⊆ Ω` of
  -- points whose distance to `c` lies in `tsupport ψ`.
  have hψ0 : (0 : ℝ) ∉ tsupport ψ := fun h ↦ lt_asymm hr₁ (hψs h).1
  set K : Set E := (fun x ↦ ‖x - c‖) ⁻¹' tsupport ψ
  have hKc : IsClosed K := (isClosed_tsupport ψ).preimage (by fun_prop)
  have hKΩ : K ⊆ Ω := fun x hx ↦ by
    have hx' : ‖x - c‖ ∈ Ioo r₁ r₂ := hψs hx
    exact ⟨mem_ball_iff_norm.2 hx'.2, fun h ↦ (mem_closedBall_iff_norm.1 h).not_gt hx'.1⟩
  have hKcpt : IsCompact K :=
    (isCompact_closedBall c r₂).of_isClosed_subset hKc (hKΩ.trans (hΩ.trans sdiff_subset))
  have hχK : tsupport (fun x ↦ ψ ‖x - c‖) ⊆ K :=
    closure_minimal (fun x hx ↦ subset_tsupport ψ hx) hKc
  let φ : 𝓓(Ω, ℝ) := ⟨fun x ↦ ψ ‖x - c‖, (hψ.comp_norm hψ0).comp (contDiff_id.sub contDiff_const),
    hKcpt.of_isClosed_subset (isClosed_tsupport _) hχK, hχK.trans hKΩ⟩
  have hφ : (φ : E → ℝ) = fun x ↦ ψ ‖x - c‖ := rfl
  -- The first integrand is continuous on `Ω` and supported in `K`.
  have hh_supp : tsupport (fun x ↦ deriv ψ ‖x - c‖ * (⟪V x, x - c⟫_ℝ / ‖x - c‖)) ⊆ K :=
    closure_minimal (fun x hx ↦ support_deriv_subset (left_ne_zero_of_mul hx)) hKc
  have hne : ∀ x ∈ (Ω : Set E), ‖x - c‖ ≠ 0 := fun x hx ↦
    (hr₁.trans (by simpa [dist_eq_norm] using hx.2)).ne'
  refine ⟨Continuous.integrable_of_hasCompactSupport ?_
    (hKcpt.of_isClosed_subset (isClosed_tsupport _) hh_supp), ?_, ?_⟩
  · refine ContinuousOn.continuous_of_tsupport_subset ?_ Ω.isOpen (hh_supp.trans hKΩ)
    exact ((hψ.continuous_deriv (by simp)).comp_continuousOn (by fun_prop)).mul
      ((hVΩ.continuousOn.inner (continuousOn_id.sub continuousOn_const)).div
        (continuousOn_id.sub continuousOn_const).norm hne)
  · exact integrable_mul_trace_fderiv (μ := (volume : Measure E)) Ω.isOpen φ.continuous
      (hKcpt.of_isClosed_subset (isClosed_tsupport _) hχK) (hχK.trans hKΩ)
      fun x hx ↦ hV x (hΩ hx)
  · simpa only [hφ, inner_gradient_comp_norm_sub (hψ.differentiable (by simp)) hψ0,
      smul_eq_mul] using (hVΩ.hasWeakFDerivOn_fderiv (μ := (volume : Measure E))
        ).integral_inner_gradient_eq_neg_integral_smul_trace φ

/-- **The radial flux has distributional derivative the sphere integral of the divergence.** Let
`V` be `C¹` near the closed shell `r₁ ≤ ‖x - c‖ ≤ r₂`, `0 < r₁`, let `F s` be the flux of `V`
through `sphere c s` for the radial normal, and `G s` the integral of `tr (DV)` over `sphere c s`.
For every test function `ψ` on `(r₁, r₂)`, `∫ ψ' F = -∫ ψ G`. -/
private lemma integral_deriv_mul_flux_eq_neg_integral_mul [Nontrivial E] {V : E → E}
    (hr₁ : 0 < r₁) (hV : ∀ x ∈ closedBall c r₂ \ ball c r₁, ContDiffAt ℝ 1 V x) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo r₁ r₂) :
    ∫ t, deriv ψ t * ∫ x in sphere c t, ⟪V x, x - c⟫_ℝ / ‖x - c‖ ∂μHE[finrank ℝ E - 1] =
      -∫ t, ψ t * ∫ x in sphere c t, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E)
        ∂μHE[finrank ℝ E - 1] := by
  obtain ⟨hh, hg, hweak⟩ := integral_deriv_mul_inner_eq_neg_integral_mul_trace hr₁ hV hψ hψs
  -- Both radial integrands vanish for `t ≤ 0`, outside `tsupport ψ`.
  have hψt : ∀ t ∉ Ioi (0 : ℝ), t ∉ tsupport ψ := fun t ht h ↦ ht (hr₁.trans (hψs h).1)
  -- On the sphere of radius `t > 0`, the integrands are `ψ' t` times the flux density and `ψ t`
  -- times the divergence.
  have hsph {a : ℝ → ℝ} {f : E → ℝ} (t : ℝ) :
      ∫ x in sphere c t, a ‖x - c‖ * f x ∂μHE[finrank ℝ E - 1] =
        a t * ∫ x in sphere c t, f x ∂μHE[finrank ℝ E - 1] := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx ↦ by
      rw [mem_sphere_iff_norm.1 hx]
  -- Integrate in polar coordinates.
  calc _ = ∫ t in Ioi 0, deriv ψ t *
        ∫ x in sphere c t, ⟪V x, x - c⟫_ℝ / ‖x - c‖ ∂μHE[finrank ℝ E - 1] :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by
          rw [deriv_of_notMem_tsupport (hψt t ht), zero_mul]).symm
    _ = -∫ t in Ioi 0, ψ t * ∫ x in sphere c t,
          LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μHE[finrank ℝ E - 1] := by
        simp only [← hsph]
        rw [← integral_eq_integral_Ioi_setIntegral_sphere c hh,
          ← integral_eq_integral_Ioi_setIntegral_sphere c hg, hweak]
    _ = _ := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by
          rw [image_eq_zero_of_notMem_tsupport (hψt t ht), zero_mul]]

/-- **The divergence theorem on a spherical shell.** Let `V : E → E` be a vector field of class
`C¹` near the closed shell `r₁ ≤ ‖x - c‖ ≤ r₂`, where `0 < r₁ ≤ r₂`. Then the integral of its
divergence `tr (DV)` over the open shell `ball c r₂ \ closedBall c r₁` is the flux of `V` through
the outer sphere minus its flux through the inner sphere, both for the radial unit normal
`(x - c) / ‖x - c‖` and `(n - 1)`-dimensional Hausdorff measure. -/
theorem integral_divergence_ball_sdiff_closedBall {V : E → E} (hr₁ : 0 < r₁) (hr : r₁ ≤ r₂)
    (hV : ∀ x ∈ closedBall c r₂ \ ball c r₁, ContDiffAt ℝ 1 V x) :
    ∫ x in ball c r₂ \ closedBall c r₁, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) =
      (∫ x in sphere c r₂, ⟪V x, x - c⟫_ℝ / ‖x - c‖ ∂μHE[finrank ℝ E - 1]) -
        ∫ x in sphere c r₁, ⟪V x, x - c⟫_ℝ / ‖x - c‖ ∂μHE[finrank ℝ E - 1] := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space the shell and the spheres of positive radius are empty.
    have hempty : ball c r₂ \ closedBall c r₁ = ∅ :=
      sdiff_eq_empty.2 fun x _ ↦ by simp [Subsingleton.elim x c, hr₁.le]
    rw [hempty, sphere_eq_empty_of_subsingleton (hr₁.trans_le hr).ne',
      sphere_eq_empty_of_subsingleton hr₁.ne']
    simp
  have hK : closedBall c r₂ \ ball c r₁ ⊆ {x | ‖x - c‖ ≠ 0} := fun x hx ↦
    (hr₁.trans_le (by simpa [dist_eq_norm] using hx.2)).ne'
  have hVc : ContinuousOn V (closedBall c r₂ \ ball c r₁) := fun x hx ↦
    (hV x hx).continuousAt.continuousWithinAt
  -- The flux `F` and the sphere integrals `G` of the divergence are continuous on `[r₁, r₂]`, and
  -- `G` is the weak derivative of `F` on `(r₁, r₂)`, so `F r₂ - F r₁ = ∫_{r₁}^{r₂} G`.
  have hF := continuousOn_setIntegral_sphere (c := c) (r₂ := r₂) hr₁
    (f := fun x ↦ ⟪V x, x - c⟫_ℝ / ‖x - c‖)
    ((hVc.inner (continuousOn_id.sub continuousOn_const)).div
      (continuousOn_id.sub continuousOn_const).norm fun x hx ↦ hK hx)
  have hG := continuousOn_setIntegral_sphere (c := c) (r₂ := r₂) hr₁
    (continuousOn_trace_fderiv hV)
  have hW : HasWeakLineDerivOn volume ⟨Ioo r₁ r₂, isOpen_Ioo⟩
      (fun t ↦ ∫ x in sphere c t, ⟪V x, x - c⟫_ℝ / ‖x - c‖ ∂μHE[finrank ℝ E - 1])
      (fun t ↦ ∫ x in sphere c t, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E)
        ∂μHE[finrank ℝ E - 1]) 1 :=
    (hasWeakLineDerivOn_iff ((hF.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo)
      ((hG.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo)).2
      fun ψ hψ _ hψs ↦ by
        simpa only [lineDeriv_one, smul_eq_mul] using
          integral_deriv_mul_flux_eq_neg_integral_mul hr₁ hV hψ hψs
  -- Polar coordinates over the shell.
  have hint : IntegrableOn (fun x ↦ LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E))
      (ball c r₂ \ closedBall c r₁) :=
    ((continuousOn_trace_fderiv hV).integrableOn_compact
      ((isCompact_closedBall c r₂).diff isOpen_ball)).mono_set
      fun x hx ↦ ⟨ball_subset_closedBall hx.1, fun h ↦ hx.2 (ball_subset_closedBall h)⟩
  rw [setIntegral_ball_sdiff_closedBall_eq_integral_Ioo_setIntegral_sphere c r₁ r₂ hint,
    ← integral_Ioc_eq_integral_Ioo, ← _root_.intervalIntegral.integral_of_le hr]
  exact hW.integral_eq_sub (hG.integrableOn_Icc.mono_set Ioo_subset_Icc_self) hF
    EventuallyEq.rfl ⟨le_rfl, hr⟩ ⟨hr, le_rfl⟩

end TauCeti
