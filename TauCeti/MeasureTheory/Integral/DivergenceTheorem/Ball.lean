/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.MeasureTheory.Group.Integral
import TauCeti.Topology.Algebra.Module.Trace

/-!
# The divergence theorem on a ball

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure `μ`, and let `V : E → E` be a vector field which is `C¹` near the closed ball of radius
`R ≥ 0` about `c`. This file proves the **divergence theorem on the ball**:

`∫_{ball c R} tr (DV) dμ = R ^ (n - 1) ∫_{θ ∈ S} ⟪V (c + R θ), θ⟫ dμ.toSphere`,

where `S` is the unit sphere with Mathlib's polar-coordinate surface measure `μ.toSphere`, so that
`R ^ (n - 1) dμ.toSphere` is the surface measure of the sphere of radius `R`, and `θ` is the outward
unit normal at `c + R θ` (`TauCeti.setIntegral_ball_trace_fderiv`).

Write `Φ s = s ^ (n - 1) ∫ ⟪V (s θ), θ⟫` for the flux through the sphere of radius `s` about the
origin and `G s = ∫_{ball 0 s} tr (DV)`. In polar coordinates `G` is the primitive of
`g s = s ^ (n - 1) ∫ tr (DV (s θ))` (`TauCeti.hasDerivAt_setIntegral_ball`). The proof shows that
`Φ` has the same distributional derivative `g` on `(0, R)`, without any tangential calculus on the
sphere. For a test function `ψ` on `(0, R)`, the radial function `χ x = ψ ‖x‖` has gradient
`ψ' (‖x‖) x / ‖x‖`, and the compactly supported field `χ V` has divergence integral zero
(`TauCeti.integral_fderiv_eq_zero_of_hasCompactSupport`). Expanding
`tr (D (χ V)) = χ tr (DV) + ⟪∇χ, V⟫` in polar coordinates gives `∫ ψ' Φ = -∫ ψ g`. So `Φ - G` is
constant on `(0, R)` by the du Bois-Reymond lemma
(`ContinuousOn.exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero`), and both vanish at the
origin: the surface measure has barycenter zero (`TauCeti.integral_toSphere_coe_eq_zero`). This
is the radial test-function argument of the mean-value property for harmonic functions
(`InnerProductSpace.HarmonicOnNhd.integral_toSphere_eq`), applied to the flux instead of the sphere
average.

## Main results

* `TauCeti.setIntegral_ball_trace_fderiv`: the divergence theorem on a ball.

## References

* L. C. Evans, *Partial Differential Equations*, Appendix C.2 (the Gauss–Green theorem).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Filter Topology Module
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A point at radius `s ≥ 0` in direction `θ` lies in the closed ball of radius `R ≥ s`. -/
private lemma smul_mem_closedBall {s R : ℝ} (hs : s ∈ Icc 0 R) (θ : sphere (0 : E) 1) :
    s • (θ : E) ∈ closedBall (0 : E) R := by
  rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere θ, mul_one,
    Real.norm_of_nonneg hs.1]
  exact hs.2

/-! ### Radial test functions -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the norm away from the origin. -/
private lemma hasFDerivAt_norm {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hx' : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have h := (Real.hasDerivAt_sqrt hx').comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] at h
  convert h using 1
  ext v
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul, two_smul,
    add_apply]
  field_simp
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A function `ψ` on the line vanishing near `0` gives the radial function `x ↦ ψ ‖x‖`, with
gradient `ψ' (‖x‖) x / ‖x‖`. -/
private lemma hasFDerivAt_comp_norm {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ)
    (hψ0 : 0 ∉ tsupport ψ) (x : E) :
    HasFDerivAt (fun y : E ↦ ψ ‖y‖) ((deriv ψ ‖x‖ / ‖x‖) • innerSL ℝ x) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : (fun y : E ↦ ψ ‖y‖) =ᶠ[𝓝 0] fun _ ↦ 0 :=
      (continuous_norm.tendsto' (0 : E) 0 norm_zero).eventually
        (notMem_tsupport_iff_eventuallyEq.mp hψ0)
    simpa using (hasFDerivAt_const (0 : ℝ) (0 : E)).congr_of_eventuallyEq h
  · have h := (hψ ‖x‖).hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_norm hx)
    rwa [div_eq_mul_inv, mul_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The radial function `x ↦ ψ ‖x‖` of a smooth `ψ` vanishing near `0` is smooth. -/
private lemma contDiff_comp_norm {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψ0 : 0 ∉ tsupport ψ) :
    ContDiff ℝ ∞ fun x : E ↦ ψ ‖x‖ := by
  refine contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · have h : (fun y : E ↦ ψ ‖y‖) =ᶠ[𝓝 0] fun _ ↦ 0 :=
      (continuous_norm.tendsto' (0 : E) 0 norm_zero).eventually
        (notMem_tsupport_iff_eventuallyEq.mp hψ0)
    exact contDiffAt_const.congr_of_eventuallyEq h
  · exact hψ.contDiffAt.comp x (contDiffAt_norm ℝ hx)

/-! ### The distributional derivative of the flux -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The trace of the derivative of `V` is continuous on the closed ball where `V` is `C¹`. -/
private lemma continuousOn_trace_fderiv {V : E → E} {s : Set E}
    (hV : ∀ x ∈ s, ContDiffAt ℝ 1 V x) :
    ContinuousOn (fun x ↦ LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E)) s := fun x hx ↦ by
  simpa only [Function.comp_def, traceCLM_apply] using ((traceCLM ℝ E).continuous.continuousAt.comp
    ((hV x hx).fderiv_right (m := 0) le_rfl).continuousAt).continuousWithinAt

/-- If `χ` is continuous with compact support inside an open set `U` on which `V` is `C¹`, then
`χ tr (DV)` is integrable. -/
private lemma integrable_mul_trace_fderiv {U : Set E} (hU : IsOpen U) {χ : E → ℝ} {V : E → E}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x) :
    Integrable (fun x ↦ χ x * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E)) μ :=
  ((hχ.continuousOn.mul (continuousOn_trace_fderiv hV)).continuous_of_tsupport_subset hU
    (tsupport_mul_subset_left.trans hχU)).integrable_of_hasCompactSupport hχc.mul_right

omit [FiniteDimensional ℝ E] in
/-- If `χ` is `C¹` with compact support inside an open set `U` on which `V` is continuous, then
`x ↦ Dχ(x) (V x)` is integrable. -/
private lemma integrable_fderiv_apply {U : Set E} (hU : IsOpen U) {χ : E → ℝ} {V : E → E}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hV : ContinuousOn V U) : Integrable (fun x ↦ fderiv ℝ χ x (V x)) μ := by
  have hsupp : tsupport (fun x ↦ fderiv ℝ χ x (V x)) ⊆ tsupport χ :=
    (closure_mono (Function.support_subset_iff'.mpr fun x hx ↦ by
      simp [Function.notMem_support.mp hx])).trans (tsupport_fderiv_subset ℝ)
  exact (((hχ.continuous_fderiv one_ne_zero).continuousOn.clm_apply hV
    ).continuous_of_tsupport_subset hU (hsupp.trans hχU)).integrable_of_hasCompactSupport
      (hχc.mono' (subset_closure.trans hsupp))

/-- **Integration by parts for the divergence.** If `χ` is `C¹` with compact support inside an
open set `U` on which the field `V` is `C¹`, then `∫ χ tr (DV) = -∫ Dχ (V)`: the field `χ V` is
compactly supported, so its divergence `χ tr (DV) + Dχ (V)` integrates to zero. -/
private lemma integral_mul_trace_fderiv_eq_neg {U : Set E} (hU : IsOpen U) {χ : E → ℝ}
    {V : E → E} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    (hV : ∀ x ∈ U, ContDiffAt ℝ 1 V x) :
    ∫ x, χ x * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      -∫ x, fderiv ℝ χ x (V x) ∂μ := by
  have hχ0 : ∀ x ∉ U, χ =ᶠ[𝓝 x] 0 := fun x hx ↦
    notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hx (hχU h)
  set u : E → E := fun x ↦ χ x • V x
  -- `D(χ V) = χ DV + Dχ ⊗ V`, also off `U`, where both sides vanish.
  have hu_deriv : ∀ x, fderiv ℝ u x = χ x • fderiv ℝ V x + (fderiv ℝ χ x).smulRight (V x) :=
    fun x ↦ by
      by_cases hx : x ∈ U
      · exact ((hχ.differentiable one_ne_zero x).hasFDerivAt.smul
          ((hV x hx).differentiableAt one_ne_zero).hasFDerivAt).fderiv
      · have h0 := hχ0 x hx
        have hu0 : u =ᶠ[𝓝 x] 0 := h0.mono fun y hy ↦ by simp [u, hy]
        rw [hu0.fderiv_eq, h0.self_of_nhds, h0.fderiv_eq]
        simp
  have hu : ContDiff ℝ 1 u := contDiff_iff_contDiffAt.mpr fun x ↦ by
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul (hV x hx)
    · exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
        ((hχ0 x hx).mono fun y hy ↦ by simp [u, hy])
  have huc : HasCompactSupport u := hχc.smul_right
  have hzero : ∫ x, traceCLM ℝ E (fderiv ℝ u x) ∂μ = 0 := by
    rw [(traceCLM ℝ E).integral_comp_comm
      ((hu.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport (huc.fderiv (𝕜 := ℝ))),
      integral_fderiv_eq_zero_of_hasCompactSupport hu huc, map_zero]
  have hsplit : ∀ x, traceCLM ℝ E (fderiv ℝ u x) =
      χ x * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) + fderiv ℝ χ x (V x) := fun x ↦ by
    rw [hu_deriv, map_add, map_smul, traceCLM_apply, traceCLM_apply,
      ContinuousLinearMap.coe_smulRight, LinearMap.trace_smulRight, smul_eq_mul]
    rfl
  -- Both parts are integrable: the first is continuous with compact support.
  have hint₁ := integrable_mul_trace_fderiv (μ := μ) hU hχ.continuous hχc hχU hV
  have hint₂ := integrable_fderiv_apply (μ := μ) hU hχ hχc hχU
    fun x hx ↦ (hV x hx).continuousAt.continuousWithinAt
  have h := integral_add hint₁ hint₂
  simp_rw [← hsplit] at h
  rw [hzero] at h
  linarith

/-- **The flux has distributional derivative `g`.** For a field `V` that is `C¹` on `ball 0 R`
and a test function `ψ` on `(0, R)`,
`∫ ψ' (s) s ^ (n - 1) ∫ ⟪V (s θ), θ⟫ = -∫ ψ (s) s ^ (n - 1) ∫ tr (DV (s θ))`. This is
`integral_mul_trace_fderiv_eq_neg` for the radial function `χ x = ψ ‖x‖`, in polar coordinates. -/
private lemma integral_deriv_mul_flux_eq_neg [Nontrivial E] {R : ℝ} {V : E → E}
    (hV : ∀ x ∈ ball (0 : E) R, ContDiffAt ℝ 1 V x) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo 0 R) :
    ∫ s, deriv ψ s * (s ^ (finrank ℝ E - 1) *
        ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere) =
      -∫ s, ψ s * (s ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1,
        LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere) := by
  have hψ0 : 0 ∉ tsupport ψ := fun h ↦ (lt_irrefl _ (hψs h).1)
  set χ : E → ℝ := fun x ↦ ψ ‖x‖
  have hχ : ContDiff ℝ ∞ χ := contDiff_comp_norm hψ hψ0
  -- The support of `χ` lies in the shell `0 < ‖x‖ < R`, in particular in the ball.
  have hχs : tsupport χ ⊆ ball (0 : E) R := fun x hx ↦ by
    simpa using (hψs (tsupport_comp_subset_preimage ψ continuous_norm hx)).2
  have hχc : HasCompactSupport χ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport χ) (isBounded_ball.subset hχs)
  have hχd : ∀ x, fderiv ℝ χ x = (deriv ψ ‖x‖ / ‖x‖) • innerSL ℝ x := fun x ↦
    (hasFDerivAt_comp_norm (hψ.differentiable (by simp)) hψ0 x).fderiv
  have hparts := integral_mul_trace_fderiv_eq_neg (μ := μ) isOpen_ball (hχ.of_le (by simp)) hχc
    hχs hV
  -- Polar coordinates for both sides.
  have hψ_out : ∀ s ∉ Ioi (0 : ℝ), ψ s = 0 ∧ deriv ψ s = 0 := fun s hs ↦
    ⟨image_eq_zero_of_notMem_tsupport fun h ↦ hs (hψs h).1,
      image_eq_zero_of_notMem_tsupport fun h ↦ hs (hψs (tsupport_deriv_subset h)).1⟩
  have hnorm : ∀ s ∈ Ioi (0 : ℝ), ∀ θ : sphere (0 : E) 1, ‖s • (θ : E)‖ = s := fun s hs θ ↦ by
    rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg (le_of_lt hs)]
  have h₁ : ∫ x, χ x * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      ∫ s, ψ s * (s ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1,
        LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere) := by
    refine (integral_eq_integral_Ioi_integral_toSphere _ (integrable_mul_trace_fderiv
      isOpen_ball hχ.continuous hχc hχs hV)).trans <| Eq.trans ?_
      (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun s hs ↦ by
        simp [(hψ_out s hs).1])
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
    simp only [χ, hnorm s hs, smul_eq_mul, integral_const_mul]
    ring
  -- `Dχ (V) = ψ' (‖x‖) ⟪x, V x⟫ / ‖x‖`.
  have hint₂ := integrable_fderiv_apply (μ := μ) isOpen_ball (hχ.of_le (by simp)) hχc hχs
    fun x hx ↦ (hV x hx).continuousAt.continuousWithinAt
  have h₂ : ∫ x, fderiv ℝ χ x (V x) ∂μ = ∫ s, deriv ψ s * (s ^ (finrank ℝ E - 1) *
      ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere) := by
    refine (integral_eq_integral_Ioi_integral_toSphere _ hint₂).trans <| Eq.trans ?_
      (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun s hs ↦ by
        simp [(hψ_out s hs).2])
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
    have hs' : (s : ℝ) ≠ 0 := (show (0 : ℝ) < s from hs).ne'
    have hθ : ∀ θ : sphere (0 : E) 1,
        fderiv ℝ χ (s • (θ : E)) (V (s • (θ : E))) = deriv ψ s * ⟪V (s • (θ : E)), θ⟫ :=
      fun θ ↦ by
        simp only [hχd, hnorm s hs, FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply,
          inner_smul_left, real_inner_comm (θ : E), smul_eq_mul, RCLike.conj_to_real]
        field_simp
    simp only [hθ, smul_eq_mul, integral_const_mul]
    ring
  rw [← h₁, ← h₂, hparts, neg_neg]

/-! ### The divergence theorem -/

/-- A function on the line whose topological support lies in a bounded open interval has compact
support. -/
private lemma hasCompactSupport_of_tsupport_subset_Ioo {ψ : ℝ → ℝ} {a b : ℝ}
    (hψs : tsupport ψ ⊆ Ioo a b) : HasCompactSupport ψ :=
  isCompact_of_isClosed_isBounded (isClosed_tsupport ψ) ((Metric.isBounded_Ioo a b).subset hψs)

/-- **Integration by parts against a test function.** If `G` has derivative `g` on `(0, R)`, with
`g` continuous there, then `∫ ψ' G = -∫ ψ g` for every smooth `ψ` with support in `(0, R)`. -/
private lemma integral_deriv_mul_eq_neg_integral_mul {ψ G g : ℝ → ℝ} {R : ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo 0 R)
    (hG : ∀ s ∈ Ioo 0 R, HasDerivAt G (g s) s) (hg : ContinuousOn g (Ioo 0 R)) :
    ∫ s, deriv ψ s * G s = -∫ s, ψ s * g s := by
  have hψc := hasCompactSupport_of_tsupport_subset_Ioo hψs
  have hGc : ContinuousOn G (Ioo 0 R) := fun s hs ↦ (hG s hs).continuousAt.continuousWithinAt
  have hi₁ : Integrable fun s ↦ deriv ψ s * G s :=
    (((hψ.continuous_deriv (by simp)).continuousOn.mul hGc).continuous_of_tsupport_subset
      isOpen_Ioo (tsupport_mul_subset_left.trans (tsupport_deriv_subset.trans hψs))
      ).integrable_of_hasCompactSupport hψc.deriv.mul_right
  have hi₂ : Integrable fun s ↦ ψ s * g s :=
    ((hψ.continuous.continuousOn.mul hg).continuous_of_tsupport_subset isOpen_Ioo
      (tsupport_mul_subset_left.trans hψs)).integrable_of_hasCompactSupport hψc.mul_right
  have hi : Integrable fun s ↦ ψ s * G s :=
    ((hψ.continuous.continuousOn.mul hGc).continuous_of_tsupport_subset isOpen_Ioo
      (tsupport_mul_subset_left.trans hψs)).integrable_of_hasCompactSupport hψc.mul_right
  -- `ψ G` has derivative `ψ' G + ψ g` everywhere, since it vanishes near every point off `(0, R)`.
  have hderiv : ∀ s, HasDerivAt (fun s ↦ ψ s * G s) (deriv ψ s * G s + ψ s * g s) s := by
    intro s
    by_cases hs : s ∈ Ioo 0 R
    · exact (hψ.differentiable (by simp) s).hasDerivAt.mul (hG s hs)
    · have h0 : ψ =ᶠ[𝓝 s] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hs (hψs h)
      rw [h0.deriv_eq, h0.self_of_nhds]
      simpa using (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
        (h0.mono fun y hy ↦ by simp [hy])
  have h := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (hi₁.add hi₂) hi
  rw [integral_add hi₁ hi₂] at h
  linarith

/-- The flux `s ↦ ∫ ⟪V (s θ), θ⟫` through spheres about the origin is continuous in the radius on
`[0, R]` when `V` is continuous on `closedBall 0 R`. -/
private lemma continuousOn_integral_toSphere_inner {V : E → E} {R : ℝ}
    (hV : ContinuousOn V (closedBall (0 : E) R)) :
    ContinuousOn (fun s : ℝ ↦ ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere)
      (Icc 0 R) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hV
  refine continuousOn_of_dominated (bound := fun _ ↦ C) (fun s hs ↦ ?_) (fun s hs ↦ ?_)
    (integrable_const C) (ae_of_all _ fun θ ↦ ?_)
  · exact ((hV.comp_continuous (continuous_const.smul continuous_subtype_val)
      (smul_mem_closedBall hs)).inner continuous_subtype_val).aestronglyMeasurable
  · refine ae_of_all _ fun θ ↦ ?_
    calc ‖⟪V (s • (θ : E)), θ⟫‖ ≤ ‖V (s • (θ : E))‖ * ‖(θ : E)‖ := norm_inner_le_norm _ _
      _ ≤ C := by
        rw [norm_eq_of_mem_sphere θ, mul_one]
        exact hC _ (smul_mem_closedBall hs θ)
  · exact (hV.comp (continuous_id.smul continuous_const).continuousOn
      fun s hs ↦ smul_mem_closedBall hs θ).inner continuousOn_const

/-- **A continuous function with distributional derivative `g` is a primitive of `g`.** If `Φ`
and `g` are continuous on `[0, R]` and `∫ ψ' Φ = -∫ ψ g` for every test function `ψ` on `(0, R)`,
then `Φ R = Φ 0 + ∫₀^R g`. -/
private lemma eq_add_intervalIntegral_of_integral_deriv_mul_eq_neg {Φ g : ℝ → ℝ} {R : ℝ}
    (hR : 0 < R) (hΦ : ContinuousOn Φ (Icc 0 R)) (hg : ContinuousOn g (Icc 0 R))
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → tsupport ψ ⊆ Ioo 0 R →
      ∫ s, deriv ψ s * Φ s = -∫ s, ψ s * g s) :
    Φ R = Φ 0 + ∫ s in (0 : ℝ)..R, g s := by
  set G : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..s, g t
  have hGc : ContinuousOn G (Icc 0 R) := by
    simpa [G, uIcc_of_le hR.le] using intervalIntegral.continuousOn_primitive_interval
      (μ := volume) (a := 0) (b := R) (by simpa [uIcc_of_le hR.le] using hg.integrableOn_Icc)
  have hGd : ∀ s ∈ Ioo 0 R, HasDerivAt G (g s) s := fun s hs ↦
    intervalIntegral.integral_hasDerivAt_right
      ((hg.mono (by simpa [uIcc_of_le hs.1.le] using Icc_subset_Icc_right hs.2.le)
        ).intervalIntegrable)
      ((hg.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
      ((hg.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds hs))
  -- `Φ - G` has zero distributional derivative on `(0, R)`, so it is constant on `[0, R]`.
  obtain ⟨c, hc⟩ := ((hΦ.sub hGc).mono Ioo_subset_Icc_self
    ).exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero fun ψ hψ hψs ↦ by
      have hint : ∀ f : ℝ → ℝ, ContinuousOn f (Ioo 0 R) →
          Integrable fun s ↦ deriv ψ s * f s := fun f hf ↦
        (((hψ.continuous_deriv (by simp)).continuousOn.mul hf).continuous_of_tsupport_subset
          isOpen_Ioo (tsupport_mul_subset_left.trans (tsupport_deriv_subset.trans hψs))
          ).integrable_of_hasCompactSupport
            ((hasCompactSupport_of_tsupport_subset_Ioo hψs).deriv.mul_right)
      simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
      rw [integral_sub (hint Φ (hΦ.mono Ioo_subset_Icc_self))
          (hint G (hGc.mono Ioo_subset_Icc_self)), h ψ hψ hψs,
        integral_deriv_mul_eq_neg_integral_mul hψ hψs hGd (hg.mono Ioo_subset_Icc_self), sub_self]
  have hIcc : EqOn (Φ - G) (fun _ ↦ c) (Icc 0 R) :=
    hc.of_subset_closure (hΦ.sub hGc) continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hR.ne])
  have h0 := hIcc ⟨le_rfl, hR.le⟩
  have hR' := hIcc ⟨hR.le, le_rfl⟩
  simp only [Pi.sub_apply, G, intervalIntegral.integral_same, sub_zero] at h0 hR'
  linarith

/-- The divergence theorem on balls about the origin. -/
private lemma setIntegral_ball_zero_trace_fderiv [Nontrivial E] {R : ℝ} (hR : 0 ≤ R) {V : E → E}
    (hV : ∀ x ∈ closedBall (0 : E) R, ContDiffAt ℝ 1 V x) :
    ∫ x in ball (0 : E) R, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      R ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (R • (θ : E)), θ⟫ ∂μ.toSphere := by
  -- The flux through the sphere of radius zero vanishes.
  have hΦ0 : (0 : ℝ) ^ (finrank ℝ E - 1) *
      ∫ θ : sphere (0 : E) 1, ⟪V ((0 : ℝ) • (θ : E)), θ⟫ ∂μ.toSphere = 0 := by
    simp only [zero_smul]
    rw [integral_inner (continuous_subtype_val.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), integral_toSphere_coe_eq_zero, inner_zero_right,
      mul_zero]
  rcases hR.eq_or_lt with rfl | hR
  · rw [Metric.ball_eq_empty.mpr le_rfl, Measure.restrict_empty, integral_zero_measure, hΦ0]
  have htr := continuousOn_trace_fderiv hV
  have h := eq_add_intervalIntegral_of_integral_deriv_mul_eq_neg (R := R)
    (Φ := fun s ↦ s ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere)
    (g := fun s ↦ s ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1,
      LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere) hR
    (((continuous_pow _).continuousOn).mul (continuousOn_integral_toSphere_inner (μ := μ)
      fun x hx ↦ (hV x hx).continuousAt.continuousWithinAt))
    (((continuous_pow (finrank ℝ E - 1)).continuousOn).mul (htr.integral_toSphere_smul (μ := μ)))
    fun ψ hψ hψs ↦ integral_deriv_mul_flux_eq_neg (fun x hx ↦ hV x (ball_subset_closedBall hx))
      hψ hψs
  beta_reduce at h
  rw [hΦ0, zero_add] at h
  rw [setIntegral_ball_zero_eq_integral_Ioo ((htr.integrableOn_compact (isCompact_closedBall _ _)
    ).mono_set ball_subset_closedBall), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le]
  exact h.symm

/-- **The divergence theorem on a ball.** Let `V : E → E` be `C¹` near the closed ball of radius
`R ≥ 0` about `c`. The integral of its divergence `tr (DV)` over the open ball is the flux of `V`
through the boundary sphere: with the unit sphere `S` and its surface measure `μ.toSphere`,

`∫_{ball c R} tr (DV) dμ = R ^ (n - 1) ∫_{θ ∈ S} ⟪V (c + R θ), θ⟫ dμ.toSphere`,

where `n` is the dimension of `E`. -/
theorem setIntegral_ball_trace_fderiv (c : E) {R : ℝ} (hR : 0 ≤ R) {V : E → E}
    (hV : ∀ x ∈ closedBall c R, ContDiffAt ℝ 1 V x) :
    ∫ x in ball c R, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      R ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (c + R • (θ : E)), θ⟫ ∂μ.toSphere := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space every endomorphism is zero and the unit sphere is empty.
    have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun θ ↦ by simpa [Subsingleton.elim (θ : E) 0] using norm_eq_of_mem_sphere θ⟩
    simp [Subsingleton.elim (fderiv ℝ V _ : E →ₗ[ℝ] E) 0, integral_of_isEmpty]
  have h := setIntegral_ball_zero_trace_fderiv (μ := μ) hR (V := fun y ↦ V (y + c))
    fun y hy ↦ (hV (y + c) (by simpa [mem_closedBall, dist_eq_norm] using hy)).comp y
      (contDiffAt_id.add contDiffAt_const)
  simp only [fderiv_comp_add_right] at h
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add, h]
  simp [add_comm]

end TauCeti
