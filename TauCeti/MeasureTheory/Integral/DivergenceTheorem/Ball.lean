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
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.InnerProductSpace.NormPow
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Group.Integral

/-!
# The divergence theorem on a ball and on a spherical shell

Let `E` be a finite-dimensional real inner product space of dimension `n` with an additive Haar
measure `μ`, and let `V : E → E` be a vector field which is `C¹` near the closed shell
`r ≤ ‖x - c‖ ≤ R`, `0 ≤ r ≤ R`. This file proves the **divergence theorem on the shell**:

`∫_{ball c R \ closedBall c r} tr (DV) dμ = Φ R - Φ r`,

with the flux `Φ s = s ^ (n - 1) ∫_{θ ∈ S} ⟪V (c + s θ), θ⟫ dμ.toSphere`, where `S` is the unit
sphere with Mathlib's polar-coordinate surface measure `μ.toSphere`, so that
`s ^ (n - 1) dμ.toSphere` is the surface measure of the sphere of radius `s`, and `θ` is the outward
unit normal at `c + s θ` (`TauCeti.setIntegral_ball_sdiff_closedBall_trace_fderiv`). For `r = 0`
the shell is the ball up to its null centre and `Φ 0 = 0`, which is the **divergence theorem on the
ball** (`TauCeti.setIntegral_ball_trace_fderiv`).

Take `c = 0` and write `g s = s ^ (n - 1) ∫ tr (DV (s θ))`, so that in polar coordinates the
integral of `tr (DV)` over the shell is `∫_r^R g`
(`TauCeti.setIntegral_ball_sdiff_closedBall_zero_eq_integral_Ioo`). The proof shows that `Φ` has
the distributional derivative `g` on `(r, R)`, without any tangential calculus on the sphere. For
a test function `ψ` on `(r, R)`, the radial function `χ x = ψ ‖x‖` is a test function on the open
shell with gradient `ψ' (‖x‖) x / ‖x‖`. The classical derivative of `V` is a weak one, so
`∫ ⟪∇χ, V⟫ = -∫ χ tr (DV)`
(`TauCeti.HasWeakFDerivOn.integral_inner_gradient_eq_neg_integral_smul_trace`), which in polar
coordinates reads `∫ ψ' Φ = -∫ ψ g`: `g` is the weak derivative of `Φ`. So
`Φ R - Φ r = ∫_r^R g` by the fundamental theorem of calculus for weak derivatives
(`TauCeti.HasWeakLineDerivOn.integral_eq_sub`, which rests on the du Bois-Reymond lemma). For the
ball, `Φ 0 = 0` because the surface measure has barycenter zero
(`MeasureTheory.Measure.integral_coe_toSphere`). This is the radial test-function argument of the
mean-value property for harmonic functions (`InnerProductSpace.HarmonicOnNhd.integral_toSphere_eq`),
applied to the flux instead of the sphere average.

## Main results

* `TauCeti.setIntegral_ball_sdiff_closedBall_trace_fderiv`: the divergence theorem on a spherical
  shell.
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

/-! ### The distributional derivative of the flux -/

/-- **The weak divergence identity against a radial test function.** For `0 ≤ r`, a field `V`
that is `C¹` on the open shell `ball 0 R \ closedBall 0 r`, and a test function `ψ` on `(r, R)`,
the radial test function `χ x = ψ ‖x‖` satisfies `∫ Dχ (V) = -∫ χ tr (DV)`, and both integrands
are integrable. -/
private lemma integrable_and_integral_fderiv_comp_norm_apply_eq_neg {r R : ℝ} (hr : 0 ≤ r)
    {V : E → E} (hV : ∀ x ∈ ball (0 : E) R \ closedBall 0 r, ContDiffAt ℝ 1 V x) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo r R) :
    Integrable (fun x ↦ fderiv ℝ (fun y ↦ ψ ‖y‖) x (V x)) μ ∧
      Integrable (fun x ↦ ψ ‖x‖ * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E)) μ ∧
      ∫ x, fderiv ℝ (fun y ↦ ψ ‖y‖) x (V x) ∂μ =
        -∫ x, ψ ‖x‖ * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ := by
  have hψ0 : 0 ∉ tsupport ψ := fun h ↦ hr.not_gt (hψs h).1
  set χ : E → ℝ := fun x ↦ ψ ‖x‖
  have hχ : ContDiff ℝ ∞ χ := hψ.comp_norm hψ0
  -- The support of `χ` lies in the open shell `r < ‖x‖ < R`.
  have hχs : tsupport χ ⊆ ball (0 : E) R \ closedBall 0 r := fun x hx ↦ by
    simpa [and_comm] using hψs (tsupport_comp_subset_preimage ψ continuous_norm hx)
  have hχc : HasCompactSupport χ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport χ)
      (isBounded_ball.subset (hχs.trans sdiff_subset))
  have hΩ : IsOpen (ball (0 : E) R \ closedBall 0 r) := isOpen_ball.sdiff isClosed_closedBall
  -- The weak divergence identity `∫ Dχ (V) = -∫ χ tr (DV)` for `V`, tested against `χ`.
  have hparts := (ContDiffOn.hasWeakFDerivOn_fderiv (μ := μ) (Ω := ⟨_, hΩ⟩)
    fun x hx ↦ (hV x hx).contDiffWithinAt).integral_inner_gradient_eq_neg_integral_smul_trace
      ⟨χ, hχ, hχc, hχs⟩
  simp only [TestFunction.coe_mk, inner_gradient_left, smul_eq_mul] at hparts
  have hVc : ContinuousOn V (tsupport χ) := fun x hx ↦
    (hV x (hχs hx)).continuousAt.continuousWithinAt
  exact ⟨integrable_fderiv_apply_of_tsupport_subset (G := id) (hχ.of_le (by simp)) hχc subset_rfl
      aestronglyMeasurable_id ((integrable_indicator_iff (isClosed_tsupport χ).measurableSet).mpr
        (hVc.integrableOn_compact hχc)),
    integrable_mul_trace_fderiv hΩ hχ.continuous hχc hχs hV, hparts⟩

/-- **The flux has distributional derivative `g`.** For `0 ≤ r`, a field `V` that is `C¹` on the
open shell `ball 0 R \ closedBall 0 r`, and a test function `ψ` on `(r, R)`,
`∫ ψ' (s) s ^ (n - 1) ∫ ⟪V (s θ), θ⟫ = -∫ ψ (s) s ^ (n - 1) ∫ tr (DV (s θ))`. This is the weak
divergence identity `∫ ⟪∇χ, V⟫ = -∫ χ tr (DV)` for the radial test function `χ x = ψ ‖x‖`, in
polar coordinates. -/
private lemma integral_deriv_mul_flux_eq_neg [Nontrivial E] {r R : ℝ} (hr : 0 ≤ r) {V : E → E}
    (hV : ∀ x ∈ ball (0 : E) R \ closedBall 0 r, ContDiffAt ℝ 1 V x) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo r R) :
    ∫ s, deriv ψ s • (s ^ (finrank ℝ E - 1) •
        ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere) =
      -∫ s, ψ s • (s ^ (finrank ℝ E - 1) • ∫ θ : sphere (0 : E) 1,
        LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere) := by
  obtain ⟨hint₂, hint₁, hparts⟩ :=
    integrable_and_integral_fderiv_comp_norm_apply_eq_neg (μ := μ) hr hV hψ hψs
  have hψ0 : 0 ∉ tsupport ψ := fun h ↦ hr.not_gt (hψs h).1
  have hχd : ∀ x, fderiv ℝ (fun y : E ↦ ψ ‖y‖) x = (deriv ψ ‖x‖ / ‖x‖) • innerSL ℝ x := fun x ↦
    ((hψ.differentiable (by simp) ‖x‖).hasFDerivAt_comp_norm hψ0).fderiv
  -- Polar coordinates for both sides.
  have hψ_out : ∀ s ∉ Ioi (0 : ℝ), ψ s = 0 ∧ deriv ψ s = 0 := fun s hs ↦
    ⟨image_eq_zero_of_notMem_tsupport fun h ↦ hs (hr.trans_lt (hψs h).1),
      image_eq_zero_of_notMem_tsupport fun h ↦ hs (hr.trans_lt (hψs (tsupport_deriv_subset h)).1)⟩
  have hnorm : ∀ s ∈ Ioi (0 : ℝ), ∀ θ : sphere (0 : E) 1, ‖s • (θ : E)‖ = s := fun s hs θ ↦ by
    rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg (le_of_lt hs)]
  have h₁ : ∫ x, ψ ‖x‖ * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      ∫ s, ψ s • (s ^ (finrank ℝ E - 1) • ∫ θ : sphere (0 : E) 1,
        LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere) := by
    refine (integral_eq_integral_Ioi_integral_toSphere _ hint₁).trans <| Eq.trans ?_
      (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun s hs ↦ by
        simp [(hψ_out s hs).1])
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
    simp only [hnorm s hs, smul_eq_mul, integral_const_mul]
    ring
  -- `Dχ (V) = ψ' (‖x‖) ⟪x, V x⟫ / ‖x‖`.
  have h₂ : ∫ x, fderiv ℝ (fun y ↦ ψ ‖y‖) x (V x) ∂μ = ∫ s, deriv ψ s • (s ^ (finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere) := by
    refine (integral_eq_integral_Ioi_integral_toSphere _ hint₂).trans <| Eq.trans ?_
      (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun s hs ↦ by
        simp [(hψ_out s hs).2])
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
    have hs' : (s : ℝ) ≠ 0 := (mem_Ioi.mp hs).ne'
    have hθ : ∀ θ : sphere (0 : E) 1, fderiv ℝ (fun y ↦ ψ ‖y‖) (s • (θ : E)) (V (s • (θ : E))) =
        deriv ψ s * ⟪V (s • (θ : E)), θ⟫ := fun θ ↦ by
      simp only [hχd, hnorm s hs, FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply,
        inner_smul_left, real_inner_comm (θ : E), smul_eq_mul, RCLike.conj_to_real]
      field_simp
    simp only [hθ, smul_eq_mul, integral_const_mul]
    ring
  rw [← h₁, ← h₂, hparts]

/-! ### The divergence theorem -/

/-- The divergence theorem on shells about the origin. -/
private lemma setIntegral_ball_sdiff_closedBall_zero_trace_fderiv [Nontrivial E] {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) {V : E → E}
    (hV : ∀ x ∈ closedBall (0 : E) R \ ball 0 r, ContDiffAt ℝ 1 V x) :
    ∫ x in ball (0 : E) R \ closedBall 0 r, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      R ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (R • (θ : E)), θ⟫ ∂μ.toSphere -
        r ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (r • (θ : E)), θ⟫ ∂μ.toSphere := by
  have htr := continuousOn_trace_fderiv hV
  -- The flux `s ↦ ∫ ⟪V (s θ), θ⟫` and the sphere integrals of `tr (DV)` are continuous in the
  -- radius.
  have hVc : ContinuousOn V (closedBall (0 : E) R \ ball 0 r) := fun x hx ↦
    (hV x hx).continuousAt.continuousWithinAt
  have hflux : ContinuousOn (fun s : ℝ ↦ ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere)
      (Icc r R) :=
    ContinuousOn.integral_toSphere_smul_uncurry hr (g := fun x u ↦ ⟪V x, u⟫)
      ((hVc.comp continuousOn_fst fun _ hp ↦ (mem_prod.mp hp).1).inner continuousOn_snd)
  -- The flux `Φ` has weak derivative `g` on `(r, R)`, so `∫_r^R g = Φ R - Φ r`.
  set Φ : ℝ → ℝ := fun s ↦
    s ^ (finrank ℝ E - 1) • ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere with hΦ
  set g : ℝ → ℝ := fun s ↦ s ^ (finrank ℝ E - 1) • ∫ θ : sphere (0 : E) 1,
    LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere
  have hΦc : ContinuousOn Φ (Icc r R) := ((continuous_pow _).continuousOn).smul hflux
  have hgc : ContinuousOn g (Icc r R) :=
    ((continuous_pow _).continuousOn).smul (ContinuousOn.integral_toSphere_smul_uncurry (μ := μ)
      hr (g := fun x _ ↦ LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E))
      (htr.comp continuousOn_fst fun _ hp ↦ (mem_prod.mp hp).1))
  have hd {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo r R) :
      ∫ s, deriv ψ s • Φ s = -∫ s, ψ s • g s :=
    integral_deriv_mul_flux_eq_neg hr
      (fun x hx ↦ hV x (sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall hx)) hψ hψs
  have hweak : HasWeakLineDerivOn volume ⟨Ioo r R, isOpen_Ioo⟩ Φ g 1 :=
    hasWeakLineDerivOn_iff_testFunction.mpr ⟨inferInstance,
      (hΦc.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo,
      (hgc.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo,
      fun φ ↦ by simpa only [lineDeriv_one] using hd φ.contDiff φ.tsupport_subset⟩
  have h := hweak.integral_eq_sub (hgc.integrableOn_Icc.mono_set Ioo_subset_Icc_self) hΦc
    EventuallyEq.rfl ⟨le_rfl, hrR⟩ ⟨hrR, le_rfl⟩
  rw [setIntegral_ball_sdiff_closedBall_zero_eq_integral_Ioo hr ((htr.integrableOn_compact
    ((isCompact_closedBall _ _).diff isOpen_ball)).mono_set
      (sdiff_subset_sdiff ball_subset_closedBall ball_subset_closedBall)),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR, h]
  simp only [hΦ, smul_eq_mul]

/-- **The divergence theorem on a spherical shell.** Let `V : E → E` be `C¹` near the closed shell
`r ≤ ‖x - c‖ ≤ R`, where `0 ≤ r ≤ R`. The integral of its divergence `tr (DV)` over the open shell
`ball c R \ closedBall c r` is the flux of `V` through the outer sphere minus its flux through the
inner sphere: with the unit sphere `S` and its surface measure `μ.toSphere`,

`∫_{ball c R \ closedBall c r} tr (DV) dμ = Φ R - Φ r`, where
`Φ s = s ^ (n - 1) ∫_{θ ∈ S} ⟪V (c + s θ), θ⟫ dμ.toSphere`

where `n` is the dimension of `E`. -/
theorem setIntegral_ball_sdiff_closedBall_trace_fderiv (c : E) {r R : ℝ} (hr : 0 ≤ r)
    (hrR : r ≤ R) {V : E → E} (hV : ∀ x ∈ closedBall c R \ ball c r, ContDiffAt ℝ 1 V x) :
    ∫ x in ball c R \ closedBall c r, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      R ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (c + R • (θ : E)), θ⟫ ∂μ.toSphere -
        r ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (c + r • (θ : E)), θ⟫ ∂μ.toSphere := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In the trivial space every endomorphism is zero and the unit sphere is empty.
    simp [Subsingleton.elim (fderiv ℝ V _ : E →ₗ[ℝ] E) 0, integral_of_isEmpty]
  have hpre : (· + c) ⁻¹' (ball c R \ closedBall c r) = ball (0 : E) R \ closedBall 0 r := by
    ext y
    simp [dist_eq_norm]
  have h := setIntegral_ball_sdiff_closedBall_zero_trace_fderiv (μ := μ) hr hrR
    (V := fun y ↦ V (y + c)) fun y hy ↦ (hV (y + c) (by simpa [dist_eq_norm] using hy)).comp y
      (contDiffAt_id.add contDiffAt_const)
  simp only [fderiv_comp_add_right] at h
  rw [← (measurePreserving_add_right μ c).setIntegral_preimage_emb
    (measurableEmbedding_addRight c), hpre, h]
  simp [add_comm]

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
    simp [Subsingleton.elim (fderiv ℝ V _ : E →ₗ[ℝ] E) 0, integral_of_isEmpty]
  -- The ball is the shell of inner radius `0`, up to the null centre.
  have h := setIntegral_ball_sdiff_closedBall_trace_fderiv (μ := μ) c le_rfl hR
    fun x hx ↦ hV x hx.1
  rw [closedBall_zero, setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton c))] at h
  -- The flux through the sphere of radius zero vanishes: the surface measure has barycentre zero.
  rw [h]
  simp only [zero_smul, add_zero]
  rw [integral_inner (continuous_subtypeVal.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)), Measure.integral_coe_toSphere, inner_zero_right,
    mul_zero, sub_zero]

end TauCeti
