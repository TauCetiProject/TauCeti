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
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Trace
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Group.Integral

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
`g s = s ^ (n - 1) ∫ tr (DV (s θ))` (`ContinuousOn.hasDerivAt_setIntegral_ball`). The proof shows
that `Φ` has the same distributional derivative `g` on `(0, R)`, without any tangential calculus on
the sphere. For a test function `ψ` on `(0, R)`, the radial function `χ x = ψ ‖x‖` is a test
function on the ball with gradient `ψ' (‖x‖) x / ‖x‖`. The classical derivative of `V` is a weak
one, so `∫ ⟪∇χ, V⟫ = -∫ χ tr (DV)`
(`TauCeti.HasWeakFDerivOn.integral_inner_gradient_eq_neg_integral_smul_trace`), which in polar
coordinates reads `∫ ψ' Φ = -∫ ψ g`: `g` is the weak derivative of `Φ`. So
`Φ R - Φ 0 = ∫₀^R g = G R` by the fundamental theorem of calculus for weak derivatives
(`TauCeti.HasWeakLineDerivOn.integral_eq_sub`, which rests on the du Bois-Reymond lemma), and
`Φ 0 = 0` because the surface measure has barycenter zero
(`MeasureTheory.Measure.integral_coe_toSphere`). This is the radial test-function argument of the
mean-value property for harmonic functions (`InnerProductSpace.HarmonicOnNhd.integral_toSphere_eq`),
applied to the flux instead of the sphere average.

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

/-! ### The distributional derivative of the flux -/

/-- **The flux has distributional derivative `g`.** For a field `V` that is `C¹` on `ball 0 R`
and a test function `ψ` on `(0, R)`,
`∫ ψ' (s) s ^ (n - 1) ∫ ⟪V (s θ), θ⟫ = -∫ ψ (s) s ^ (n - 1) ∫ tr (DV (s θ))`. This is the weak
divergence identity `∫ ⟪∇χ, V⟫ = -∫ χ tr (DV)` for the radial test function `χ x = ψ ‖x‖`, in
polar coordinates. -/
private lemma integral_deriv_mul_flux_eq_neg [Nontrivial E] {R : ℝ} {V : E → E}
    (hV : ∀ x ∈ ball (0 : E) R, ContDiffAt ℝ 1 V x) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψs : tsupport ψ ⊆ Ioo 0 R) :
    ∫ s, deriv ψ s • (s ^ (finrank ℝ E - 1) •
        ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere) =
      -∫ s, ψ s • (s ^ (finrank ℝ E - 1) • ∫ θ : sphere (0 : E) 1,
        LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere) := by
  have hψ0 : 0 ∉ tsupport ψ := fun h ↦ (lt_irrefl _ (hψs h).1)
  set χ : E → ℝ := fun x ↦ ψ ‖x‖
  have hχ : ContDiff ℝ ∞ χ := hψ.comp_norm hψ0
  -- The support of `χ` lies in the shell `0 < ‖x‖ < R`, in particular in the ball.
  have hχs : tsupport χ ⊆ ball (0 : E) R := fun x hx ↦ by
    simpa using (hψs (tsupport_comp_subset_preimage ψ continuous_norm hx)).2
  have hχc : HasCompactSupport χ :=
    isCompact_of_isClosed_isBounded (isClosed_tsupport χ) (isBounded_ball.subset hχs)
  have hχd : ∀ x, fderiv ℝ χ x = (deriv ψ ‖x‖ / ‖x‖) • innerSL ℝ x := fun x ↦
    ((hψ.differentiable (by simp) ‖x‖).hasFDerivAt_comp_norm hψ0).fderiv
  -- The weak divergence identity `∫ Dχ (V) = -∫ χ tr (DV)` for `V`, tested against `χ`.
  have hparts := (ContDiffOn.hasWeakFDerivOn_fderiv (μ := μ) (Ω := ⟨ball (0 : E) R, isOpen_ball⟩)
    fun x hx ↦ (hV x hx).contDiffWithinAt).integral_inner_gradient_eq_neg_integral_smul_trace
      ⟨χ, hχ, hχc, hχs⟩
  simp only [TestFunction.coe_mk, inner_gradient_left, smul_eq_mul] at hparts
  -- Polar coordinates for both sides.
  have hψ_out : ∀ s ∉ Ioi (0 : ℝ), ψ s = 0 ∧ deriv ψ s = 0 := fun s hs ↦
    ⟨image_eq_zero_of_notMem_tsupport fun h ↦ hs (hψs h).1,
      image_eq_zero_of_notMem_tsupport fun h ↦ hs (hψs (tsupport_deriv_subset h)).1⟩
  have hnorm : ∀ s ∈ Ioi (0 : ℝ), ∀ θ : sphere (0 : E) 1, ‖s • (θ : E)‖ = s := fun s hs θ ↦ by
    rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg (le_of_lt hs)]
  have h₁ : ∫ x, χ x * LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      ∫ s, ψ s • (s ^ (finrank ℝ E - 1) • ∫ θ : sphere (0 : E) 1,
        LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere) := by
    refine (integral_eq_integral_Ioi_integral_toSphere _ (integrable_mul_trace_fderiv
      isOpen_ball hχ.continuous hχc hχs hV)).trans <| Eq.trans ?_
      (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun s hs ↦ by
        simp [(hψ_out s hs).1])
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
    simp only [χ, hnorm s hs, smul_eq_mul, integral_const_mul]
    ring
  -- `Dχ (V) = ψ' (‖x‖) ⟪x, V x⟫ / ‖x‖`.
  have hVc : ContinuousOn V (tsupport χ) := fun x hx ↦
    (hV x (hχs hx)).continuousAt.continuousWithinAt
  have hint₂ : Integrable (fun x ↦ fderiv ℝ χ x (V x)) μ :=
    integrable_fderiv_apply_of_tsupport_subset (G := id) (hχ.of_le (by simp)) hχc subset_rfl
      aestronglyMeasurable_id ((integrable_indicator_iff (isClosed_tsupport χ).measurableSet).mpr
        (hVc.integrableOn_compact hχc))
  have h₂ : ∫ x, fderiv ℝ χ x (V x) ∂μ = ∫ s, deriv ψ s • (s ^ (finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere) := by
    refine (integral_eq_integral_Ioi_integral_toSphere _ hint₂).trans <| Eq.trans ?_
      (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0) fun s hs ↦ by
        simp [(hψ_out s hs).2])
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
    have hs' : (s : ℝ) ≠ 0 := (mem_Ioi.mp hs).ne'
    have hθ : ∀ θ : sphere (0 : E) 1,
        fderiv ℝ χ (s • (θ : E)) (V (s • (θ : E))) = deriv ψ s * ⟪V (s • (θ : E)), θ⟫ :=
      fun θ ↦ by
        simp only [hχd, hnorm s hs, FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply,
          inner_smul_left, real_inner_comm (θ : E), smul_eq_mul, RCLike.conj_to_real]
        field_simp
    simp only [hθ, smul_eq_mul, integral_const_mul]
    ring
  rw [← h₁, ← h₂, hparts]

/-! ### The divergence theorem -/

/-- The divergence theorem on balls about the origin. -/
private lemma setIntegral_ball_zero_trace_fderiv [Nontrivial E] {R : ℝ} (hR : 0 ≤ R) {V : E → E}
    (hV : ∀ x ∈ closedBall (0 : E) R, ContDiffAt ℝ 1 V x) :
    ∫ x in ball (0 : E) R, LinearMap.trace ℝ E (fderiv ℝ V x : E →ₗ[ℝ] E) ∂μ =
      R ^ (finrank ℝ E - 1) * ∫ θ : sphere (0 : E) 1, ⟪V (R • (θ : E)), θ⟫ ∂μ.toSphere := by
  -- The flux through the sphere of radius zero vanishes.
  have hΦ0 : (0 : ℝ) ^ (finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, ⟪V ((0 : ℝ) • (θ : E)), θ⟫ ∂μ.toSphere = 0 := by
    simp only [zero_smul]
    rw [integral_inner (continuous_subtypeVal.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), Measure.integral_coe_toSphere, inner_zero_right,
      smul_zero]
  rcases hR.eq_or_lt with rfl | hR
  · rw [Metric.ball_eq_empty.mpr le_rfl, Measure.restrict_empty, integral_zero_measure,
      ← smul_eq_mul, hΦ0]
  have htr := continuousOn_trace_fderiv hV
  -- The flux `s ↦ ∫ ⟪V (s θ), θ⟫` is continuous in the radius.
  have hflux : ContinuousOn (fun s : ℝ ↦ ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere)
      (Icc 0 R) :=
    have hVc : ContinuousOn V (closedBall (0 : E) R) := fun x hx ↦
      (hV x hx).continuousAt.continuousWithinAt
    ContinuousOn.integral_toSphere_smul_uncurry (g := fun x u ↦ ⟪V x, u⟫)
      ((hVc.comp continuousOn_fst fun _ hp ↦ (mem_prod.mp hp).1).inner continuousOn_snd)
  -- The flux `Φ` has weak derivative `g` on `(0, R)`, so `∫₀^R g = Φ R - Φ 0`.
  set Φ : ℝ → ℝ := fun s ↦
    s ^ (finrank ℝ E - 1) • ∫ θ : sphere (0 : E) 1, ⟪V (s • (θ : E)), θ⟫ ∂μ.toSphere with hΦ
  set g : ℝ → ℝ := fun s ↦ s ^ (finrank ℝ E - 1) • ∫ θ : sphere (0 : E) 1,
    LinearMap.trace ℝ E (fderiv ℝ V (s • (θ : E)) : E →ₗ[ℝ] E) ∂μ.toSphere
  have hΦc : ContinuousOn Φ (Icc 0 R) := ((continuous_pow _).continuousOn).smul hflux
  have hgc : ContinuousOn g (Icc 0 R) :=
    ((continuous_pow _).continuousOn).smul (htr.integral_toSphere_smul (μ := μ))
  have hd {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) :
      ∫ s, deriv ψ s • Φ s = -∫ s, ψ s • g s :=
    integral_deriv_mul_flux_eq_neg (fun x hx ↦ hV x (ball_subset_closedBall hx)) hψ hψs
  have hweak : HasWeakLineDerivOn volume ⟨Ioo 0 R, isOpen_Ioo⟩ Φ g 1 :=
    hasWeakLineDerivOn_iff_testFunction.mpr ⟨inferInstance,
      (hΦc.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo,
      (hgc.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo,
      fun φ ↦ by simpa only [lineDeriv_one] using hd φ.contDiff φ.tsupport_subset⟩
  have h := hweak.integral_eq_sub (hgc.integrableOn_Icc.mono_set Ioo_subset_Icc_self) hΦc
    EventuallyEq.rfl ⟨le_rfl, hR.le⟩ ⟨hR.le, le_rfl⟩
  rw [setIntegral_ball_zero_eq_integral_Ioo ((htr.integrableOn_compact (isCompact_closedBall _ _)
    ).mono_set ball_subset_closedBall), ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le, h]
  simp only [hΦ]
  rw [hΦ0, sub_zero, smul_eq_mul]

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
  have h := setIntegral_ball_zero_trace_fderiv (μ := μ) hR (V := fun y ↦ V (y + c))
    fun y hy ↦ (hV (y + c) (by simpa [mem_closedBall, dist_eq_norm] using hy)).comp y
      (contDiffAt_id.add contDiffAt_const)
  simp only [fderiv_comp_add_right] at h
  rw [setIntegral_ball_eq_setIntegral_ball_zero_add, h]
  simp [add_comm]

end TauCeti
