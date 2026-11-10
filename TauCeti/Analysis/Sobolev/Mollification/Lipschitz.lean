/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# Mollification of Lipschitz functions

Let `ψ` be `K`-Lipschitz on a finite-dimensional real normed space and let `ρ` be a smooth bump
centred at `0`. The derivative in a direction `v` of the mollification `ρ.normed μ ⋆ ψ` is the
mollification of the directional derivative `∂_v ψ`, which exists almost everywhere by
Rademacher's theorem and is the weak derivative of `ψ`. Hence these derivatives are bounded by
`K ‖v‖`. When the radii shrink to zero with a bounded ratio of outer to inner radius, they converge
to `∂_v ψ` almost everywhere, by the Lebesgue differentiation theorem. By dominated convergence,
integrals against the mollifications and against their directional derivatives then converge to
the integrals against `ψ` and `∂_v ψ`.

These are the estimates that pass an identity proved for smooth factors to Lipschitz ones by
dominated convergence, as in the Leibniz rule `TauCeti.HasWeakLineDerivOn.lipschitzWith_smul`.

## Main results

* `LipschitzWith.fderiv_normed_convolution_apply`: the directional derivative of the mollification
  is the mollification of the almost-everywhere directional derivative.
* `LipschitzWith.norm_fderiv_normed_convolution_apply_le`: these derivatives are bounded by
  `K ‖v‖`.
* `LipschitzWith.ae_tendsto_fderiv_normed_convolution_apply`: they converge almost everywhere to
  the directional derivative as the bumps shrink.
* `LipschitzWith.tendsto_integral_normed_convolution_smul` and
  `LipschitzWith.tendsto_integral_fderiv_normed_convolution_apply_smul`: integrals against the
  mollifications and against their directional derivatives converge as the bumps shrink.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.2.2 and §4.2.3.
-/

public section

open ContinuousLinearMap Filter Metric MeasureTheory
open scoped NNReal Convolution ContDiff Topology

namespace LipschitzWith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {K : ℝ≥0} {ψ : E → ℝ}

/-- The derivative in a direction `v` of the mollification of a Lipschitz function is the
mollification of its directional derivative `∂_v ψ`, which exists almost everywhere. -/
theorem fderiv_normed_convolution_apply (hψ : LipschitzWith K ψ) (ρ : ContDiffBump (0 : E))
    (x v : E) :
    fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v =
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y => lineDeriv ℝ ψ y v) x := by
  have hweak : TauCeti.HasWeakLineDerivOn μ ⊤ ψ (fun y => lineDeriv ℝ ψ y v) v :=
    hψ.locallyLipschitz.locallyLipschitzOn.hasWeakLineDerivOn
      ((hψ.ae_lineDifferentiableAt v).mono fun x hx _ => hx.hasLineDerivAt)
  have hl := hweak.lineDeriv_convolution_right hψ.continuous.locallyIntegrable (ρ.normed μ)
    ρ.contDiff_normed ρ.hasCompactSupport_normed x (by simp)
  have hsmooth : ContDiff ℝ ∞ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
      hψ.continuous.locallyIntegrable
  rw [convolution_flip, convolution_flip] at hl
  rw [← hl, (hsmooth.differentiable (by simp) x).lineDeriv_eq_fderiv]

/-- The derivatives in a direction `v` of the mollifications of a `K`-Lipschitz function are
bounded by `K ‖v‖`. -/
theorem norm_fderiv_normed_convolution_apply_le (hψ : LipschitzWith K ψ)
    (ρ : ContDiffBump (0 : E)) (x v : E) :
    ‖fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v‖ ≤ K * ‖v‖ := by
  rw [hψ.fderiv_normed_convolution_apply, ← dist_zero_right]
  exact dist_convolution_le (by positivity) ρ.support_normed_eq.subset ρ.nonneg_normed
    ρ.integral_normed (measurable_lineDeriv hψ.continuous).aestronglyMeasurable fun y _ => by
      rw [dist_zero_right]
      exact norm_lineDeriv_le_of_lipschitz ℝ hψ

/-- As normalized bumps shrink to `0` with a bounded ratio of outer to inner radius, the
derivatives in a direction `v` of the mollifications of a Lipschitz function converge almost
everywhere to its directional derivative `∂_v ψ`. -/
theorem ae_tendsto_fderiv_normed_convolution_apply (hψ : LipschitzWith K ψ) {ι : Type*}
    {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)} {C : ℝ}
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) (h'ρ : ∀ᶠ i in l, (ρ i).rOut ≤ C * (ρ i).rIn)
    (v : E) :
    ∀ᵐ x ∂μ, Tendsto (fun i => fderiv ℝ ((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v) l
      (𝓝 (lineDeriv ℝ ψ x v)) := by
  filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hρ h'ρ
    ((hψ.memLp_lineDeriv v).locallyIntegrable le_top)] with x hx
  simpa only [hψ.fderiv_normed_convolution_apply] using hx

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- As normalized bumps shrink to `0`, integrals against the mollifications of a Lipschitz
function `ψ` converge to the integral against `ψ`: `∫ (ρᵢ ⋆ ψ) w → ∫ ψ w` whenever `w` and `ψ w`
are integrable. -/
theorem tendsto_integral_normed_convolution_smul (hψ : LipschitzWith K ψ) {ι : Type*}
    {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)}
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) {w : E → G} (hw : Integrable w μ)
    (hψw : Integrable (fun x => ψ x • w x) μ) :
    Tendsto (fun i => ∫ x, ((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x • w x ∂μ) l
      (𝓝 (∫ x, ψ x • w x ∂μ)) := by
  have hunif := ContDiffBump.tendstoUniformly_normed_convolution (μ := μ) hρ hψ.uniformContinuous
  have hmeas : ∀ i, AEStronglyMeasurable
      (fun x => ((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x • w x) μ := fun i =>
    ((ρ i).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (ρ i).contDiff_normed
      hψ.continuous.locallyIntegrable (n := ⊤)).continuous.aestronglyMeasurable.smul hw.1
  rw [Metric.tendsto_nhds]
  intro ε hε
  set I : ℝ := ∫ x, ‖w x‖ ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  set δ : ℝ := min 1 (ε / (I + 1)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  filter_upwards [tendstoUniformly_iff.1 hunif δ hδ0] with i hi
  have hi' : ∀ x, ‖((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x - ψ x‖ ≤ δ := fun x => by
    have := hi x
    rw [dist_comm, dist_eq_norm] at this
    exact this.le
  -- The mollification is within `δ ≤ 1` of `ψ`, so `‖ψ w‖ + ‖w‖` dominates the integrand.
  have hint : Integrable (fun x => ((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x • w x) μ := by
    refine (hψw.norm.add hw.norm).mono' (hmeas i) (Eventually.of_forall fun x => ?_)
    have hx : ‖((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x‖ ≤ ‖ψ x‖ + 1 :=
      (norm_le_norm_add_norm_sub' _ (ψ x)).trans (add_le_add le_rfl
        ((hi' x).trans (min_le_left _ _)))
    simp only [Pi.add_apply, norm_smul]
    nlinarith [norm_nonneg (w x)]
  rw [dist_eq_norm, ← integral_sub hint hψw]
  calc ‖∫ x, (((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x • w x - ψ x • w x) ∂μ‖
      ≤ ∫ x, δ * ‖w x‖ ∂μ :=
        norm_integral_le_of_norm_le (hw.norm.const_mul δ) (Eventually.of_forall fun x => by
          rw [← sub_smul, norm_smul]
          exact mul_le_mul_of_nonneg_right (hi' x) (norm_nonneg _))
    _ = δ * I := integral_const_mul _ _
    _ < ε := by
        calc δ * I ≤ ε / (I + 1) * I :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hI0
          _ < ε := by
              rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
              nlinarith

/-- As normalized bumps shrink to `0` with a bounded ratio of outer to inner radius, integrals
against the directional derivatives of the mollifications of a Lipschitz function `ψ` converge to
the integral against its directional derivative: `∫ ∂_v (ρᵢ ⋆ ψ) w → ∫ (∂_v ψ) w` for integrable
`w`. -/
theorem tendsto_integral_fderiv_normed_convolution_apply_smul (hψ : LipschitzWith K ψ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {ρ : ι → ContDiffBump (0 : E)} {C : ℝ}
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) (h'ρ : ∀ᶠ i in l, (ρ i).rOut ≤ C * (ρ i).rIn)
    (v : E) {w : E → G} (hw : Integrable w μ) :
    Tendsto (fun i => ∫ x, fderiv ℝ ((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v • w x ∂μ) l
      (𝓝 (∫ x, lineDeriv ℝ ψ x v • w x ∂μ)) :=
  tendsto_integral_filter_of_dominated_convergence (fun x => (K * ‖v‖) * ‖w x‖)
    (Eventually.of_forall fun i =>
      ((((ρ i).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (ρ i).contDiff_normed
        hψ.continuous.locallyIntegrable (n := ⊤)).continuous_fderiv (by simp)).clm_apply
          continuous_const).aestronglyMeasurable.smul hw.1)
    (Eventually.of_forall fun i => Eventually.of_forall fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hψ.norm_fderiv_normed_convolution_apply_le (ρ i) x v)
        (norm_nonneg _))
    (hw.norm.const_mul _)
    ((hψ.ae_tendsto_fderiv_normed_convolution_apply hρ h'ρ v).mono fun x hx =>
      hx.smul_const (w x))

end LipschitzWith
